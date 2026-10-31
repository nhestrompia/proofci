#!/usr/bin/env python3
"""Validate the proposed ticket graph and render review artifacts. Never publishes."""
from pathlib import Path
import html
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
plan = json.loads((ROOT / "plan.json").read_text())
tickets = plan["tickets"]
by_id = {ticket["id"]: ticket for ticket in tickets}
assert len(by_id) == len(tickets), "Duplicate ticket ID"
assert list(by_id) == list(range(1, len(tickets) + 1)), "IDs must be sequential"
assert plan["state"] == "proposed-awaiting-approval", "Do not publish through this script"
publication_path = ROOT / "publication.json"
publication = json.loads(publication_path.read_text()) if publication_path.exists() else {}
published = publication.get("state") == "published-verified"
if published:
    assert publication["approvedPlanSha256"] == hashlib.sha256((ROOT / "plan.json").read_bytes()).hexdigest()

ancestors = {}
for ticket in tickets:
    number = ticket["id"]
    assert re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", ticket["slug"])
    blockers = ticket["blockedBy"]
    assert len(blockers) == len(set(blockers)), f"Duplicate blocker in {number}"
    assert all(blocker in by_id and blocker < number for blocker in blockers), f"Invalid/topologically late blocker in {number}"
    assert 4 <= len(ticket["acceptance"]) <= 7, f"Acceptance size in {number}"
    assert ticket["delivers"] and ticket["ownership"]
    ancestors[number] = set(blockers)
    for blocker in blockers:
        ancestors[number].update(ancestors[blocker])
    for blocker in blockers:
        assert not any(blocker in ancestors[other] for other in blockers if other != blocker), f"Redundant blocker {blocker} in {number}"

stories = {story for ticket in tickets for story in ticket["stories"]}
assert stories == set(range(1, 45)), f"Story coverage mismatch: {stories ^ set(range(1, 45))}"
spec = (ROOT.parent.parent / plan["source"]).read_text()
assert len(re.findall(r"^\d+\. As an? ", spec, re.M)) == 44, "Source spec changed; review coverage"

done = set()
waves = []
while len(done) < len(tickets):
    frontier = [t["id"] for t in tickets if t["id"] not in done and set(t["blockedBy"]) <= done]
    assert frontier, "Dependency cycle"
    waves.append(frontier)
    done.update(frontier)
after_cli = ancestors[5] | {5} | set(waves[0])
post_cli_ready = [t["id"] for t in tickets if t["id"] not in after_cli and set(t["blockedBy"]) <= after_cli]

# Dilworth's theorem: maximum antichain = vertices minus maximum matching
# in the transitive-closure bipartite graph. This is dependency capacity,
# not a promise that that many runtime agent slots are available.
successors = {i: [j for j in by_id if i in ancestors[j]] for i in by_id}
matched = {}
def augment(left, seen):
    for right in successors[left]:
        if right in seen:
            continue
        seen.add(right)
        if right not in matched or augment(matched[right], seen):
            matched[right] = left
            return True
    return False
matching_size = sum(augment(i, set()) for i in by_id)
width = len(tickets) - matching_size
reachable_left = set(by_id) - set(matched.values())
reachable_right = set()
pending = list(reachable_left)
while pending:
    left = pending.pop()
    for right in successors[left]:
        if matched.get(right) == left or right in reachable_right:
            continue
        reachable_right.add(right)
        if right in matched and matched[right] not in reachable_left:
            reachable_left.add(matched[right])
            pending.append(matched[right])
maximum_frontier = sorted(reachable_left - reachable_right)
assert len(maximum_frontier) == width, "Maximum frontier derivation failed"
frontier_prerequisites = set().union(*(ancestors[i] for i in maximum_frontier))
assert not frontier_prerequisites.intersection(maximum_frontier)
assert all(set(by_id[i]["blockedBy"]) <= frontier_prerequisites for i in maximum_frontier)

drafts = ROOT / "drafts"
drafts.mkdir(exist_ok=True)
expected_files = set()
for ticket in tickets:
    number = ticket["id"]
    name = f"{number:02d}-{ticket['slug']}.md"
    expected_files.add(name)
    blocked = "; ".join(f"{i:02d}: {by_id[i]['title']}" for i in ticket["blockedBy"]) or "None (can start immediately)"
    criteria = "\n".join(f"- [ ] {criterion}" for criterion in ticket["acceptance"])
    text = f"# {number:02d}: {ticket['title']}\n\n**What to build:** {ticket['delivers']}\n\n**Blocked by:** {blocked}.\n\n**Status:** proposed-awaiting-approval\n\n{criteria}\n\n**Agent ownership:** {ticket['ownership']}\n\n**Spec coverage:** user stories {', '.join(map(str, ticket['stories']))}.\n"
    if published:
        text = text.replace("**Status:** proposed-awaiting-approval", f"**Status:** ready-for-agent\n\n**Published issue:** {publication['issues'][str(number)]['url']}")
    (drafts / name).write_text(text)
assert {p.name for p in drafts.glob("*.md")} == expected_files, "Unexpected/stale draft files"

coverage = {str(i): [t["id"] for t in tickets if i in t["stories"]] for i in range(1, 45)}
summary = {"tickets": len(tickets), "edges": sum(len(t["blockedBy"]) for t in tickets), "waves": waves, "maxDependencyParallelism": width, "maximumFrontier": maximum_frontier, "maximumFrontierPrerequisites": sorted(frontier_prerequisites), "storyCoverage": coverage, "state": plan["state"]}
if published:
    summary["state"] = publication["state"]
(ROOT / "validation.json").write_text(json.dumps(summary, indent=2) + "\n")

lines = ["# Proposed ProofCI ticket breakdown", "", "Status: awaiting breakdown approval. No GitHub issues or labels were created.", "", f"Publication target: {plan['tracker']}. Intended label: `{plan['publicationLabel']}`.", "", f"{len(tickets)} independently verifiable tickets. Immediate frontier: {', '.join(f'{i:02d}' for i in waves[0])}. The dependency graph permits up to {width} independent tickets; the current session has three child-agent slots.", "", f"The core binding, validation, and CLI sequence is a real prerequisite. The VM probe and GitHub enrollment can run alongside it. After ticket 05 and the initial spikes, {len(post_cli_ready)} lanes can start: {', '.join(f'{i:02d}' for i in post_cli_ready)}. Do not turn release prerequisites into fake implementation dependencies, or treat protocol fixtures as real enforcement evidence.", "", "## Proposed tickets", ""]
for t in tickets:
    blockers = ", ".join(f"{i:02d}" for i in t["blockedBy"]) or "None"
    lines.append(f"{t['id']}. **{t['title']}**. Blocked by: {blockers}. Delivers: {t['delivers']} [Full draft](drafts/{t['id']:02d}-{t['slug']}.md).")
lines += ["", "## Agent execution rules", "", "- Work only the current frontier. Refill available agent slots as blockers finish rather than imposing global wave barriers.", "- Give each implementation agent an isolated worktree after its prerequisite commits land. Uncommitted parent edits are not inherited by a worktree.", "- One ticket has one implementation owner. Tests and behavior belong with that ticket, not a separate horizontal team.", "- Ticket 05 owns public run/report interfaces. Other agents extend through their declared adapters and coordinate any shared-contract change.", "- Shared run, contract, evidence, broker, worker, and platform responsibilities are assigned in each draft. Keep one migration author at a time while unrelated modules can proceed.", "- The three property outcomes remain distinct. No agent can weaken acceptance to finish a ticket or improve a benchmark.", "- Linux virtualization, a test App and pilot repositories, GitLab access, model configuration, and a license decision are external prerequisites. Missing access does not count as passing acceptance. Licensing must be approved before the first public distribution, not deferred until deployment.", "- A no-go trust spike is not an accepted completed prerequisite. Replan the supported subset before allowing downstream verification claims.", "- Hosted paid AI remains disabled until durable provider-attempt recovery passes. Provider response loss is an uncertain cost, not permission to retry blindly.", "- Do not launch implementation agents from this planning proposal. First approve granularity, blocking edges, and publication target, then publish approved tickets with ready-for-agent.", "", "## Dependency waves", "", "Waves illustrate earliest starts assuming equal durations. Actual agents can take any unblocked ticket without waiting for a whole wave.", ""]
lines += [f"{i + 1}. {', '.join(f'{j:02d}' for j in wave)}" for i, wave in enumerate(waves)]
lines += ["", f"A maximum-width frontier is {', '.join(f'{i:02d}' for i in maximum_frontier)} after completing its predecessors {', '.join(f'{i:02d}' for i in sorted(frontier_prerequisites))}. This is a graph-capacity witness, not a recommended reason to delay useful work or a promise of runtime slots."]
lines += ["", "## Publication", "", "The GitHub remote and Issues are available. The ready-for-agent label is currently absent. After approval, create the label if necessary and publish one issue per ticket in dependency order. Use native blocking relations where available, otherwise link blocker issue identifiers in each body. Record returned issue URLs and avoid duplicate publication on retry. Do not modify or close a parent issue.", "", "If local publication is selected instead, place the approved per-ticket files in the skill's issues directory and change their status to ready-for-agent. These draft files are not published tickets.", "", "## Review required by to-tickets", "", "Does the granularity feel right? Are the blocking edges genuine? Should any tickets be merged or split? Approve the breakdown and GitHub target, or specify revisions.", ""]
readme = "\n".join(lines)
if published:
    readme = readme.replace("# Proposed ProofCI ticket breakdown", "# Published ProofCI ticket breakdown")
    readme = readme.replace("Status: awaiting breakdown approval. No GitHub issues or labels were created.", "Status: approved, published, and verified on GitHub. See the [published issue index](published.md).")
    readme = readme.replace("Intended label:", "Applied label:").replace("## Proposed tickets", "## Approved tickets")
    readme = readme.replace("- Do not launch implementation agents from this planning proposal. First approve granularity, blocking edges, and publication target, then publish approved tickets with ready-for-agent.", "- Publication is complete. Implementation agents should work the current frontier in isolated checkouts. Publishing alone does not start implementation.")
    readme = readme.split("## Publication\n", 1)[0] + "## Publication\n\nAll approved issues and native blocking relationships were read back and verified. The [published index](published.md) records their URLs. The immutable approved input remains in the plan manifest, and the publication ledger records approval, its digest, issue IDs, and verification.\n"
(ROOT / "README.md").write_text(readme)

escape = html.escape
rows = []
for t in tickets:
    blockers = ", ".join(f"{i:02d}" for i in t["blockedBy"]) or "None · ready to start"
    criteria = "".join(f"<li>{escape(x)}</li>" for x in t["acceptance"])
    heading = escape(t["title"])
    if published:
        heading = f'<a href="{escape(publication["issues"][str(t["id"])]["url"])}">{heading}</a>'
    rows.append(f'<li value="{t["id"]}" data-lane="{escape(t["lane"])}" data-root="{str(not t["blockedBy"]).lower()}"><h3>{heading}</h3><p class="meta">{escape(t["lane"])} · Blocked by: {blockers}</p><p>{escape(t["delivers"])}</p><details><summary>Acceptance and ownership</summary><ul>{criteria}</ul><p><strong>Owner boundary.</strong> {escape(t["ownership"])}</p></details></li>')
wave_html = "".join(f'<div class="wave"><b>{i + 1:02d}</b><span>{", ".join(f"{j:02d}" for j in wave)}</span></div>' for i, wave in enumerate(waves))
options = '<option value="all">All lanes</option>' + ''.join(f'<option>{escape(lane)}</option>' for lane in dict.fromkeys(t['lane'] for t in tickets))
page = '''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>Proposed ProofCI tickets</title><style>
*{box-sizing:border-box}body{margin:0;font:14px/1.5 var(--font-sans,system-ui,sans-serif);color:var(--foreground,#222)}p{margin:0 0 10px}h2{font-size:18px;margin:22px 0 10px}h3{font-size:15px;margin:0 0 4px}.stats{display:grid;grid-template-columns:repeat(3,1fr);gap:10px;margin-bottom:16px}.stat{padding:16px;border:1px solid var(--border,#ddd);border-radius:var(--radius,9px)}.stat b{display:block;font-size:25px;line-height:1.2}.stat span,.meta,.note{color:var(--muted-foreground,#666);font-size:12px}.callout{border-left:3px solid var(--primary,#5269c7);padding-left:12px;margin:16px 0}.waves{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}.wave{padding:12px;border:1px solid var(--border,#ddd);border-radius:var(--radius,9px)}.wave b{display:block;font-family:var(--font-mono,monospace);font-size:12px;color:var(--muted-foreground,#666)}.wave span{font-size:12px}.controls{display:flex;gap:8px;flex-wrap:wrap;margin:14px 0}select,button{padding:9px 12px;color:inherit;font:inherit;background:var(--card,#f6f6f6);border:1px solid var(--border,#ddd);border-radius:7px}button{cursor:pointer}button[aria-pressed=true]{background:var(--primary,#5269c7);color:var(--primary-foreground,#fff)}button:focus-visible,select:focus-visible,summary:focus-visible{outline:2px solid var(--ring,#5269c7);outline-offset:3px}ol{padding-left:30px;margin:0}ol>li{padding:16px;margin:0 0 10px;border:1px solid var(--border,#ddd);border-radius:var(--radius,9px)}ol>li::marker{font-family:var(--font-mono,monospace);font-weight:700}ol>li p{margin:5px 0}summary{cursor:pointer;color:var(--primary,#5269c7);font-size:13px;margin-top:10px}details ul{padding-left:19px}details ul li{margin:8px 0}.hidden{display:none}.footer{margin:18px 0 0;padding:16px;background:var(--card,#f6f6f6);border:1px solid var(--border,#ddd);border-radius:var(--radius,9px)}@media(max-width:480px){.stats{gap:6px}.stat{padding:12px}.stat b{font-size:22px}.waves{grid-template-columns:repeat(2,1fr)}ol>li{padding:13px}}
</style></head><body>
<div class="stats"><div class="stat"><b>TICKET_COUNT</b><span>proposed tickets</span></div><div class="stat"><b>ROOT_COUNT</b><span>can start immediately</span></div><div class="stat"><b>WIDTH</b><span>maximum independent tickets</span></div></div>
<p>Three agents reviewed the spec. The breakdown preserves real verification prerequisites and opens POST_CLI_COUNT work lanes after the CLI and initial spikes.</p><p class="note">Current session capacity: three child agents. Dependency capacity is not the same as available runtime slots.</p>
<p class="callout">Proposal awaiting approval. No GitHub issues or labels were created. Proposed tracker: nhestrompia/proofci, with ready-for-agent.</p>
<h2>Earliest-start groups</h2><p class="note">Ticket numbers below. Groups illustrate dependencies; agents can take any unblocked ticket without waiting for a group to finish.</p><div class="waves">WAVES</div>
<h2>Numbered ticket breakdown</h2><div class="controls"><select id="lane" aria-label="Filter work lane">OPTIONS</select><button id="roots" type="button" aria-pressed="false">Show immediate frontier</button></div><p id="count" class="note" aria-live="polite">TICKET_COUNT tickets shown</p><ol id="tickets">ROWS</ol>
<div class="footer"><strong>Review before publication</strong><p>Does this granularity feel right? Are the blocking edges correct? Should any tickets be merged or split?</p><p class="note">Each ticket includes its own acceptance criteria and ownership. Release still requires real Lean, isolation, fork, merge-enforcement, merge-queue, portability, and recovery evidence.</p></div>
<script>const list=[...document.querySelectorAll('#tickets>li')],lane=document.getElementById('lane'),roots=document.getElementById('roots');function filter(){let count=0;for(const row of list){const show=(lane.value==='all'||row.dataset.lane===lane.value)&&(roots.getAttribute('aria-pressed')!=='true'||row.dataset.root==='true');row.classList.toggle('hidden',!show);count+=show?1:0}document.getElementById('count').textContent=count+' tickets shown';return count}lane.addEventListener('change',filter);roots.addEventListener('click',()=>{roots.setAttribute('aria-pressed',String(roots.getAttribute('aria-pressed')!=='true'));filter()});if(filter()!==TICKET_COUNT)throw Error('Missing tickets');roots.click();if(filter()!==ROOT_COUNT)throw Error('Incorrect initial frontier');roots.click();lane.value='Portable CI';if(filter()!==PORTABLE_COUNT)throw Error('Lane filter failed');lane.value='all';filter();console.log('Ticket listing and filters passed: TICKET_COUNT tickets, ROOT_COUNT roots, PORTABLE_COUNT portable CI slices');</script></body></html>'''
page = page.replace('TICKET_COUNT', str(len(tickets))).replace('ROOT_COUNT', str(len(waves[0]))).replace('POST_CLI_COUNT', str(len(post_cli_ready))).replace('PORTABLE_COUNT', str(sum(t['lane'] == 'Portable CI' for t in tickets))).replace('WIDTH', str(width)).replace('WAVES', wave_html).replace('OPTIONS', options).replace('ROWS', ''.join(rows))
if published:
    page = page.replace("Proposed ProofCI tickets", "Published ProofCI tickets").replace("<span>proposed tickets</span>", "<span>published tickets</span>")
    page = page.replace("Proposal awaiting approval. No GitHub issues or labels were created. Proposed tracker: nhestrompia/proofci, with ready-for-agent.", "Approved and published to nhestrompia/proofci. Every issue body, ready-for-agent label, and native blocking relationship was read back and verified.")
    page = page.replace("Review before publication", "Implementation frontier").replace("Does this granularity feel right? Are the blocking edges correct? Should any tickets be merged or split?", "Tickets 01, 02, and 03 have no blockers. Refill available agent slots as dependencies finish.")
(ROOT / "review.html").write_text(page)
print(json.dumps({key: summary[key] for key in ['tickets', 'edges', 'waves', 'maxDependencyParallelism', 'maximumFrontier', 'state']}, indent=2))
print("Validated: acyclic/topological graph, no redundant edges, 44-story coverage, acceptance/ownership, one local snapshot per ticket. This generator performs no publication.")
