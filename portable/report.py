"""Strict validation and normalization for reports crossing the worker boundary."""


def _required(value, kind, name):
    if not isinstance(value, kind):
        raise ValueError("report field is invalid: " + name)
    return value


def validate(report, envelope, baseline, *, attempt=False, attempt_id=None):
    if not isinstance(report, dict) or report.get("version") != 1:
        raise ValueError("worker report version is invalid")
    if report.get("envelope") != envelope:
        raise ValueError("worker report envelope does not match inputs")
    status = report.get("status")
    if status not in (("attempt",) if attempt else ("passed", "blocked", "error")):
        raise ValueError("worker report status is invalid")
    results = _required(report.get("results"), list, "results")
    obligations = baseline.get("obligations") if isinstance(baseline, dict) else None
    if not isinstance(obligations, list) or not obligations:
        raise ValueError("worker report cannot be checked against an empty baseline")
    expected = {item["id"]: item for item in obligations}
    if attempt:
        if not isinstance(attempt_id, str) or attempt_id not in expected:
            raise ValueError("worker attempt identity is invalid")
        expected = {attempt_id: expected[attempt_id]}
    if len(results) != len(expected):
        raise ValueError("worker report does not contain every obligation")
    seen = set()
    for result in results:
        if not isinstance(result, dict) or result.get("id") not in expected:
            raise ValueError("worker report contains an unknown obligation")
        obligation = expected[result["id"]]
        if result["id"] in seen or result.get("policy") != obligation["policy"]:
            raise ValueError("worker report obligation identity mismatch")
        seen.add(result["id"])
        if result.get("decision") not in ("verified", "violated", "unproven"):
            raise ValueError("worker report decision is invalid")
        if not isinstance(result.get("reason"), str) or not result["reason"]:
            raise ValueError("worker report reason is invalid")
        if result.get("evidence") not in (obligation["evidence"], obligation.get("refutation")):
            raise ValueError("worker report evidence identity mismatch")
        if result["decision"] in ("verified", "violated"):
            validation = result.get("validation")
            if not isinstance(validation, dict) or validation.get("decision") != result["decision"]:
                raise ValueError("accepted result lacks independent validation")
            if validation.get("candidate_sha256") != envelope["candidate_sha256"]:
                raise ValueError("accepted result candidate identity mismatch")
            if validation.get("contract_sha256") != obligation["contract_sha256"]:
                raise ValueError("accepted result contract identity mismatch")
    if seen != set(expected):
        raise ValueError("worker report is missing an obligation")
    counts = {decision: sum(item["decision"] == decision for item in results)
              for decision in ("verified", "violated", "unproven")}
    if report.get("property_counts") != counts:
        raise ValueError("worker report property counts are inconsistent")
    if status == "passed":
        if any(item["decision"] != "verified" for item in results if item["policy"] == "required"):
            raise ValueError("worker report passed with a blocking result")
    elif status == "error" and not isinstance(report.get("reason"), str):
        raise ValueError("worker error report lacks a reason")
    return report


def normalized(report, envelope, baseline):
    """Return only outcome data suitable for local/worker comparison."""
    validate(report, envelope, baseline)
    return {
        "status": report["status"],
        "results": [
            {
                "id": result["id"],
                "policy": result["policy"],
                "decision": result["decision"],
                "reason": result["reason"],
                "evidence": result.get("evidence"),
                "evidence_sha256": result.get("evidence_sha256", {}),
            }
            for result in sorted(report["results"], key=lambda item: item["id"])
        ],
        "property_counts": report["property_counts"],
    }
