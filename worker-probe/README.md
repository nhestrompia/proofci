# Disposable worker probe

This launcher runs a fixed set of adversarial experiments in disposable Linux guests under QEMU. It does not run repository verification or accept public jobs. A passing probe is not a proof of correctness and does not establish that an arbitrary hosted workload is safe.

On an aarch64 machine with Docker, build and run:

```sh
docker build -t proofci-worker-probe worker-probe
docker run --rm --network none proofci-worker-probe --job probe --challenge sample-123
```

The optional `--challenge` accepts 1 to 64 letters, digits, underscores or hyphens. The trusted guest returns it in a `probe_receipt` artifact in the report. The launcher writes a JSON report to standard output and exits 0 only when all required checks pass. It returns 2 for failed checks or prerequisites and 130 when cancelled. To retain the report as an artifact, mount a directory and supply a path inside it:

```sh
docker run --rm --network none -v "$PWD/reports:/reports" proofci-worker-probe --job probe --report /reports/probe.json
```

The image uses software emulation and requires no `/dev/kvm`. The recorded Linux host is the Docker container's Linux kernel; on Docker Desktop it is not the physical host. A different architecture fails with a prerequisite error. The guest has no network device or host mounts. The dummy host files and Unix socket are created in the container solely for this probe; no real credentials are used.

The fixed guest checks access to the dummy host objects and a simulated other-repository cache sentinel, exercises cgroup memory and process limits, a supervised CPU budget, a disk workload confined to a size-limited tmpfs, and per-process limits. Separate guests exercise cancellation, fresh state, bounded output, and timeout. The serial result channel is trusted only because the guest runs these fixed, image-owned programs. It must not be reused as an authoritative channel for arbitrary job output. The challenge is the only job payload. No repository snapshot or executable job input is accepted by this launcher.

Run the host-side process tests in Linux with:

```sh
docker run --rm --network none -v "$PWD/worker-probe:/work:ro" --entrypoint python3 proofci-worker-probe -m unittest discover -s /work/tests -v
```
