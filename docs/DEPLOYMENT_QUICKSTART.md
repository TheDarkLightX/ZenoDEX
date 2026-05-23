# ZenoDeploy Operator Quickstart

This is the short operator path for running ZenoDEX/ZenoLedger safely from the
repo checkout. It wraps existing release, public-testnet, and container checks
behind stable commands.

## 1. Doctor

Run a lightweight static check:

```bash
python3 tools/zenoctl.py doctor --engine none --strict
```

For CI or machines without Docker/Podman installed:

```bash
python3 tools/zenoctl.py doctor --engine none --strict
```

The doctor checks the production Dockerfiles, compose files, deployment
profiles, hash-locked Python requirement files, the ZenoLedger node tool, the
public-testnet gates, and operator preflight entrypoint. It also checks that the
Dockerfiles install runtime Python dependencies from
`requirements-core.lock.txt` with `--require-hashes`.

## 1a. Install Local Wrappers

For macOS and Linux, install stable wrappers into a user-local bin directory:

```bash
scripts/install_zenodex.sh --bin-dir "$HOME/.local/bin"
```

Preview first:

```bash
scripts/install_zenodex.sh --dry-run
```

For Windows PowerShell:

```powershell
.\scripts\install_zenodex.ps1 -BinDir "$HOME\.zenodex\bin"
```

These wrappers install `zenoctl` and `zenodex-node`. They call this checkout's
Python tools directly and do not install services, write secrets, or modify
shell profiles. They also install `zenodex-local-testnet`, a short wrapper for
`zenoctl testnet local`.

Run the packaging readiness check:

```bash
python3 tools/check_operator_packaging.py --pretty
```

Build a deterministic operator release bundle:

```bash
python3 tools/build_operator_release_bundle.py build \
  --version dev \
  --out-dir /tmp/zenodex-release
```

Verify the bundle manifest:

```bash
python3 tools/build_operator_release_bundle.py verify \
  --manifest /tmp/zenodex-release/zenodex-operator-dev.tar.gz.manifest.json
```

## 2. Operator Preflight

Run the operator preflight gate:

```bash
python3 tools/zenoctl.py prod preflight
```

Static-only form:

```bash
python3 tools/zenoctl.py prod preflight --skip-engine
```

Strict base-image digest mode:

```bash
python3 tools/zenoctl.py prod preflight --strict-digest
```

The preflight gate checks:

- Docker hash-locked runtime install;
- deployment, proof, and UPBA policy profiles;
- Python hash lock status;
- container hardening artifacts;
- minimal ZenoOps status output;
- deployment compose files and container engine availability, unless skipped.

## 3. Local Testnet Bundle

Build a local public-testnet bundle:

```bash
python3 tools/zenoctl.py testnet init \
  --out-dir /tmp/zeno-ledger-public-testnet
```

Preview the command without running it:

```bash
python3 tools/zenoctl.py testnet init --dry-run
```

## 4. Local Two-Node Smoke

Run the same-machine public-network smoke:

```bash
python3 tools/zenoctl.py testnet up \
  --profile local \
  --out-dir /tmp/zenoctl-public-testnet \
  --report-out /tmp/zenoctl-public-testnet/report.json
```

This uses `tools/zeno_ledger_public_network_smoke.py` and writes a replayable
JSON report.

## 4a. Full Local Testnet (UI + Backends, One Command)

For exercising the mounted UI against live local backends (3-node ledger +
Tau + Oracle + stdlib API), use the dedicated `local` subcommand:

```bash
python3 tools/zenoctl.py testnet local up --out-dir /tmp/zen-local
```

Open <http://127.0.0.1:18080> when bring-up reports `phase=done`. Every UI
tab hits a real local backend. See
[docs/LOCAL_TESTNET_QUICKSTART.md](LOCAL_TESTNET_QUICKSTART.md) for the
full guide (lifecycle, fixture locations, what each tab is wired to,
security posture).

Installed operator-bundle form:

```bash
zenodex-local-testnet up --out-dir /tmp/zen-local
zenodex-local-testnet smoke --out-dir /tmp/zen-local --browser required
```

Lifecycle:

```bash
python3 tools/zenoctl.py testnet local status --out-dir /tmp/zen-local
python3 tools/zenoctl.py testnet local smoke  --out-dir /tmp/zen-local --browser required
python3 tools/zenoctl.py testnet local down   --out-dir /tmp/zen-local
```

Requires Docker (or Podman) and `external/tau-testnet/` cloned into the
repo.

## 5. Full Public-Testnet Candidate Gate

Run the heavier public-testnet candidate gate through the same CLI:

```bash
python3 tools/zenoctl.py testnet up \
  --profile public-testnet-gate \
  --out-dir /tmp/zenodex-public-testnet-gate
```

## 6. Docker Two-Node Smoke

Run the containerized public-network smoke profile:

```bash
python3 tools/zenoctl.py testnet up --profile docker-two-node
```

Preview the compose command:

```bash
python3 tools/zenoctl.py testnet up --profile docker-two-node --dry-run
```

This uses `docker-compose.two-node.yml` and the hash-locked
`Dockerfile.operator-tools` image.

## 7. Gate Split

Use the narrow gate while editing:

```bash
bash tools/gate_dev_fast.sh
```

Run the focused type gate directly:

```bash
bash tools/gate_typecheck.sh
```

View the operator cockpit:

```bash
python3 tools/zenoctl.py node status \
  --node-identity local-operator \
  --node-label "local operator" \
  --peer-count 1
```

The cockpit uses a chain-bound node hash. Labels are only display hints, so
operators do not depend on names like `node-a`.

Use the operator preflight before running a node:

```bash
bash tools/gate_operator_preflight.sh --skip-engine
```

Use the release wrapper for the full release gate:

```bash
bash tools/gate_release_full.sh
```

## 8. Light Client Checkpoint Verification

Light clients should verify a checkpoint range plus an external finality quorum
instead of running a full node:

```bash
python3 tools/zenoctl.py light-client verify-checkpoint \
  --headers-dir /path/to/headers \
  --bodies-dir /path/to/bodies \
  --checkpoints-dir /path/to/checkpoints \
  --registry /path/to/signer_registry.json \
  --envelope /path/to/checkpoint.a.sig.json \
  --envelope /path/to/checkpoint.b.sig.json \
  --from-height 1 \
  --to-height 100 \
  --pretty
```

This is the right shape for phones and browser-hosted clients: they consume a
small checkpoint bundle, verify quorum signatures, and avoid full node storage
and networking.

To package that evidence for the browser SDK:

```bash
python3 tools/zenoctl.py light-client build-browser-bundle \
  --headers-dir /path/to/headers \
  --bodies-dir /path/to/bodies \
  --checkpoints-dir /path/to/checkpoints \
  --registry /path/to/signer_registry.json \
  --envelope /path/to/checkpoint.a.sig.json \
  --envelope /path/to/checkpoint.b.sig.json \
  --from-height 1 \
  --to-height 100 \
  --out /tmp/zenodex-browser-checkpoint-bundle.json \
  --pretty
```

The browser package lives at `tools/dex-ui/src/sdk/zenoProofClient.js`. Version
0 verifies bundle hash binding and wallet-sync rollback rules in browser code,
while relying on the Python builder for BLS quorum verification.

## Current Limits

The Docker two-node smoke is still a bounded evidence flow, not a long-running
public validator network. Use `tools/gate_public_testnet_live.sh` for the
public-testnet candidate gate once the operator machine is ready.
