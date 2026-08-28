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

These wrappers install `zenoctl`, `zenodex-node`, `zenodex-local-testnet`,
`zenodex-public-testnet`, and `zenodex-public-follower`. They call this
checkout's Python tools directly and do not install services, write secrets, or
modify shell profiles.

Run the packaging readiness check:

```bash
python3 tools/check_operator_packaging.py --pretty
```

Build a deterministic unadmitted operator candidate archive for format testing:

```bash
python3 tools/build_operator_release_bundle.py candidate \
  --version dev \
  --out-dir /tmp/zenodex-release
```

Verify the candidate manifest:

```bash
python3 tools/build_operator_release_bundle.py verify \
  --manifest /tmp/zenodex-release/zenodex-operator-candidate-dev.tar.gz.manifest.json
```

The `build` subcommand refuses before writing files while the current operator
profile is release-ineligible. Candidate archives grant no release or
publication authority. A successful candidate verification report binds the
manifest hash, archive hash, canonical candidate basename, current profile,
`authority: NONE`, `release_eligible: false`, and the empty VM-gate set. The
verifier rejects symlinked or changing manifests, renamed archives,
concatenated gzip members, and noncanonical tar tails.

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

Open <http://127.0.0.1:18080> when bring-up reports `phase=done`. Spot and the
bounded enabled research surfaces can reach local backends. Perps, both zUSD
routes, and AutoTrader remain visible donor surfaces without mounted write
backends. See
[docs/LOCAL_TESTNET_QUICKSTART.md](LOCAL_TESTNET_QUICKSTART.md) for the
full guide (lifecycle, fixture locations, what each tab is wired to,
security posture).

Installed operator-bundle form:

```bash
zenodex-public-testnet
zenodex-public-follower --config-url https://<quick-tunnel-host>/public_network_config.json
zenodex-local-testnet up --out-dir /tmp/zen-local
zenodex-local-testnet smoke --out-dir /tmp/zen-local --browser required
```

`zenodex-public-testnet` is a retained launcher. Its default historical release
smoke now refuses before stack, tunnel, manifest, report, or browser effects
because stream `8` and stream `11` are quarantined. Use the explicitly narrower
research workflow only when no v0.1.16 release claim is intended.
`zenodex-public-follower` is the outside-node path: it downloads the public
config, hash-pins the bundle, replays bootstrap, pulls live blocks, and emits a
common-header acceptance report.

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
