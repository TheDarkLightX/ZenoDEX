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

## 1a. One-Command Local Testnet Demo

For people who want to try the DEX, proof-mining status flow, zUSD, and perps
preview from a browser, start the local-only demo stack:

```bash
python3 tools/zenoctl.py testnet demo up
```

Or call the script directly:

```bash
scripts/zenodex_testnet_demo.sh up
```

Open:

```text
http://127.0.0.1:3000
```

The demo stack:

- builds the ZenoDEX UI container;
- starts the Python API behind nginx on the same origin;
- enables local/testnet DEX, proof-mining status, zUSD, perps preview, and
  confidential-attestation demo routes;
- binds the UI port to `127.0.0.1` by default;
- keeps the API bound to `127.0.0.1` inside the container;
- injects a local demo bearer token into the runtime UI config;
- does not enable production external writes.

Useful commands:

```bash
python3 tools/zenoctl.py testnet demo status
python3 tools/zenoctl.py testnet demo logs
python3 tools/zenoctl.py testnet demo smoke
python3 tools/zenoctl.py testnet demo down
```

The smoke command builds the operator-tools image and runs the full bounded
two-node ledger rehearsal, so it can take several minutes on a laptop.

Windows PowerShell:

```powershell
.\scripts\zenodex_testnet_demo.ps1 up
```

Optional local Tau node:

```bash
python3 tools/zenoctl.py testnet demo up --with-tau
```

## 1b. Install Local Wrappers

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

## 1c. Publish Release Artifacts

Release publication is handled by `.github/workflows/release-publish.yml`.
Pushing a `v*` tag builds the operator bundle, the Zeno Oracle Python-local zip,
the browser proof-client npm tarball, `SHA256SUMS`, and a release manifest. The
workflow then attaches those files to a GitHub Release and pushes the production
and operator-tool images to GHCR.

Tag-driven release:

```bash
git tag v0.1.0
git push origin v0.1.0
```

Manual runs default to packaging-only dry publication. Enable the public write
targets explicitly when you want to publish:

```bash
gh workflow run release-publish.yml \
  -f version=0.1.0 \
  -f publish_github_release=true \
  -f publish_containers=true \
  -f publish_npm=false
```

The npm package remains manual opt-in because it requires `NPM_TOKEN` and the
package version must match the public npm registry state. Enable it only for a
versioned release:

```bash
gh workflow run release-publish.yml \
  -f version=0.1.0 \
  -f publish_github_release=true \
  -f publish_containers=true \
  -f publish_npm=true
```

The published container images are:

```text
ghcr.io/<owner>/zenodex:<version>
ghcr.io/<owner>/zenodex-operator-tools:<version>
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

## 7. Join A Published Public Testnet

Once an operator publishes `public_network_config.json` at a stable HTTPS URL,
join through `zenoctl`:

```bash
python3 tools/zenoctl.py testnet publish-config \
  --bundle-root /var/lib/zenodex/public-testnet/bundle \
  --mirror-base-url https://seed.example.test/zeno-ledger-public-testnet/ \
  --writer-url https://seed.example.test/zeno-ledger-writer \
  --out /var/lib/zenodex/public-testnet/bundle/public_network_config.json
```

```bash
python3 tools/zenoctl.py testnet join \
  --config-url https://example.test/zeno-ledger-public-testnet/public_network_config.json \
  --node-id operator-laptop \
  --serve
```

If the host machine cannot receive inbound router or Wi-Fi traffic and the
budget is $0, use the outbound tunnel host:

```bash
python3 tools/zeno_ledger_public_tunnel_host.py \
  --out-dir /tmp/zeno-ledger-public-testnet-tunnel \
  --data-dir /tmp/zeno-ledger-node-a-tunnel
```

This starts the writer and bundle mirror on loopback, exposes one gateway
through a Cloudflare Quick Tunnel, writes that tunnel URL into
`public_network_config.json`, and prints the exact Machine B acceptance command.
Copy the generated token file contents to the Machine B peer token path shown
in the command.

This is a thin wrapper over `tools/zeno_ledger_node.py join-network`. It:

- downloads the published network config;
- syncs and verifies the indexed bundle from the advertised mirror;
- writes the local join artifacts under the chosen bundle/data directories;
- optionally serves local node status when `--serve` is set.

Safe defaults:

- `--bundle-root ~/.zenodex/testnet/bundle`
- `--data-dir ~/.zenodex/testnet/node`
- `--host 127.0.0.1`

Useful overrides:

```bash
python3 tools/zenoctl.py testnet join \
  --config-url https://example.test/zeno-ledger-public-testnet/public_network_config.json \
  --node-id operator-server-1 \
  --bundle-root /var/lib/zenodex/testnet/bundle \
  --data-dir /var/lib/zenodex/testnet/node \
  --host 0.0.0.0 \
  --port 8788 \
  --poll-seconds 5 \
  --serve
```

Preview the delegated command:

```bash
python3 tools/zenoctl.py testnet join \
  --config-url https://example.test/zeno-ledger-public-testnet/public_network_config.json \
  --node-id operator-laptop \
  --dry-run
```

This command does not create the hosted testnet by itself. The shared testnet
still depends on external operator infrastructure:

- seed/writer nodes;
- a published bundle mirror plus `public_network_config.json`;
- public read endpoints for the UI;
- faucet and test-collateral operations;
- monitoring and status pages.

The `v0.1.16` target is to make this a real public-testnet v0 flow after the
3-node multi-machine evidence gate passes. See
[docs/PUBLIC_TESTNET_V0_1_16_PLAN.md](PUBLIC_TESTNET_V0_1_16_PLAN.md).

## 8. Gate Split

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

## 9. Light Client Checkpoint Verification

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
