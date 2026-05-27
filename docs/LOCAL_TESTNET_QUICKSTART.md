# Local-Testnet Quickstart

One command brings up a real local-testnet stack of ZenoDEX against live
local backends. Every mounted UI tab exercises a real backend end-to-end on
your machine.

## What this gives you

| Service | Role |
|---|---|
| **3-node ZenoLedger** (writer + forwarder + read-only follower) | Live spot routes (`/api/pools`, `/api/swap`), block production / sync / replay |
| **Local Tau node** | Settlement validation; zUSD wallet bridge; perps wallet path |
| **Zeno Oracle service** | Oracle dashboard, freshness/reporter lifecycle, token-settlement |
| **Stdlib API** | All other `/api/*` routes (zUSD wallet/monetary, perps wallet, autotrader, confidential) |
| **UI + nginx** | The mounted dex-ui, single-origin path split, browser never sees bearer tokens |

## Prerequisites

- Docker (or Podman) with `docker compose` v2 (or `podman compose`) on PATH.
- Python 3.11+ for the orchestrator (no other Python deps required for the CLI itself).
- `external/tau-testnet/` cloned into the repo or extracted operator bundle.
  Tau is fetched by the tester and is not redistributed inside the ZenoDEX
  bundle:
  ```bash
  mkdir -p external
  git clone https://github.com/IDNI/tau-testnet.git external/tau-testnet
  ```

## From the GitHub release

Download, verify, and extract the operator bundle:

```bash
ZENODEX_VERSION=0.1.15

curl -L -o "zenodex-operator-${ZENODEX_VERSION}.tar.gz" \
  "https://github.com/TheDarkLightX/ZenoDEX/releases/download/v${ZENODEX_VERSION}/zenodex-operator-${ZENODEX_VERSION}.tar.gz"
curl -L -o SHA256SUMS \
  "https://github.com/TheDarkLightX/ZenoDEX/releases/download/v${ZENODEX_VERSION}/SHA256SUMS"

sha256sum -c --ignore-missing SHA256SUMS

tar -xzf "zenodex-operator-${ZENODEX_VERSION}.tar.gz"
cd "zenodex-operator-${ZENODEX_VERSION}"
```

Clone Tau locally, then bring up the stack:

```bash
mkdir -p external
git clone https://github.com/IDNI/tau-testnet.git external/tau-testnet

python3 tools/zenoctl.py testnet local up \
  --out-dir ./local-testnet \
  --engine docker \
  --ui-port 18081 \
  --health-timeout 240
```

Open <http://127.0.0.1:18081>.

## Bring it up from a source checkout

```bash
python3 tools/zenoctl.py testnet local up --out-dir /tmp/zen-local
```

From an installed operator bundle, the shorter wrapper is equivalent:

```bash
zenodex-local-testnet up --out-dir /tmp/zen-local
```

When the stack is healthy you'll see:

```
[testnet-local phase=done] stack up: http://127.0.0.1:18080

ZenoDEX local-testnet is up.

  UI:                http://127.0.0.1:18080
  Compose project:   zenodex-local-testnet-<hash8>
  Chain ID:          zeno-ledger-localtest-v0
  Manifest:          /tmp/zen-local/local_testnet_manifest.json
  Fixtures:          /tmp/zen-local/fixtures/keys.json
```

Open <http://127.0.0.1:18080> in a browser. Every tab is wired to a real
local backend.

## Lifecycle

| Command | What it does |
|---|---|
| `zenoctl testnet local up --out-dir DIR` | Bring up the stack and seed initial state. Refuses if a stack already exists in DIR; pass `--force` to wipe and recreate. |
| `zenoctl testnet local down --out-dir DIR` | Stop the stack. Preserves compose volumes, manifest, and fixtures. |
| `zenoctl testnet local status --out-dir DIR [--json]` | Show stack health, per-service state, and per-lane readiness. |
| `zenoctl testnet local smoke --out-dir DIR [--browser auto\|off\|required]` | Exercise live spot, zUSD, perps, Oracle, AutoTrader, confidential, and optional browser UI paths. Writes `<out-dir>/reports/local_smoke_report.json`. |
| `zenoctl testnet local logs --out-dir DIR [--service NAME] [--tail N]` | Stream or tail compose logs from one service or the whole stack. |
| `zenoctl testnet local reset --out-dir DIR --force` | Destructive: stops the stack, removes compose volumes, and deletes the out-dir (manifest + fixtures + reports). `--force` is required. |

Running `up` a second time on the same `--out-dir` produces byte-identical
fixture keys (seed derived from `abspath(out_dir) + chain_id`). To rotate,
use `--seed <64-hex>` or `--random`.

## Verify the Full Feature Path

After bring-up, run the smoke checker:

```bash
python3 tools/zenoctl.py testnet local smoke \
  --out-dir /tmp/zen-local \
  --browser required
```

Installed wrapper form:

```bash
zenodex-local-testnet smoke --out-dir /tmp/zen-local --browser required
```

This submits real local-testnet feature transactions through the running
stack and then loads the UI in headless Chrome/Chromium. The backend checks
cover spot swap, zUSD wallet transfer, zUSD monetary epoch advance, perps
clearing-price publication, Oracle write flow, AutoTrader live prepare, and
confidential runtime execution. The browser checks cover the mounted UI
tabs for those same surfaces.

Use `--browser off` for API-only verification on machines without Chrome.
Use `--browser auto` to run UI checks when Chrome is available and skip them
otherwise.

## What each UI tab is wired to

| Tab / route | Backend | Notes |
|---|---|---|
| Spot pools | ZenoLedger writer (`/api/pools`, `/api/swap`) | Mutation auth: nginx injects the writer bearer; browser never holds it. |
| zUSD wallet (Tau / monetary) | Stdlib API (`/api/zusd/*`) | Talks to local Tau. |
| Perps wallet | Stdlib API (`/api/perps/wallet/*`) | Authoritative live path. The perps grid in the UI remains preview-only. |
| AutoTrader | Stdlib API (`/api/strategy/autotrader/*`) | Local supervisor profile is in fixtures. |
| Confidential | Stdlib API (`/api/confidential/*`) | Status and attestation routes. |
| Oracle dashboard | Oracle service (`/api/oracle/*`) | Reverse-proxied through nginx (same-origin). |

## Where to find things

```text
<out-dir>/
├── local_testnet_manifest.json          # service URLs, ports, fixture paths, writer_token_sha256 (NOT the raw token)
├── fixtures/
│   ├── keys.json                        # deterministic role keys (operator, oracle authority, perps authority, autotrader, guardians, Alice/Bob/Carol)
│   ├── oracle_authority_profile.json
│   ├── perps_wallet_authority_profile.json
│   ├── autotrader_supervisor_profile.json
│   └── guardians.json
└── rendered/
    ├── nginx.local-testnet.conf          # mounted into nginx container (CONTAINS writer + stdlib tokens; 0600; loopback-only)
    └── zenodex-config.json               # UI runtime config (NEVER contains tokens)
```

## Security posture

- **Loopback only.** Only nginx exposes a host port (`127.0.0.1:18080`). All
  backend services live on the compose network and cannot be reached from
  outside the host.
- **Browser never holds bearer tokens.** The UI calls relative `/api/*`
  paths; nginx injects the right bearer token server-side. The rendered
  `nginx.local-testnet.conf` contains the live tokens (mode 0600); the
  manifest stores only `sha256(writer_token)`.
- **No auth gateway.** Anyone with shell access to your host can hit the
  API. This is local-only by design; do NOT expose any port from this
  stack to a public network.
- **Fixture keys are local-only.** They are deterministic per-out-dir and
  marked with `non_claims` in their bundle. Never reuse them on a public
  network.

## Non-claims

- The perps grid in the UI is preview-only; authoritative perps testing
  uses the `/api/perps/wallet/*` panel.
- This is NOT a shared public testnet. There are no public seed nodes, no
  hosted faucet, and no monitoring page. Joining a public testnet is a
  separate flow.
- The local Tau node uses `TAU_FORCE_TEST=1`; this is the local test mode
  and is not the production Tau settlement posture.

## Troubleshooting

| Symptom | Likely cause / fix |
|---|---|
| `required dependency missing: …/external/tau-testnet` | Clone it: `cd external && git clone https://github.com/IDNI/tau-testnet.git`. |
| `host port 127.0.0.1:18080 is in use` | Either another stack is up (`docker ps`) or another process holds the port. Pick a different port with `--ui-port 18081`. |
| `existing manifest detected … Re-run with --force` | A stack already exists in this `--out-dir`. Either `zenoctl testnet local down`, or pass `--force` to recreate. |
| Timed out waiting for UI `/health` | The orchestrator tails the last 20 lines of each service's log when health fails. Read those, then `zenoctl testnet local down` and retry. |
| `docker` not on PATH | Install Docker or Podman; pass `--engine podman` to use Podman. |

## Related docs

- [docs/PERMISSIONLESS_HOSTING.md](PERMISSIONLESS_HOSTING.md): the local-Tau-node-first operator posture.
- [docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md](ZENO_LEDGER_TWO_MACHINE_TESTNET.md): two-machine ledger rehearsal.
- [docs/tau_testnet_local_node.md](tau_testnet_local_node.md): local Tau node alone.
- The existing `zenoctl testnet up --profile local` produces a 2-node
  ledger-only smoke; it is unchanged by this work. Prefer
  `zenoctl testnet local up` for the full UI/API/Tau/Oracle stack.
