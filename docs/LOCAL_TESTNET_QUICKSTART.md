# Local-Testnet Quickstart

One command brings up a real local-testnet stack of ZenoDEX against live
local backends. The current profile mounts Spot, Oracle, and bounded
Confidential test paths. Stream `8` perps, stream `9` zUSD wallet, stream `11`
zUSD monetary, and AutoTrader are quarantined. Retained UI surfaces can include
routes that remain unavailable.

## What this gives you

| Service | Role |
|---|---|
| **3-node ZenoLedger** (writer + forwarder + read-only follower) | Live spot routes (`/api/pools`, `/api/swap`), block production / sync / replay |
| **Local Tau node** | Retained local settlement dependency; stream `8`, `9`, and `11` application routes are unmounted |
| **Zeno Oracle service** | Oracle dashboard, freshness/reporter lifecycle, token-settlement |
| **Stdlib API** | Health plus bounded Confidential operations; normal startup refuses stream `8`, stream `9`, stream `11`, and AutoTrader routes |
| **UI + nginx** | The mounted dex-ui, single-origin path split, browser never sees bearer tokens |

## Prerequisites

- Docker (or Podman) with `docker compose` v2 (or `podman compose`) on PATH.
- `cloudflared` on PATH for the public launcher, or Docker/Podman access to run
  `cloudflare/cloudflared:latest`. You can also pass `--tunnel-url` for an
  already-created tunnel.
- `external/tau-testnet/` cloned into the repo:
  ```bash
  mkdir -p external && cd external && \
    git clone https://github.com/IDNI/tau-testnet.git && cd ..
  ```
- Python 3.11+ for the orchestrator (no other Python deps required for the CLI itself).

## Bring it up

For the public v0.1.16 path, use the launcher:

```bash
./bin/zenodex-public-testnet
```

From an installed operator bundle:

```bash
zenodex-public-testnet
```

That workflow refuses before stack or tunnel effects because its release smoke
requires quarantined stream `8` and stream `11`. The legacy
`--no-release-smoke` flag cannot bypass the current profile admission.

The manual local-only command remains:

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
  Compose project:   zenodex-local-testnet-v2-<hash32>
  Chain ID:          zeno-ledger-localtest-v0
  Manifest:          /tmp/zen-local/local_testnet_manifest.json
  Fixtures:          /tmp/zen-local/fixtures
  Key secrets:       /tmp/zen-local/secrets/keys.json
```

Open <http://127.0.0.1:18080> in a browser. Spot, Oracle, and bounded
Confidential test actions are wired to local backends. Perps, both zUSD routes,
and AutoTrader are unmounted.

## Lifecycle

| Command | What it does |
|---|---|
| `zenoctl testnet local up --out-dir DIR [--zk-mode auto-strict\|strict\|open]` | Bring up the stack and seed initial state. If a manifest already exists in DIR, restart from the saved artifacts; pass `--force` to wipe and recreate. Default ZK posture is `auto-strict`. |
| `zenoctl testnet local down --out-dir DIR` | Stop the stack. Preserves compose volumes, manifest, and fixtures. |
| `zenoctl testnet local status --out-dir DIR [--json]` | Show stack health, per-service state, and per-lane readiness. |
| `zenoctl testnet local smoke --out-dir DIR [--browser auto\|off\|required]` | Exercise Spot, Oracle, bounded Confidential, and optional browser checks. Stream `8`, stream `9`, stream `11`, and AutoTrader are omitted. Writes `<out-dir>/reports/local_smoke_report.json`. |
| `zenoctl testnet local release-smoke --out-dir DIR` | Refuse deterministically because the historical release flow requires quarantined stream `8` and stream `11`; no manifest or runtime is accessed. |
| `zenoctl testnet local public [--no-open] [--no-release-smoke]` | Retained command surface that refuses before stack or tunnel effects. The legacy bypass flag does not alter the canonical admission result. |
| `zenoctl testnet local public-up --out-dir DIR` | Refuse before stack, tunnel, manifest, or host-report effects while the current profile is release-ineligible. |
| `zenoctl testnet local logs --out-dir DIR [--service NAME] [--tail N]` | Stream or tail compose logs from one service or the whole stack. |
| `zenoctl testnet local reset --out-dir DIR --force` | Destructive: stops the stack, removes compose volumes, and deletes the out-dir (manifest + fixtures + reports). `--force` is required. |

Running `up` a second time on the same `--out-dir` produces byte-identical
fixture keys (seed derived from `abspath(out_dir) + chain_id`). To rotate,
use `--seed <64-hex>` or `--random`.

The retained `--zk-mode` settings describe historical proof-wrapper donor
configuration. They do not enable stream `8`, stream `9`, or stream `11` in the
current profile. Perps and both zUSD routes remain unmounted under every ZK
mode. Local fixture key control and retained proof-wrapper evidence always
report `production_security_claim=false`.

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

This submits local-testnet Spot, Oracle, and bounded Confidential test
transactions through the running stack and then loads their retained UI paths
in headless Chrome/Chromium. Stream `8`, stream `9`, stream `11`, and
AutoTrader remain outside this smoke path.

Use `--browser off` for API-only verification on machines without Chrome.
Use `--browser auto` to run UI checks when Chrome is available and skip them
otherwise.

## Public fake-value testnet

The v0.1.16 public release path is currently blocked:

```bash
./bin/zenodex-public-testnet
```

The launcher refuses before local stack or tunnel effects because
`release-smoke` depends on quarantined routes. The legacy
`--no-release-smoke` flag does not bypass current-profile admission. Operators
must not expose a public tunnel for this retained profile. The commands below
are historical examples only and are not part of the current launch path:

```bash
cloudflared tunnel --url http://127.0.0.1:18080
```

or the fallback container:

```bash
docker run --rm --network host cloudflare/cloudflared:latest \
  tunnel --no-autoupdate --url http://127.0.0.1:18080
```

and prints:

- public UI URL;
- public network config URL;
- public network config hash;
- admin/write token file location;
- read-only tester instructions.

Scripted form with an explicit output directory:

```bash
python3 tools/zenoctl.py testnet local public-up \
  --out-dir /tmp/zen-public-v016 \
  --release-smoke \
  --open
```

No public URL is created by the current command. A later profile must add an
explicit release admission before any tunnel or host report can be produced.
When an older output directory records retired value routes, every lifecycle
command first stops its exact Compose project. A forced rebuild must also use a
different `--ui-port`; this prevents a still-running managed tunnel from
reattaching to the new local origin at the historical port. `reset` removes the
retired Compose volumes while preserving the old manifest as an origin-identity
marker, then returns a blocked status until that fresh-port rebuild occurs.

Same-origin public routes:

| Route | Purpose |
|---|---|
| `/` | Public browser UI. |
| `/public_network_config.json` | Single URL used by external followers. Includes the config hash. |
| `/ledger-bundle/...` | Read-only public bundle artifacts for follower sync and replay. |
| `/live`, `/live/header/...`, `/live/body/...` | Read-only live block follow API used by external followers. |
| `/status`, `/features`, `/tokens`, `/network` | Read-only node, feature, token, and network status. |
| `/api/*`, `/tx` | Release-flow APIs and transaction submission paths. |

Browser users do not receive bearer tokens. nginx injects local writer/API
tokens server-side. This transport property does not admit perps or zUSD value
routes. The retained v0.1.16 release flow cannot currently be exercised.

The following command is expected to return the typed quarantine rejection:

```bash
python3 tools/zenoctl.py testnet local release-smoke \
  --out-dir /tmp/zen-public-v016
```

The release evidence manifest is checked with:

```bash
python3 tools/check_public_testnet_v0_1_16_evidence.py \
  /path/to/public-testnet-v0.1.16-evidence.json
```

Historical v0.1.16 evidence requirements, not satisfied by the current profile:

- Docker/local full-stack smoke report;
- external laptop acceptance report from `zenodex-public-follower`;
- second clean follower report from `zenodex-public-follower`;
- phone/browser validation report over HTTPS;
- release-flow transaction smoke JSON;
- residual-limits statement covering fake value, no production value, moves no
  mainnet assets, and session-stable Quick Tunnel limits when applicable.

External follower command:

```bash
zenodex-public-follower \
  --config-url https://<quick-tunnel-host>/public_network_config.json
```

The follower report must include the public config hash, live follower and seed
tips, and `common_header_match: true`.

## What each UI tab is wired to

| Tab / route | Backend | Notes |
|---|---|---|
| Spot pools | ZenoLedger writer (`/api/pools`, `/api/swap`) | Mutation auth: nginx injects the writer bearer; browser never holds it. |
| zUSD monetary | Unmounted (`/api/zusd/monetary/*`) | Normal startup refuses the retired stream `11` application bridge. |
| Perps wallet | Unmounted (`/api/perps/wallet/*`) | Normal startup refuses the retired stream `8` application bridge. The perps grid remains a retained preview. |
| AutoTrader | Unmounted (`/api/strategy/autotrader/*` refused at startup) | UI retained; no local-testnet submission authority. |
| Confidential | Stdlib API (`/api/confidential/*`) | Status and attestation routes. |
| Oracle dashboard | Oracle service (`/api/oracle/*`) | Reverse-proxied through nginx (same-origin). |

## Where to find things

```text
<out-dir>/
├── local_testnet_manifest.json          # service URLs, ports, fixture paths, token hashes (NOT raw tokens)
├── secrets/
│   └── keys.json                        # deterministic role keys, mode 0600, not mounted into API containers
├── fixtures/
│   ├── oracle_authority_profile.json
│   ├── perps_wallet_authority_profile.json
│   ├── perps_wallet_recovery_exercise.json
│   ├── perps_wallet_rotation_exercise.json
│   ├── perps_wallet_device_approval_exercise.json
│   ├── perps_wallet_signer_device_integration.json
│   ├── perps_wallet_signer_prompt_capture.json
│   ├── perps_wallet_signer_execution_exercise.json
│   ├── perps_wallet_encrypted_sss_backup.json
│   ├── perps_wallet_encrypted_sss_recipient_keys.json
│   ├── autotrader_supervisor_profile.json
│   └── guardians.json
└── rendered/
    ├── nginx.local-testnet.conf          # mounted into nginx container (CONTAINS writer + stdlib tokens; 0600; loopback-only)
    └── zenodex-config.json               # UI runtime config (NEVER contains tokens)
```

## Security posture

- **Loopback only.** Only nginx exposes a host port (`127.0.0.1:18080`). All
  backend services live on the compose network and cannot be reached from
  outside the host. The current profile refuses `public-up` and does not start
  a Quick Tunnel.
- **Browser never holds bearer tokens.** The UI calls relative `/api/*`
  paths; nginx injects the right bearer token server-side. The rendered
  `nginx.local-testnet.conf` contains the live tokens (mode 0600); the
  manifest stores only token hashes.
- **Tokenomics authority gate.** Status and smoke reports include ZK posture
  plus key-management authority readiness. The local tokenomics lane remains
  disabled with `TOKENOMICS_AUTHORITY_NOT_READY` until the wallet authority
  profile, signer threshold, recovery policies, recovery/rotation exercises,
  device approval, signer ceremony, hardware or fixture custody, and encrypted
  SSS backup checks are ready.
- **Encrypted SSS backup donor fixture.** The retained fixture set includes a 3-of-5
  Shamir backup of the perps wallet fixture key. Each share is encrypted with
  `cryptography` AES-256-GCM using HKDF-derived per-recipient keys before it is
  assigned to recovery email, cloud-drive (`dropbox`/`box` style), or
  offline-export transport. The recipient replay-key fixture remains offline
  test material. The current API container receives no fixtures mount and no
  perps authority, recovery, signer, backup, or reconstruction file. Direct
  isolated evaluator tests may supply the donor fixtures explicitly. Hardware
  custody evidence, strict ZK artifacts, and production promotion evidence
  remain separate gates. The fixture sets `production_security_claim=false`.
- **Public tunnel posture.** `public-up` currently refuses before resolving or
  starting a tunnel. Historical tunnel instructions below are donor material.
- **Fixture keys are local-only.** They are deterministic per-out-dir and
  marked with `non_claims` in their bundle. The browser/API runtime does not
  expose a fixture-key endpoint or fixture-role signing shortcut; signed smoke
  flows use the internal local harness. Never reuse fixture keys on a public
  network.

## Non-claims

- The perps grid in the UI is preview-only. The `/api/perps/wallet/*` write
  panel is retained donor code and is unmounted.
- `zenoctl testnet local up` is loopback-only. The default
  `zenoctl testnet local public-up` path refuses startup while the retained
  v0.1.16 release flow depends on quarantined routes. The legacy
  `--no-release-smoke` flag grants no bypass or release eligibility.
- The public path has no production value, moves no mainnet assets, and has no
  production consensus claim.
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

- [docs/PERMISSIONLESS_HOSTING.md](PERMISSIONLESS_HOSTING.md) — the local-Tau-node-first operator posture.
- [docs/PUBLIC_TESTNET_V0_1_16.md](PUBLIC_TESTNET_V0_1_16.md) — v0.1.16 fake-value public testnet release target.
- [docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md](ZENO_LEDGER_TWO_MACHINE_TESTNET.md) — two-machine ledger rehearsal.
- [docs/tau_testnet_local_node.md](tau_testnet_local_node.md) — local Tau node alone.
- The existing `zenoctl testnet up --profile local` produces a 2-node
  ledger-only smoke; it is unchanged by this work. Prefer
  `zenoctl testnet local up` for the full UI/API/Tau/Oracle stack.
