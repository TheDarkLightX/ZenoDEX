# Local-Testnet Quickstart

One command brings up a real local-testnet stack of ZenoDEX against live
local backends. Mounted actions exercise real local backends end-to-end on
your machine. Retained UI surfaces can include routes that remain unavailable.

## What this gives you

| Service | Role |
|---|---|
| **3-node ZenoLedger** (writer + forwarder + read-only follower) | Live spot routes (`/api/pools`, `/api/swap`), block production / sync / replay |
| **Local Tau node** | Settlement validation; zUSD monetary path; perps wallet path |
| **Zeno Oracle service** | Oracle dashboard, freshness/reporter lifecycle, token-settlement |
| **Stdlib API** | Mounted `/api/*` routes for zUSD monetary, perps wallet, and confidential operations. Normal startup refuses the zUSD Tau wallet and AutoTrader routes. |
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

That starts the full local stack from `~/.zenodex/public-testnet-v0.1.16`,
runs the release-flow smoke, opens a Cloudflare Quick Tunnel, and opens the
public UI URL in your default browser. Double-clicking
`bin/zenodex-public-testnet.command` does the same on macOS.

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

Open <http://127.0.0.1:18080> in a browser. Mounted actions are wired to real
local backends. The AutoTrader route and stream `9` zUSD Tau wallet are unmounted.

## Lifecycle

| Command | What it does |
|---|---|
| `zenoctl testnet local up --out-dir DIR [--zk-mode auto-strict\|strict\|open]` | Bring up the stack and seed initial state. If a manifest already exists in DIR, restart from the saved artifacts; pass `--force` to wipe and recreate. Default ZK posture is `auto-strict`. |
| `zenoctl testnet local down --out-dir DIR` | Stop the stack. Preserves compose volumes, manifest, and fixtures. |
| `zenoctl testnet local status --out-dir DIR [--json]` | Show stack health, per-service state, and per-lane readiness. |
| `zenoctl testnet local smoke --out-dir DIR [--browser auto\|off\|required]` | Exercise live spot, zUSD monetary, perps, Oracle, confidential, and optional browser UI paths. AutoTrader and the stream `9` zUSD Tau wallet are omitted. Writes `<out-dir>/reports/local_smoke_report.json`. |
| `zenoctl testnet local release-smoke --out-dir DIR` | Exercise the public v0.1.16 flow: verify startup-funded fixture accounts, faucet `tAGRS`, deposit fake native AGRS collateral, mint `zUSD`, deposit perps collateral, open long/short, settle perps state, swap `tAGRS/tZDEX`, and verify live height plus header/config hashes. Writes `<out-dir>/reports/release_flow_smoke_report.json`. |
| `zenoctl testnet local public [--no-open] [--no-release-smoke]` | Point-and-click public mode. Uses `~/.zenodex/public-testnet-v0.1.16` by default, validates the release flow, starts the Quick Tunnel, and opens the public UI. |
| `zenoctl testnet local public-up --out-dir DIR` | Bring up the same stack and expose it through a Cloudflare Quick Tunnel. Writes `<out-dir>/reports/public_testnet_host_report.json` after the public URL is known. |
| `zenoctl testnet local logs --out-dir DIR [--service NAME] [--tail N]` | Stream or tail compose logs from one service or the whole stack. |
| `zenoctl testnet local reset --out-dir DIR --force` | Destructive: stops the stack, removes compose volumes, and deletes the out-dir (manifest + fixtures + reports). `--force` is required. |

Running `up` a second time on the same `--out-dir` produces byte-identical
fixture keys (seed derived from `abspath(out_dir) + chain_id`). To rotate,
use `--seed <64-hex>` or `--random`.

`--zk-mode auto-strict` uses the bundled local live-wrapper verifier for
fake-value zUSD/perps write gates when no explicit verifier environment is set.
`--zk-mode strict` refuses bring-up if the active verifier command or verifier
plus circuit artifact hashes are incomplete. `--zk-mode open` disables the
local proof-wrapper gate for non-production development. Local fixture custody
and the bundled live-wrapper verifier always report
`production_security_claim=false`.

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
cover spot swap, grouped transactions, zUSD monetary epoch advance, perps
clearing-price publication, Oracle write flow, and confidential runtime
execution. The browser checks cover the corresponding mounted actions.
AutoTrader and the stream `9` zUSD Tau wallet remain outside this smoke path.

Use `--browser off` for API-only verification on machines without Chrome.
Use `--browser auto` to run UI checks when Chrome is available and skip them
otherwise.

## Public fake-value testnet

For v0.1.16, the zero-cost public path is a Cloudflare Quick Tunnel over the
full local-testnet stack:

```bash
./bin/zenodex-public-testnet
```

The launcher starts or restarts the local stack, runs `release-smoke`, and then
launches a Quick Tunnel through either local `cloudflared`:

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

The public URL is session-stable. It remains usable while the `cloudflared`
process or fallback container is running, and it changes when a new Quick
Tunnel session is created.
If a stable named HTTPS domain is configured later, record
`public_config_url_posture: stable_named_url` in the release evidence.

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
tokens server-side. Transaction-capable paths use the startup-funded fixture
accounts or signed local test wallet payloads. The launcher pre-funds fixture
accounts with fake native AGRS plus `tAGRS`/`tZDEX`, then the existing zUSD,
perps, and spot pages can exercise the release flows. The assets are fake-value
test assets: `tAGRS`, `tZDEX`, and collateralized `zUSD`.

After public bring-up, run the release-flow smoke:

```bash
python3 tools/zenoctl.py testnet local release-smoke \
  --out-dir /tmp/zen-public-v016
```

The release evidence manifest is checked with:

```bash
python3 tools/check_public_testnet_v0_1_16_evidence.py \
  /path/to/public-testnet-v0.1.16-evidence.json
```

Required v0.1.16 evidence:

- Docker/local full-stack smoke report;
- external laptop acceptance report from `zenodex-public-follower`;
- second clean follower report from `zenodex-public-follower`;
- phone/browser validation report over HTTPS;
- release-flow transaction smoke JSON;
- residual-limits statement covering fake value, no production value, no
  mainnet custody, and session-stable Quick Tunnel limits when applicable.

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
| zUSD monetary | Stdlib API (`/api/zusd/monetary/*`) | Mounted stream `11` actions talk to local Tau. Normal startup refuses `/api/zusd/wallet/*`. |
| Perps wallet | Stdlib API (`/api/perps/wallet/*`) | Authoritative live path. The perps grid in the UI remains preview-only. |
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
  outside the host unless `public-up` starts a Quick Tunnel.
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
- **Encrypted SSS backup fixture.** The local fixture set includes a 3-of-5
  Shamir backup of the perps wallet fixture key. Each share is encrypted with
  `cryptography` AES-256-GCM using HKDF-derived per-recipient keys before it is
  assigned to recovery email, cloud-drive (`dropbox`/`box` style), or
  offline-export transport. The public runtime config receives only encrypted
  backup receipts. A separate mode-0600 recipient replay-key fixture is mounted
  into the local API so status can decrypt threshold shares, reconstitute the
  fixture key, verify the subject public key, and replay hostile-share checks
  instead of trusting self-attested booleans. Status also requires provider
  diversity, per-envelope delivery receipts, and no raw key/share material in
  public reports. The runtime no longer fabricates external provider-delivery
  receipts: provider delivery uses configured SMTP/cloud/offline export
  backends or fails closed. Hardware custody evidence, strict ZK artifacts, and
  production promotion evidence remain separate gates. This is still a
  local-testnet fixture and sets `production_security_claim=false`.
- **Public tunnel posture.** `public-up` intentionally exposes nginx through a
  session-stable HTTPS tunnel. Use it only for fake-value testing. Do not expose
  raw backend service ports.
- **Fixture keys are local-only.** They are deterministic per-out-dir and
  marked with `non_claims` in their bundle. The browser/API runtime does not
  expose a fixture-key endpoint or fixture-role signing shortcut; signed smoke
  flows use the internal local harness. Never reuse fixture keys on a public
  network.

## Non-claims

- The perps grid in the UI is preview-only; authoritative perps testing
  uses the `/api/perps/wallet/*` panel.
- `zenoctl testnet local up` is loopback-only. `zenoctl testnet local public-up`
  is the shared fake-value testnet path for v0.1.16.
- The public path has no production value, no mainnet custody, and no
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
