---
title: README
type: note
permalink: autonomous-tau-dex-review/tools/dex-ui/readme
---

# ZenoDEX UI (React + Vite)

Frontend for ZenoDEX: Swap, Pools, Perpetuals, zUSD, Strategy, ZenoOracle,
and a Confidential tab for the TEE / sealed-bid feature surface.

Current mounted posture:
- Swap and pools target the Zeno ledger spot path.
- Oracle can bind to the local `tools/zenodex-oracle serve` API.
- zUSD in live mode targets the Tau-node-backed stream-9 wallet transport path.
- The zUSD monetary panel targets the Tau-node-backed stream-11 vault and
  stability-pool transaction path.
- Perps has a read-only preview grid plus a live stream-8 wallet panel for
  signed clearinghouse market init, collateral, position, epoch, oracle-price,
  and settle transactions. Local preview writes for the older `/api/perps/*`
  lane require an explicit override and still do not represent authoritative
  settlement.
- Strategy remains a planning workbench and reference surface. It does not
  submit live strategies.
- Confidential exposes live operator posture through `GET /api/confidential/status`
  plus static proof and disaster-surface context. It is not the default swap
  path or a generally enabled execution lane.

The Confidential tab is not just a status page. It explains:
- who the feature is for,
- why a user would choose it,
- when the normal public path is better,
- which formal checks back the current experiment.
- and, in live mode, the current beta posture from `GET /api/confidential/status`.

The Oracle tab is a local ZenoOracle operator console. It renders feeds,
reporter health, source diversity, accepted reads, terminal authorizations,
disputes, rewards, selected-feed status, evidence class, and the local replay
posture. With a local Oracle server running in write-enabled mode, it can also
draft feed queries, create/register/bond a reporter, and submit local reports
through the same deterministic CLI-backed endpoints. The receipt builder can
also build local aggregates, accept reads, and emit typed OracleAuthorization
bundles for local replay testing. Quick Verify calls the local read-only
receipt verifier for stored receipt IDs.

Oracle sub-views are addressable with `oracleView`, for example:

```text
http://127.0.0.1:5173/?tab=oracle&oracleView=Receipts
```

Supported Oracle views are `Overview`, `Feeds`, `Reports`, `Reporters`,
`Disputes`, `Receipts`, `Verify`, and `Governance`.

## Dev Server

```bash
npm install
npm run dev
```

To bind the UI to the local stdlib API server:

```bash
# In repo root (starts the minimal REST API on 127.0.0.1:8000 by default)
PERPS_API_ENABLED=true ZUSD_API_ENABLED=true DEMO_API_TOKEN=sekret python3 -m src.integration.api_server
```

Then run the UI. The Vite dev-server proxy avoids local CORS setup:

```bash
# IMPORTANT: keep the port value on the same line as --port (no newline).
VITE_DEMO_MODE=false \
API_PROXY_TARGET=http://127.0.0.1:8000 \
npm run dev -- --host 127.0.0.1 --port 5173
```

Open `http://127.0.0.1:5173`.

To expose the Tau-node-backed zUSD wallet transport surface through the same
API server, enable the wallet bridge and point it at a local Tau node:

```bash
ZUSD_TAU_WALLET_API_ENABLED=true \
ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING=true \
ZUSD_TAU_WALLET_CHAIN_ID=tau-local \
ZUSD_TAU_WALLET_TAU_HOST=127.0.0.1 \
ZUSD_TAU_WALLET_TAU_PORT=65432 \
DEMO_API_TOKEN=sekret \
python3 -m src.integration.api_server
```

The Tau node can run through the local-node Docker profile:

```bash
docker compose -f docker-compose.yml -f docker-compose.permissionless.yml --profile local-node up -d tau-local
```

If you want to test `mint`, configure the Tau token operator pubkey for the
node environment as well:

```bash
TAU_DEX_TOKEN_OPERATOR_PUBKEY=0x<operator-pubkey>
```

To bind only the Oracle tab to the local ZenoOracle dashboard API:

```bash
# In repo root
tools/zenodex-oracle serve --home /tmp/zenodex-oracle --host 127.0.0.1 --port 8787

# In tools/dex-ui
VITE_ZENO_ORACLE_API_URL=http://127.0.0.1:8787 npm run dev -- --host 127.0.0.1 --port 5173
```

Local Oracle writes are disabled by default. Use `--allow-writes` only for a
local operator/demo console:

```bash
tools/zenodex-oracle serve --home /tmp/zenodex-oracle --host 127.0.0.1 --port 8787 --allow-writes
```

## Environment

- `VITE_DEMO_MODE=true|false`: demo mode uses mock data and does not call the API.
- `VITE_BASE_PATH=/`: optional Vite base path. Use `./` for IPFS / subpath-hosted static builds.
- `API_PROXY_TARGET=http://127.0.0.1:8000`: Vite dev-server proxy target for `/api/*` requests (keeps requests same-origin in the browser).
- `VITE_API_BASE=http://127.0.0.1:8000`: optional base URL for API requests (use for non-proxied setups / production; empty = same-origin).
- `VITE_API_TOKEN=<token>`: optional bearer token. If `DEMO_API_TOKEN` is set on the API server, set `VITE_API_TOKEN` to the same value.
- `VITE_ZENO_ORACLE_API_URL=http://127.0.0.1:8787`: optional ZenoOracle dashboard API base URL. If unset, the Oracle tab tries `http://127.0.0.1:8787` and falls back to static preview data.

## Runtime Config

Static deployments can override frontend behavior without rebuilding by editing:

- `public/zenodex-config.json`

Supported runtime keys:

- `apiBase`
- `demoMode`
- `perpsPreviewWrites`

This is useful for IPFS/static hosting where one bundle may be reused against
different operator APIs.

## IPFS / Static Hosting

For an IPFS-ready bundle with relative asset paths:

```bash
bash ../publish_ui_ipfs.sh
```

Optionally set:

```bash
VITE_API_BASE=https://operator.example bash ../publish_ui_ipfs.sh
```

The publisher also writes:

- `generated/ipfs_ui/release_manifest.json`

so operators can mirror or audit the exact static artifact they are serving.

## Security Notes (Dev API)

`/api/perps/*` and `/api/zusd/*` are demo/development routes. They operate on in-memory state and are not the production transaction path.

The mounted perps preview grid reflects that boundary. In non-demo mode it is
read-only by default, and it only enables local preview writes when one of these
is set:

- query parameter `perpsPreviewWrites=1`
- runtime config key `perpsPreviewWrites`
- env `VITE_PERPS_PREVIEW_WRITES=true`

`/api/zusd/wallet/*` is different. It is a Tau-node-backed transport bridge for
the zUSD stream-9 wallet lane. Keep it behind local or explicitly controlled
auth, and only enable local signing in test environments.

`/api/zusd/monetary/*` and `/api/perps/wallet/*` are also Tau-node-backed local
or testnet transport bridges. Keep them behind local or explicitly controlled
auth, and only enable local signing in test environments.

The API server refuses to start demo routes on non-loopback binds (e.g. `API_HOST=0.0.0.0`) unless `DEMO_API_TOKEN` is set.
