---
title: README
type: note
permalink: autonomous-tau-dex-review/tools/dex-ui/readme
---

# ZenoDEX UI (React + Vite)

Frontend for ZenoDEX: Swap, Pools, Perpetuals, zUSD, Strategy, ZenoOracle,
and a Confidential tab for the TEE / sealed-bid feature surface.

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

The API server refuses to start demo routes on non-loopback binds (e.g. `API_HOST=0.0.0.0`) unless `DEMO_API_TOKEN` is set.
