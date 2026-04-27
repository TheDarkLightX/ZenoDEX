# ZenoDEX UI (React + Vite)

Frontend for ZenoDEX: Swap, Pools, Perpetuals, and a Confidential tab for the TEE / sealed-bid feature surface.

The Confidential tab is not just a status page. It explains:
- who the feature is for,
- why a user would choose it,
- when the normal public path is better,
- which formal checks back the current experiment.
- and, in live mode, the current beta posture from `GET /api/confidential/status`.

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

## Environment

- `VITE_DEMO_MODE=true|false`: demo mode uses mock data and does not call the API.
- `VITE_BASE_PATH=/`: optional Vite base path. Use `./` for IPFS / subpath-hosted static builds.
- `API_PROXY_TARGET=http://127.0.0.1:8000`: Vite dev-server proxy target for `/api/*` requests (keeps requests same-origin in the browser).
- `VITE_API_BASE=http://127.0.0.1:8000`: optional base URL for API requests (use for non-proxied setups / production; empty = same-origin).
- `VITE_API_TOKEN=<token>`: optional bearer token. If `DEMO_API_TOKEN` is set on the API server, set `VITE_API_TOKEN` to the same value.

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
