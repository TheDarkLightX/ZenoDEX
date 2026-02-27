# ZenoDEX UI (React + Vite)

Frontend for ZenoDEX: Swap, Pools, and Perpetuals screens.

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

Then run the UI (recommended: use the Vite dev-server proxy so you do not need CORS):

```bash
# IMPORTANT: keep the port value on the same line as --port (no newline).
VITE_DEMO_MODE=false \
API_PROXY_TARGET=http://127.0.0.1:8000 \
npm run dev -- --host 127.0.0.1 --port 5173
```

Open `http://127.0.0.1:5173`.

## Environment

- `VITE_DEMO_MODE=true|false`: demo mode uses mock data and does not call the API.
- `API_PROXY_TARGET=http://127.0.0.1:8000`: Vite dev-server proxy target for `/api/*` requests (keeps requests same-origin in the browser).
- `VITE_API_BASE=http://127.0.0.1:8000`: optional base URL for API requests (use for non-proxied setups / production; empty = same-origin).
- `VITE_API_TOKEN=<token>`: optional bearer token. If `DEMO_API_TOKEN` is set on the API server, set `VITE_API_TOKEN` to the same value.

## Security Notes (Dev API)

`/api/perps/*` and `/api/zusd/*` are demo/development routes. They operate on in-memory state and are not the production transaction path.

The API server refuses to start demo routes on non-loopback binds (e.g. `API_HOST=0.0.0.0`) unless `DEMO_API_TOKEN` is set.
