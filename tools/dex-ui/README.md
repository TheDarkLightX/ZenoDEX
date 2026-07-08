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
  and settlement transactions. Local preview writes for the older `/api/perps/*`
  lane require an explicit override and still do not represent authoritative
  settlement.
- Strategy includes a receipt-backed AutoTrader local/testnet panel for
  prepare, gated submit, execute-once, and bounded supervisor flows through
  `/api/strategy/autotrader/*`. It requires explicit risk acknowledgement plus
  local/testnet enablement. The supervisor lane binds a public local/testnet
  supervisor profile, requires an externally signed Tau envelope, and consumes
  an execution key only after successful submit. Unattended production
  execution and production chain submission remain outside the current claim.
- Confidential exposes live operator posture through `GET /api/confidential/status`
  plus bounded local/testnet attestation admission and redacted runtime receipt
  flows through `/api/confidential/attestation/*`. It is not the default swap
  path or a generally enabled execution lane.

The Confidential tab combines operator status with feature context. It explains:
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

The browser smoke `zenodexUiSmokeOracleWrites=1` drives the local
write-enabled Oracle API from the mounted tab and verifies the identity, query,
reporter, source, report, aggregate, accepted-read, authorization, and reward
receipt flow.

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
DEX_API_ENABLED=true ZENODEX_API_BEARER_TOKEN=sekret python3 -m src.integration.api_server
```

Then run the UI. The Vite dev-server proxy avoids local CORS setup. If a
`zenoctl testnet local up` stack is running, the dev server auto-detects its
loopback nginx port and uses that as the `/api/*` proxy target:

```bash
# IMPORTANT: keep the port value on the same line as --port (no newline).
VITE_DEMO_MODE=false \
npm run dev -- --host 127.0.0.1 --port 5173
```

Open `http://127.0.0.1:5173`.

For a manually started API server, set `API_PROXY_TARGET` explicitly:

```bash
VITE_DEMO_MODE=false \
API_PROXY_TARGET=http://127.0.0.1:8000 \
npm run dev -- --host 127.0.0.1 --port 5173
```

To expose the Tau-node-backed zUSD wallet transport surface through the same
API server, enable the wallet bridge and point it at a local Tau node:

```bash
ZUSD_TAU_WALLET_API_ENABLED=true \
ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING=true \
ZUSD_TAU_WALLET_CHAIN_ID=tau-local \
ZUSD_TAU_WALLET_TAU_HOST=127.0.0.1 \
ZUSD_TAU_WALLET_TAU_PORT=65432 \
ZENODEX_API_BEARER_TOKEN=sekret \
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

For a static bundle, set the same Oracle API base at runtime in
`public/zenodex-config.json` or the deployed `zenodex-config.json`:

```json
{
  "zenoOracleApiBase": "http://127.0.0.1:8787"
}
```

Local Oracle writes are disabled by default. Use `--allow-writes` only for a
local operator/demo console:

```bash
tools/zenodex-oracle serve --home /tmp/zenodex-oracle --host 127.0.0.1 --port 8787 --allow-writes
```

## Environment

- `VITE_DEMO_MODE=true|false`: demo mode uses mock data and does not call the API.
- `VITE_BASE_PATH=/`: optional Vite base path. Use `./` for IPFS / subpath-hosted static builds.
- `API_PROXY_TARGET=http://127.0.0.1:8000`: Vite dev-server proxy target for `/api/*` requests (keeps requests same-origin in the browser). If unset, the dev server discovers a running `zenoctl testnet local up` nginx container first, then falls back to `http://127.0.0.1:8000`.
- `VITE_API_BASE=http://127.0.0.1:8000`: optional base URL for API requests (use for non-proxied setups / production; empty = same-origin).
- `VITE_API_TOKEN=<token>`: optional bearer token. If `ZENODEX_API_BEARER_TOKEN` is set on the API server, set `VITE_API_TOKEN` to the same value.
- `VITE_ZENO_ORACLE_API_URL=http://127.0.0.1:8787`: optional ZenoOracle dashboard API base URL. If unset, the Oracle tab tries `http://127.0.0.1:8787` and falls back to static preview data.

## Runtime Config

Static deployments can override frontend behavior without rebuilding by editing:

- `public/zenodex-config.json`

Supported runtime keys:

- `apiBase`
- `allowDemoMode`
- `allowBrowserKeyGeneration`
- `allowDefaultExternalSigner`
- `demoMode`
- `devMode`
- `defaultExternalSigner`
- `perpsPreviewWrites`
- `runtimeDiagnostics`
- `zenoOracleApiBase`

This is useful for IPFS/static hosting where one bundle may be reused against
different operator APIs.

The checked-in `public/zenodex-config.json` is currently a temporary
`local-testnet` testing config with browser key generation enabled. It exists so
the GUI can be exercised before the standalone `Keys` app is available. Do not
copy that file into public-testnet or production deployments.

`runtimeDiagnostics` and `devMode` are operator-facing controls for diagnostics
such as chain, proof posture, signer, and receipt-boundary status. They default
off so the polished UI does not expose developer/debug text. A local reviewer
can also use `?zenodexDiagnostics=1` for one session.

`allowBrowserKeyGeneration` is an explicit last-resort browser fallback and is
honored only for an explicit local/dev deployment. The normal path is an
external signer profile. A `defaultExternalSigner` must contain only public
wallet metadata plus a verified local-signer public receipt, or a `connectUrl`
that returns one. Signing URLs are accepted only when they are same-origin paths
or loopback `http://127.0.0.1` / `localhost` URLs.

Supported `signerSecurityProfile` values:

- `native-desktop-loopback-signer-v0`

Hardware wallet, TEE, and threshold signer profiles require their own receipt
schemas and validators before they can be listed in a deployable profile.

Create and serve a browser-independent native desktop signer:

```bash
python3 tools/zenodex_local_signer.py create \
  --vault ~/.zenodex/local-signer-v0.json \
  --key-id local-testnet-ui \
  --chain-id zeno-ledger-localtest-v0

python3 tools/zenodex_local_signer.py serve \
  --vault ~/.zenodex/local-signer-v0.json \
  --chain-id zeno-ledger-localtest-v0 \
  --host 127.0.0.1 \
  --port 8799 \
  --cors-origin http://127.0.0.1:5173
```

The `create` and `receipt` commands print the public receipt used by runtime
config. The bridge keeps the private key inside the local signer process and
only serves `/public-receipt`, `/sign-dex-intent`, and
`/sign-tau-transaction-payload` over loopback. Signing requests default to
terminal approval. The signer prints a request hash plus the relevant sender,
deadline, nonce, asset, amount, fee, and operation fields; type `approve` only
after checking the request. The browser-facing bridge also requires an allowed
`Origin` and a per-session pairing token returned by `/public-receipt`; the UI
keeps that token in memory and sends it only as `X-ZenoDEX-Signer-Token` on
signing requests. For hosted testnet or production UI origins, pass the exact
site origin with `--cors-origin`. Unattended signing requires the explicit
`--approval-mode unattended --i-understand-unattended-signing` flags and is
intended for controlled automation, not normal production use.

Example local-testnet external signer config:

```json
{
  "deployment": "local-testnet",
  "allowDefaultExternalSigner": true,
  "defaultExternalSigner": {
    "schema": "zenodex/dex-ui/runtime-default-external-signer/v0",
    "signerSecurityProfile": "native-desktop-loopback-signer-v0",
    "address": "0x<bls-public-key>",
    "chainId": "zeno-ledger-localtest-v0",
    "signerProvider": "zenodex-local-signer-v0",
    "connectUrl": "http://127.0.0.1:8799/public-receipt",
    "signTauTransactionPayloadUrl": "http://127.0.0.1:8799/sign-tau-transaction-payload",
    "signDexIntentForEngineUrl": "http://127.0.0.1:8799/sign-dex-intent"
  }
}
```

Production uses the same contract. The difference is that production must set
`allowDefaultExternalSigner` explicitly and must use a signer receipt that
attests prompt user approval:

```json
{
  "deployment": "production",
  "allowBrowserKeyGeneration": false,
  "allowDefaultExternalSigner": true,
  "defaultExternalSigner": {
    "schema": "zenodex/dex-ui/runtime-default-external-signer/v0",
    "signerSecurityProfile": "native-desktop-loopback-signer-v0",
    "connectUrl": "http://127.0.0.1:8799/public-receipt",
    "signTauTransactionPayloadUrl": "http://127.0.0.1:8799/sign-tau-transaction-payload",
    "signDexIntentForEngineUrl": "http://127.0.0.1:8799/sign-dex-intent"
  }
}
```

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

Legacy in-memory `/api/perps/*` and `/api/zusd/*` demo routes are no longer mounted by the stdlib API. Wallet and monetary paths use Tau-node-backed transport bridges.

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

The API server refuses to start sensitive routes without either `ZENODEX_API_BEARER_TOKEN` or an explicitly declared external auth boundary.
