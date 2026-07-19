# ZenoDEX UI

Production-facing React/Vite frontend for the live ZenoDEX surfaces:

- spot swaps;
- liquidity pools;
- ZDEX statistics;
- perpetuals;
- zUSD vault and token-wallet status;
- read-only ZenoOracle status.

The production artifact is deliberately narrow. Fixture-backed product
workbenches, query-triggered writes, bundled market snapshots, token
placeholders, faucets, and browser key generation are not compiled into it.

## Commands

```bash
npm ci
npm run lint
npm run test:config
npm run test:contract
npm run test:sdk
npm run build
```

`npm run build` runs Vite and then scans the emitted JavaScript, CSS, HTML, and
runtime configuration. The build fails if forbidden test functionality or
browser/raw-key signing paths are present.

For development against a real API:

```bash
npm run dev -- --host 127.0.0.1
```

## Runtime configuration

The server supplies `/zenodex-config.json` before the application starts. The
checked-in file is a fail-closed production template. A deployment must provide
a non-empty approved `chainId`.

Supported production fields include:

- `deployment`;
- `chainId`;
- `apiBase`;
- `zenoOracleApiBase`;
- `allowDefaultExternalSigner`;
- `defaultExternalSigner`;
- `uiSurfaceContractSchema`;
- `uiSurfaceContractVersion`;
- `uiSurfaceContractHash`.

`apiBase` and `zenoOracleApiBase` are mandatory authority declarations in a
production runtime config. An explicitly empty value selects same-origin;
omitting the Oracle field does not fall back to a browser-local service.

The production configuration has no mode switch for alternate data, browser
key generation, or query automation.

## Authority boundaries

### Spot and liquidity

Pools, assets, reserves, balances, nonces, LP positions, and fees come from the
live pool API. Feed failure produces an empty unavailable state. Swap and
liquidity writes require a connected external signer callback and an explicit
chain ID.

### Perpetuals

Market and account state comes from the Tau-node-backed wallet status endpoint.
Writes are locked unless the connected wallet exposes the production signer
bridge. The browser never receives or forwards private key material.

### zUSD

The routed monetary and token-wallet views read live status and can prepare
unsigned public requests. Submit controls are excluded until the APIs accept a
verified envelope from an external signer without browser or server raw-key
custody.

### ZenoOracle

The Oracle tab polls `/api/oracle/dashboard` and displays only rows returned by
that endpoint. It does not synthesize, authorize, or submit reports.

## External signer contract

Wallet connection looks for an injected signer bridge (`zenodexSecureSigner`,
`zenodexSigner`, or the compatibility `zenodexLocalSigner` name) or an explicitly
approved runtime signer endpoint. The bridge must return a public receipt with
no secret fields and expose signing callbacks separately. Strict deployments
require user approval and authenticated bridge pairing evidence.

If no valid signer is available, connection and all value-moving controls fail
closed.

## Production UI contract

`audit/production-surface-contract.json` pins required live-source markers and
forbidden source markers. It is promotion evidence, not runtime content, and is
therefore kept outside `public/` so Vite cannot copy the audit vocabulary into
the shipped artifact. `scripts/check-ui-contract.mjs` validates the source
contract, while `scripts/check-production-bundle.mjs` validates every emitted
text artifact. Both must pass in the same revision as the shipped bundle.
The production startup validator also requires the runtime config to bind the
contract's schema, version, and canonical SHA-256 hash.
