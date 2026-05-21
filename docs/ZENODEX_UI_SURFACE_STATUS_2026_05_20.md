# ZenoDEX UI Surface Status (2026-05-20)

This note records the mounted ZenoDEX UI posture as of 2026-05-20.

## Mounted surfaces

| Surface | Mounted in UI | Default posture | Authoritative backend path | Browser evidence |
| --- | --- | --- | --- | --- |
| Swap / Pools | Yes | Live local/testnet spot lane | Yes, mounted spot path through local API and Tau-ledger flow | `tests/integration/test_dex_ui_live_bridge.py` |
| zUSD | Yes | Live Tau wallet plus monetary-vault lanes | Yes for stream `9` transfer/mint/burn transport and stream `11` collateral mint, repay, redeem, stability pool, liquidation, and SP collateral claims. | `tests/integration/test_zusd_tau_wallet_ui_bridge.py`, `tests/integration/test_zusd_tau_wallet_ui_docker.py`, `tests/integration/test_zusd_monetary_wallet_ui_bridge.py`, `tests/integration/test_zusd_monetary_wallet_ui_docker.py`, `tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_stability_pool_liquidation_and_claim` |
| Oracle | Yes | Live local operator console | Yes for local read/write API routes, with browser evidence for dashboard reads and a write-enabled receipt flow. | `tests/integration/test_zeno_oracle_ui_bridge.py`, `tests/integration/test_zenodex_oracle_cli.py` |
| Perpetuals | Yes | Read-only preview plus live wallet panel in non-demo mode | Yes for stream `8` two-party clearinghouse init, collateral deposit/withdraw, signed position updates, epoch advance, oracle price publish, and settle through `/api/perps/wallet/*`. The mounted `/api/perps/*` path remains demo/development. | `tests/integration/test_perps_ui_preview_lock.py`, `tests/integration/test_perps_wallet_api.py`, `tests/integration/test_perps_wallet_ui_bridge.py`, `tests/integration/test_perps_stream8_resilience.py` |
| Strategy | Yes | Receipt-backed live-prepare plus gated local/testnet submit panel in non-demo mode | Yes for local AutoTrader prepare and gated local/testnet submit through `/api/strategy/autotrader/*`, including explicit risk acknowledgement, `AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING=true`, `AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION=true`, policy compilation, guard checks, signed intent operations, Tau tx payload construction or externally signed Tau envelope validation, `sendtx`, optional auto-mining, and release certificates. Unattended execution and production chain submission remain non-claims. | `tests/integration/test_autotrader_live_api.py`, `tests/integration/test_autotrader_live_ui_bridge.py` |
| Confidential | Yes | Live operator-status and proof-context surface | Status-only via `GET /api/confidential/status` | `tests/integration/test_confidential_ui_bridge.py` |

## Interpretation

The mounted app is the intended ZenoDEX shell. The open gap is no longer shell
selection.

The next product-complete backend promotions still required are:

1. perps on a mounted live transaction path, using the existing signed app-bridge engine rather than the demo HTTP route;
2. strategy execution beyond the gated local/testnet submit path;
3. any confidential execution lane beyond operator-status and proof posture.

Perps now has focused backend and browser evidence for a mounted live wallet
lane. Collateral-minted zUSD can be transferred and used as the quote collateral
asset for signed clearinghouse collateral deposits, and the UI can submit signed
stream `8` market init, oracle price publish, and opt-in isolated partial
liquidation actions through `/api/perps/wallet/*`. Local typed Oracle bridge
fixtures cover both `settle_epoch` and isolated `partial_liquidate` browser
tests. The perps wallet UI now has a verifier-backed Oracle evidence inspector
for pasted or locally built aggregate-adapter bridges, plus a live ZenoOracle
candidate picker/viewer that loads accepted reads, authorizations, and
aggregates from the mounted Oracle service URL. The perps wallet submit path
also accepts externally signed Tau transaction envelopes and validates their
sender, sequence, expiry, fee, operations, and BLS signature before `sendtx`, so
an external signer or key-manager can drive the live stream `8` lane without
enabling local raw-key signing in the API. The completion plan is recorded in
`docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md`. The main blockers are now
production Oracle network authority, full production wallet/key-manager
registry and device UX, and proof/ZK promotion.

The zUSD monetary lane is Liquity-like but does not claim exact Liquity V2
liquidation parity. The current 5% borrower-penalty gap is tracked in
`docs/ZUSD_LIQUITY_PARITY_STATUS_2026_05_20.md`.

The zUSD monetary submit path now accepts externally signed Tau transaction
envelopes for stream `11`. The API validates the signed envelope's sender,
sequence, expiry, fee limit, encoded operations, and BLS signature before
`sendtx`, so collateral, mint, repay, redeem, stability-pool, liquidation, and
SP-claim actions can be driven by an external signer or key-manager without
enabling local raw-key signing in the API.

The AutoTrader local/testnet submit path now accepts an externally signed Tau
transaction envelope for the prepared strategy operation bundle. The API
validates the envelope's sender, current sequence, expiry, fee limit, encoded
operations, and BLS signature before `sendtx`; replaying the same signed
envelope is rejected before a second `sendtx`. This is Tau-envelope transport
evidence for the gated local/testnet Strategy panel, while unattended
production strategy execution and production wallet key management remain
non-claims.

## Current browser checks

Run these from repo root:

```bash
pytest -q \
  tests/integration/test_zusd_tau_wallet_ui_bridge.py \
  tests/integration/test_zusd_tau_wallet_ui_docker.py \
  tests/integration/test_zusd_monetary_wallet_ui_bridge.py \
  tests/integration/test_zusd_monetary_wallet_ui_docker.py \
  tests/integration/test_zeno_oracle_ui_bridge.py \
  tests/integration/test_perps_wallet_ui_bridge.py \
  tests/integration/test_autotrader_live_ui_bridge.py \
  tests/integration/test_perps_ui_preview_lock.py \
  tests/integration/test_confidential_ui_bridge.py
```

These checks prove:

- the mounted Oracle tab can bind to a real local Oracle service and execute a
  write-enabled local receipt flow when the service is started with
  `--allow-writes`;
- the mounted zUSD tab can submit through the Tau wallet bridge, including the local Docker Tau node lane;
- the mounted zUSD tab can submit stream `11` monetary-vault actions through the Tau-node-backed API, including the local Docker Tau node lane;
- the mounted perps tab fails closed to read-only preview by default for the demo trading grid in non-demo mode;
- the mounted perps wallet panel can submit signed stream `8` clearinghouse init
  and oracle price publish actions through the Tau-node-backed API;
- the mounted Strategy tab can prepare receipt-backed AutoTrader operations and
  submit them to a local/testnet Tau RPC when explicit risk acknowledgement,
  local signing, and testnet-submission gates are enabled;
- the mounted confidential tab can load live operator posture from the stdlib API server.

Current backend-only perps bridge check:

```bash
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_perps_accepts_zusd_token_as_quote_collateral
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral
pytest -q tests/integration/test_zusd_monetary_wallet_api.py
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
python3 tools/zenodex_live_cross_stream_stateful.py --format json
```

Current AutoTrader live-prepare checks:

```bash
pytest -q tests/integration/test_autotrader_live_api.py
pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
```

These prove the mounted strategy API requires explicit risk acknowledgement and
local-signing enablement, prepares a signed receipt-backed operation bundle,
can submit the prepared Tau envelope to a local/testnet Tau RPC behind
`AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION=true`, and renders the result in the
Strategy tab. They do not claim unattended production strategy execution,
production wallet key management, or production chain submission.

Latest AutoTrader live-prepare pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
```

Results: `4 passed` and `1 passed`.

Latest AutoTrader local/testnet submit pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
npm run build
```

Results: `9 passed`, `2 passed`, and Vite production build passed. The API
suite includes a Tau app-bridge application check proving the default prepared
AutoTrader signed intent payload applies against the same deterministic fixture
pool that the live-preparation path quotes. It also accepts a valid externally
signed Tau envelope and rejects duplicate signed-envelope replay before a
second `sendtx`. The browser submit smoke calls the mounted Strategy tab, sends
the externally signed prepared Tau transaction to a Tau-compatible local/testnet
RPC, auto-mines, and renders the `sendtx`, block receipts, and
`external_signed_payload` signing mode.

Latest local browser pass on 2026-05-20:

```bash
pytest -q tests/integration/test_zusd_tau_wallet_ui_bridge.py tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_zeno_oracle_ui_bridge.py tests/integration/test_perps_ui_preview_lock.py tests/integration/test_confidential_ui_bridge.py
pytest -q tests/integration/test_dex_ui_live_bridge.py
```

Results: mounted non-spot browser checks `7 passed`; spot/pools browser checks
`2 passed`.

Latest perps live-wallet pass on 2026-05-20:

```bash
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: `4 passed`, `4 passed`, and `1 passed`.

Follow-on perps live-wallet pass on 2026-05-20:

```bash
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: `8 passed`, `5 passed`, and `2 passed`.

Latest external-signed perps browser pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_accepts_external_signed_payload_without_local_signing -s
```

Result: `1 passed`. The mounted perps wallet UI submitted a stream `8`
collateral deposit with local signing disabled, using an externally signed Tau
transaction envelope. The DOM receipt included `signing
external_signed_payload`, fee-limit coverage, and the expected quote/collateral
deltas after auto-mining through the local Tau RPC harness.

Latest external-signed zUSD monetary browser pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_api.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_docker.py -s
```

Results: `10 passed`, `1 passed`, and `1 passed`. The mounted zUSD monetary UI submitted a
stream `11` sequence with local signing disabled, using externally signed Tau
transaction envelopes for collateral deposit, collateral withdrawal, mint,
repay, redemption, stability-pool deposit, stability-pool withdrawal, oracle
report, liquidation, and SP collateral claim. The DOM receipts included
`external_signed_payload`, accepted `sendtx` responses, the expected native
collateral movement, zUSD debt, stability-pool escrow movement, redemption
collateral payout, liquidation debt absorption, and collateral claim settlement
after auto-mining through the local Tau RPC harness. The API regression suite
also rejects sender mismatch, sequence mismatch, operation mismatch, bad
signatures, and preflight failures before broadcast.

The Docker lane now also mints zUSD through the mounted browser UI using an
externally signed stream `11` Tau envelope with local zUSD API signing disabled,
then feeds that minted zUSD into the live perps wallet flow on the same local
Tau node. It resubmits the exact same signed zUSD mint envelope after success
and asserts a `400` rejection with no app-state mutation. In the bounded Docker
seed the duplicate is rejected during deterministic preflight; the API
regression suite separately covers the explicit signed-payload sequence-mismatch
reject path. The same Docker run now submits the follow-on perps collateral
deposit through an externally signed stream `8` Tau envelope, then replays that
exact perps envelope and asserts the sequence-mismatch rejection leaves the app
state unchanged.

Latest perps Oracle evidence inspector pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_oracle_bridge_inspector_summarizes_verified_settle_bridge tests/integration/test_perps_wallet_api.py::test_oracle_bridge_inspector_rejects_tampered_action_id
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge -s
```

Results: `2 passed` and `1 passed`. The API inspector accepts a valid
settle-time aggregate-adapter bridge, rejects an action-ID tamper with
`adapter_action_id_mismatch`, and the mounted UI renders accepted Oracle
evidence fields before submit. The browser check now also starts a local
ZenoOracle service, seeds a canonical perps index authorization, loads the
service dashboard through `VITE_ZENO_ORACLE_API_URL`, and renders the live
candidate counts and selected authorization beside the perps submit flow.

Oracle live-surface note: `tests/integration/test_zeno_oracle_ui_bridge.py`
now proves both the live dashboard read path and a write-enabled local receipt
flow from the mounted Oracle tab. The write smoke creates an identity,
registers and funds a query, registers and bonds a reporter, registers a
source, submits a report, builds aggregate/read/authorization receipts, and
pays rewards against a local `tools/zenodex-oracle serve --allow-writes`
instance.

Latest Oracle write-browser pass on 2026-05-21:

```bash
pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_runs_write_enabled_receipt_flow -s
```

Result: `1 passed`.

Latest cross-stream stateful replay pass on 2026-05-21:

```bash
python3 tools/zenodex_live_cross_stream_stateful.py --format json
pytest -q tests/integration/test_zenodex_live_cross_stream_stateful.py
```

Results: replay tool accepted `6` bounded scenarios plus `4` deterministic fuzz
seeds of `32` steps each; receipt tests `2 passed`. The covered disaster states
are duplicate zUSD replay side effects, cross-stream partial mutation, expired
zUSD deadline materialization, perps overdeposit materialization, missing Oracle
bridge settlement, balance drift after a zUSD-to-perps success path, and
long-horizon balance/nonce/atomicity drift.

## Economic-security status

Algorithmic game theory is required for value-moving actor surfaces before
promotion. The first bounded surfaces should be Oracle reporters/disputes,
perps liquidation and settlement keepers, AutoTrader delegation, proof-mining
rewards, and batch inclusion/routing games.

For each surface, record players, actions, timing, information, payoff, the
profitable-deviation query, bounded assumptions, and a replay lane such as
SMT/Z3, exact integer sweeps, TLA, ESSO/Tau, or Lean. A surface can move from
engineering evidence to an economic-security claim only after the same attack
query is replayed with positive and negative evidence.
