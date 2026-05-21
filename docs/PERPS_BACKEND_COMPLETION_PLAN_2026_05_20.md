---
title: PERPS_BACKEND_COMPLETION_PLAN_2026_05_20
type: note
permalink: autonomous-tau-dex-review/docs/perps-backend-completion-plan-2026-05-20
---

# Perps Backend Completion Plan

Date: 2026-05-20

## Current Diagnosis

Perps is partially implemented in the backend.

The production-facing engine is `src/integration/perp_engine.py`. It applies
Tau app-bridge perps operations with signature checks, nonce replay protection,
operator gates, balance debits and credits, clearinghouse market kinds, and
oracle settlement hooks.

The mounted HTTP route `src/integration/perps_api.py` is explicitly a
demo/development API. It uses in-memory state and accepts caller-supplied pubkeys
without cryptographic caller verification. It must stay separate from the live
perps product path.

The live perps wallet API is now mounted in
`src/integration/perps_wallet_api.py` under `/api/perps/wallet/*`. It reads Tau
app-state, builds stream `8` clearinghouse operations, preflights them through
`apply_perp_ops`, optionally signs local Tau transactions for testnet use, and
submits through a Tau node.

The Tau app bridge already routes upstream stream `8` to the perps engine through
`src/integration/tau_testnet_dex_plugin.py`. A focused regression proves that
zUSD TauToken balances can be used as the quote collateral asset for signed
clearinghouse perps collateral deposits:

```bash
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_perps_accepts_zusd_token_as_quote_collateral
```

The backend now also exposes zUSD monetary operations on stream `11` through
`src/integration/zusd_monetary_bridge.py`. That bridge persists account-aware
zUSD monetary state inside the Tau app-state wrapper and binds the existing
single-vault kernel to native collateral balances, transferable zUSD balances,
stability-pool escrow, liquidation, and stability-pool collateral claims.

The zUSD monetary kernel is Liquity-like and SimplexBorrow-aligned, but it is
not exact Liquity V1 or V2 parity. The current liquidation policy moves the full
vault collateral into stability-pool accounting when the vault is below MCR. It
does not yet implement Liquity V2's 5% borrower liquidation penalty with
borrower surplus collateral accounting. The parity status is tracked in
`docs/ZUSD_LIQUITY_PARITY_STATUS_2026_05_20.md`.

A focused regression proves the end-to-end backend path:

```bash
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral
```

This proves collateral-minted zUSD can become transferable zUSD and then be
posted into signed clearinghouse perps collateral.

## What Is Still Missing

The remaining blockers are broader stateful/chaos assurance, production wallet
and key-manager integration, production Oracle evidence selection, proof/ZK
wrapping, and final branch/PR cleanup. Docker browser evidence, typed
settle-time Oracle bridge fixtures, and clearinghouse liquidation UI evidence
exist for the current local/testnet lane.

The mounted non-demo zUSD UI now exposes both the stream `9` TauToken wallet
transport path and the stream `11` monetary-vault path. The monetary path is
served by `src/integration/zusd_monetary_wallet_api.py` under
`/api/zusd/monetary/*` and mounted in
`tools/dex-ui/src/components/ZUSDMonetarySurface.jsx`.

The demo HTTP wrapper `src/integration/zusd_api.py` remains demo/development
only. Product code should use stream `11` through the live monetary wallet API.

Perps now has a live product submission surface equivalent to the zUSD wallet
transport. The mounted `/api/perps/*` route remains the demo route; the live lane
is `/api/perps/wallet/*`.

## Completion Requirements

Perps can be called live only when these are true:

1. Users can obtain zUSD from the collateral-vault path, not only from operator
   token minting. Backend app-bridge evidence now exists.
2. The zUSD vault path updates both monetary state and wallet balances
   atomically enough for replay. Backend app-bridge evidence now exists.
3. The stability pool has account-aware deposits, withdrawals, liquidation
   effects, and collateral claims. Backend app-bridge evidence now exists.
4. Perps deposits debit transferable zUSD balances and credit perps collateral.
   Backend app-bridge evidence now exists.
5. Perps market init, collateral deposit/withdraw, position updates, epoch
   advance, clearing-price publish, and epoch settlement are signed and
   nonce-protected where authority is required. Backend app-bridge, wallet API,
   resilience, and browser evidence now exists for the current two-party
   clearinghouse lane.
6. Oracle settlement fails closed without typed Oracle evidence when
   `TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH=1`.
   Clearinghouse liquidation is exercised through `settle_epoch`; an explicit
   isolated-market partial-liquidation wallet action remains opt-in work if
   isolated markets are promoted.
7. Browser tests and local Tau-node acceptance tests cover the live submission
   path.

## Implementation Plan

### Phase 1: Live zUSD Monetary Bridge

Status: implemented for the Tau app bridge as stream `11`.

The live zUSD monetary transaction lane wraps `src/core/zusd.py` with
wallet/account semantics in `src/integration/zusd_monetary_bridge.py`.

Implemented operations:

- `bootstrap_oracle`
- `deposit_collateral`
- `withdraw_collateral`
- `mint_zusd`
- `repay_zusd`
- `redeem_zusd`
- `deposit_sp`
- `withdraw_sp`
- `liquidate`
- `claim_sp_collateral`

Implemented behavior:

- `mint_zusd` increases vault debt and mints TauToken zUSD to the borrower.
- `repay_zusd` burns or locks borrower zUSD and reduces debt.
- `redeem_zusd` burns redeemer zUSD and releases collateral.
- `deposit_sp` transfers user zUSD into stability-pool accounting.
- `withdraw_sp` returns zUSD from stability-pool accounting to the user.
- `liquidate` consumes stability-pool zUSD debt and moves collateral to the
  stability-pool collateral bucket.
- `claim_sp_collateral` releases account-attributed stability-pool collateral
  gains back to the user.

Current bound: the bridge uses the existing single-vault zUSD kernel, so one
vault owner is active per app-state instance. Stability-pool deposits are
account-aware. Exact Liquity V2 liquidation parity also remains open until the
5% penalty and borrower-surplus claim path are implemented and mounted.

### Phase 1b: Mounted zUSD Monetary Transport

Status: implemented for the mounted local/testnet API and UI.

Implemented endpoints:

- `GET /api/zusd/monetary/status`
- `POST /api/zusd/monetary/prepare`
- `POST /api/zusd/monetary/submit`

The API reads Tau app-state, derives the stream `11` monetary nonce, preflights
the requested operation against the deterministic app-bridge state, optionally
builds a signed Tau transaction for local testing, submits it, and can auto-mine
against a local Tau node.

The non-demo zUSD tab mounts both:

- `ZUSDMonetarySurface` for collateralized zUSD and stability-pool operations;
- `ZUSDTauWalletSurface` for transfer/mint/burn token transport.

### Phase 2: Perps Live Transport

Status: implemented for the current two-party clearinghouse lane.

Implemented endpoints:

- `GET /api/perps/wallet/status`
- `POST /api/perps/wallet/prepare`
- `POST /api/perps/wallet/submit`

Implemented operations:

- inspect Tau app state and perps markets
- prepare signed clearinghouse market init
- submit clearinghouse market init
- deposit zUSD collateral
- withdraw zUSD collateral
- prepare and submit signed position updates
- advance market epoch
- publish clearing price with an oracle signer
- settle epoch with optional or required typed Oracle adapter bridge evidence

The API also accepts a user-supplied `tx_fee_limit`, validates it as a
non-negative integer, carries it into the signed Tau transaction envelope, and
reports whether the sender's current native Tau balance appears to cover that
requested limit. This is a preflight posture check only; exact fee debit
semantics remain a Tau host responsibility until pinned by live Tau evidence.

Remaining live-transport operations:

- explicit isolated-market partial-liquidation action, if that opt-in market
  family is promoted into the mounted wallet. Clearinghouse pair liquidation is
  exercised through `settle_epoch`.

Pinned live-transport evidence:

- `tests/integration/test_zusd_monetary_wallet_ui_docker.py::test_zusd_monetary_wallet_ui_smoke_through_docker_tau_node`
  now runs a local Docker Tau node, mints zUSD through the mounted browser UI,
  initializes a two-party perps clearinghouse market, deposits minted zUSD as
  perps collateral through the mounted browser UI, mines the submitted Tau
  transactions, and verifies the app-state balance and perps collateral deltas.
- `tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge`
  runs the mounted browser UI with settle-time Oracle evidence required,
  builds a local typed O3 aggregate-adapter bridge for the current clearinghouse
  market, submits `settle_epoch`, and verifies the live preflight accepts the
  typed bridge.
- `tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_reports_liquidation_evidence`
  starts from a live clearinghouse market where a price move makes the short
  side under maintenance, submits `settle_epoch` through the mounted browser UI,
  and verifies the rendered liquidation evidence: `liquidated yes`, fee-pool
  growth, and closed positions.

Default to clearinghouse perps. Isolated markets should remain opt-in because
they require a protocol-counterparty balance-sheet design.

### Phase 3: Mounted UI Wire-Up

Status: implemented for the current non-demo live wallet action set.

The perps tab now mounts `PerpLiveWalletSurface` beside the existing read-only
preview. The preview lock remains correct for the demo `/api/perps/*` trading
grid; the live wallet panel targets `/api/perps/wallet/*` and stream `8`.

The UI now exposes:

- open clearinghouse market roles
- signed action status for market init, collateral deposit/withdraw, signed
  position update, epoch advance, clearing-price publish, and settle epoch
- Tau fee-limit input plus native-balance coverage reporting
- Tau submission receipt
- rejection reason for missing signatures, bad nonce, or insufficient zUSD
- first-class local typed Oracle adapter bridge fixture for settle testing, plus
  a JSON bridge field for externally supplied evidence

Still missing from the mounted perps UI:

- production typed Oracle evidence picker/viewer
- richer liquidation history and a dedicated isolated partial-liquidation
  control if isolated markets are promoted
- production wallet/key-manager integration

### Phase 4: Assurance

Required evidence before claiming perps live-product coverage:

- unit and integration tests for the zUSD monetary bridge
- app-bridge tests proving zUSD mint, transfer, stability-pool deposit, perps
  collateral deposit, signed position update, and settlement
- local Docker Tau-node browser smoke for zUSD collateral mint plus follow-on
  zUSD-to-perps deposit through the mounted live perps wallet
- stateful fuzzing over zUSD monetary actions and perps collateral actions
- chaos tests for node restart, duplicate tx, expired deadline, stale Oracle
  evidence, and out-of-order signed operations
- gas/fee compensation checks for keeper paths when exact Tau fee debits are
  pinned; current wallet surfaces provide fee-limit preflight and configurable
  keeper compensation coverage, not host-level fee debit proof
- docs updating the UI surface matrix from preview to live only after the live
  path passes

### Phase 5: Proof and ZK Promotion

The repo already has a state-proof scaffold under `zk/state_proof_risc0` and
proof-verifier tests. The zUSD monetary and perps live path is not yet wrapped
in a ZK proof circuit.

Promotion order:

1. Keep the deterministic app-bridge transition as the source of truth.
2. Define a stable witness schema for stream `11` zUSD monetary transitions and
   stream `8` perps transitions.
3. Add a proof-carrying receipt that binds pre-state hash, operation stream,
   post-state hash, and balance deltas.
4. Wrap that receipt in RISC Zero or another ZK backend after the witness schema
   stops changing.
5. Gate proof acceptance through `src/integration/proof_verifier.py` rather than
   trusting caller-supplied proof metadata.

## Current Evidence

Passed on 2026-05-20:

```bash
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_perps_accepts_zusd_token_as_quote_collateral
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_stability_pool_liquidation_and_claim
pytest -q tests/integration/test_perp_engine_auth_guards.py tests/integration/test_perp_engine_clearinghouse_2p.py tests/integration/test_zusd_tau_wallet_api.py
pytest -q tests/integration/test_zusd_monetary_wallet_api.py
pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py
pytest -q tests/integration/test_zusd_monetary_wallet_ui_docker.py -s
```

Focused combined run:

```bash
pytest -q tests/core/test_zusd.py tests/core/test_zusd_multi.py tests/integration/test_zusd_monetary_wallet_api.py tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_zusd_tau_wallet_api.py tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_accepts_tau_raw_sender_native_balance tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_stability_pool_liquidation_and_claim tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_perps_accepts_zusd_token_as_quote_collateral
```

Result: `42 passed`.

Mounted zUSD monetary checks:

```bash
pytest -q tests/integration/test_zusd_monetary_wallet_api.py tests/integration/test_zusd_tau_wallet_api.py tests/integration/test_api_server_main.py
npm run build
pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py
pytest -q tests/integration/test_zusd_monetary_wallet_ui_docker.py -s
pytest -q tests/integration/test_zusd_tau_wallet_ui_docker.py -s
```

Results: API checks `11 passed`; UI build passed; stream `11` fake-bridge
browser smoke `1 passed`; stream `11` Docker Tau-node browser smoke `1 passed`;
stream `9` Docker Tau-node browser smoke `1 passed`.

This is enough to prove the backend app bridge can mint collateralized zUSD,
transfer it, use it as clearinghouse perps collateral, exercise stability-pool
liquidation accounting, and pay configured liquidation compensation to a keeper.
It also proves the mounted zUSD tab can submit a stream `11` monetary mint
through the Tau-node-backed API and observe post-submit state. It is enough for
the current local/testnet zUSD-to-perps browser lane, but it is not enough to
claim full perps product completion because broader stateful/chaos assurance,
production wallet/key-manager integration, production Oracle evidence selection,
and proof/ZK wrapping remain open.

Perps live wallet checks added on 2026-05-20:

```bash
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
cd tools/dex-ui && npm run build
```

Results: wallet API `8 passed`; stream-8 resilience `5 passed`; browser bridge
`2 passed`; UI production build passed.

Additional Tau fee-limit posture check added on 2026-05-21:

```bash
pytest -q tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py tests/integration/test_perps_stream8_resilience.py
cd tools/dex-ui && npm run build
```

Results after the 2026-05-21 liquidation-summary patch: perps
wallet/API/browser/resilience checks `21 passed`; UI production build passed.
The browser bridge asserts `txFeeLimit` query plumbing, rendered fee-limit
output, native-balance coverage for both market-init and oracle-price publish
flows, typed settle Oracle-bridge construction, and clearinghouse liquidation
evidence after `settle_epoch`.

Additional typed Oracle bridge fixture check added on 2026-05-21:

```bash
pytest -q tests/integration/test_perps_wallet_api.py::test_oracle_bridge_template_preflights_required_settle_epoch
pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge -s
```

Results: API fixture and browser settle bridge checks `2 passed`.

These checks prove the mounted perps wallet panel can submit a signed stream `8`
two-party market init and a signed oracle clearing-price publish through the
Tau-node-backed API. They also prove app-bridge stream `8` rejects replayed
nonces, expired signatures, missing required settle Oracle adapter evidence, and
cross-stream partial mutation when a valid zUSD monetary operation is followed
by a bad perps operation. They also prove signed stream `8` position updates
through the Tau app bridge after zUSD collateral deposits. The new bridge
fixture check proves the browser can build an exact typed aggregate-adapter
bridge for the current clearinghouse settle action when Oracle evidence is
required.

Additional stream `8` replay evidence added on 2026-05-21:

```bash
pytest -q tests/integration/test_perps_stream8_resilience.py::test_stream8_rejects_batch_local_nonce_replay_without_first_market_side_effect
```

Result: batch-local nonce replay check `1 passed`. This covers the disaster
state `duplicate_side_effect_after_batch_local_nonce_replay`: if a later op in
one stream `8` transaction reuses signed account nonces, the earlier market init
does not survive the rejected transaction.

Additional clearinghouse liquidation UI evidence added on 2026-05-21:

```bash
pytest -q tests/integration/test_perps_wallet_api.py::test_status_exposes_clearinghouse_liquidation_summary_fields
pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_reports_liquidation_evidence -s
```

Results: API summary and browser liquidation checks `2 passed`.

Additional selected-market balance evidence added on 2026-05-21:

```bash
pytest -q tests/integration/test_perps_wallet_api.py::test_submit_deposit_collateral_uses_sender_bound_account_and_stream_8 tests/integration/test_perps_wallet_api.py::test_status_exposes_clearinghouse_liquidation_summary_fields
pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_reports_liquidation_evidence -s
```

Result: API and browser balance checks `3 passed`. The mounted wallet now
shows the selected market's account-A/account-B quote balances and posted
clearinghouse collateral beside the live transaction result.

Remaining limits:

- no explicit isolated-market partial-liquidation wallet action yet;
- no ZK proof wrapper for stream `8` or `11` transitions yet.
