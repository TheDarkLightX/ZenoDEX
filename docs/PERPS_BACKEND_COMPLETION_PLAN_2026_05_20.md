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

The remaining blockers are packet-level network partition/latency chaos,
hardware/OS wallet UX and recovery flows behind the public wallet-authority
profile, production Oracle network authority, proof/ZK wrapping, and final
branch/PR cleanup. Docker browser evidence, typed Oracle bridge fixtures,
action-aware local Oracle evidence selection, clearinghouse liquidation UI
evidence, wallet-authority profile preflight, bounded stream `8`
replay/freshness checks, Tau RPC send-failure retry evidence, API-level
node-restart replay evidence, and Docker Tau-node restart plus pause/retry
evidence exist for the current local/testnet lane.

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
   Clearinghouse liquidation is exercised through `settle_epoch`; isolated
   partial liquidation is now available as an opt-in account-bound wallet action
   when `TAU_DEX_ALLOW_ISOLATED_PERPS=1`.
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

Remaining live-transport operation scope:

- clearinghouse pair liquidation is exercised through `settle_epoch`;
- isolated partial liquidation is mounted as an opt-in wallet action with local
  typed Oracle bridge construction and action-aware live Oracle evidence
  picker/viewer evidence.

Pinned live-transport evidence:

- `tests/integration/test_zusd_monetary_wallet_ui_docker.py::test_zusd_monetary_wallet_ui_smoke_through_docker_tau_node`
  now runs a local Docker Tau node, mints zUSD through the mounted browser UI,
  initializes a two-party perps clearinghouse market, deposits minted zUSD as
  perps collateral through the mounted browser UI, mines the submitted Tau
  transactions, and verifies the app-state balance and perps collateral deltas.
- `tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge`
  runs the mounted browser UI with settle-time Oracle evidence required,
  builds a local typed O3 aggregate-adapter bridge for the current clearinghouse
  market, inspects the bridge through the mounted verifier-backed evidence
  panel, loads live candidate reads/authorizations from a local ZenoOracle
  service, submits `settle_epoch`, and verifies the live preflight accepts the
  typed bridge.
- `tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_reports_liquidation_evidence`
  starts from a live clearinghouse market where a price move makes the short
  side under maintenance, submits `settle_epoch` through the mounted browser UI,
  and verifies the rendered liquidation evidence: `liquidated yes`, fee-pool
  growth, and closed positions.
- `tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_accepts_external_signed_payload_without_local_signing`
  runs the mounted browser UI with local signing disabled, passes an externally
  signed Tau transaction envelope into the live wallet panel, submits stream `8`
  collateral, and verifies the rendered `external_signed_payload` signing mode
  plus the post-submit collateral and quote-balance deltas.

The live wallet API now also exposes
`POST /api/perps/wallet/oracle-bridge/inspect`, which verifies a pasted or
locally built aggregate-adapter bridge, returns the verifier result, and
summarizes the bridge ID, action kind, action ID, query ID, profile ID,
evidence floor, value, observed epoch, and report count for the mounted UI.
The mounted UI also loads live ZenoOracle dashboard candidates from
`VITE_ZENO_ORACLE_API_URL` or the runtime `zenoOracleApiBase`, then displays
accepted reads, authorizations, aggregates, selected evidence, and
local-vs-production authority posture beside the stream `8` submit flow.

The live wallet API now emits `perps_stream8_live_wallet_v0` proof-intent
receipts. The receipt binds chain id, stream key, operation hash,
operation-stream hash, pre-submit app hash, optional post-submit app hash, Tau
envelope hash, preflight result, sender, sequence, fee limit, signing mode, and
a public state-delta witness for changed perps markets. This completes the
deterministic receipt/witness step of the proof-promotion plan for stream `8`.
It still requires a real RISC Zero or equivalent wrapper and verifier gate
before becoming a ZK execution claim.

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
- opt-in isolated partial liquidation with explicit bps or `0` auto-sizing
- Tau fee-limit input plus native-balance coverage reporting
- Tau submission receipt
- externally signed Tau transaction envelope submission for perps, so a
  key-manager or external signer can prepare a stream `8` transaction without
  sending raw private-key material to the wallet API
- perps wallet-authority preflight via `PERPS_WALLET_AUTHORITY_PROFILE_JSON` or
  `PERPS_WALLET_AUTHORITY_PROFILE_FILE`, with public key-manager refs, a matching
  signer registry, external signer and device approval controls, stream `8`
  scope, state-delta witness requirements, and an explicit proof/ZK runtime
  profile
- rejection reason for missing signatures, bad nonce, or insufficient zUSD
- first-class local typed Oracle adapter bridge fixtures for settle and opt-in
  isolated partial-liquidation testing, plus a JSON bridge field for externally
  supplied evidence
- action-aware live Oracle candidate picker/viewer for `settle_epoch` and
  `liquidate_account` authorizations from the mounted Oracle service URL
- perps-side Oracle authority preflight via
  `PERPS_ORACLE_AUTHORITY_PROFILE_JSON`, `PERPS_ORACLE_AUTHORITY_PROFILE_FILE`,
  `ZENO_ORACLE_AUTHORITY_PROFILE_JSON`, `ZENO_ORACLE_AUTHORITY_PROFILE_FILE`,
  or `ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE`; the mounted status route
  blocks the production Oracle authority claim unless the profile validates and
  its chain id matches the perps wallet chain

Still missing from the mounted perps UI:

- actual public-testnet production Oracle profile provisioning and live network
  authority evidence behind the local/devnet picker/viewer
- richer liquidation history
- hardware/OS wallet UX, recovery flows, and live signer-device integration
  behind the public wallet-authority profile

### Phase 4: Assurance

Required evidence before claiming perps live-product coverage:

- unit and integration tests for the zUSD monetary bridge
- app-bridge tests proving zUSD mint, transfer, stability-pool deposit, perps
  collateral deposit, signed position update, and settlement
- local Docker Tau-node browser smoke for zUSD collateral mint plus follow-on
  zUSD-to-perps deposit through the mounted live perps wallet
- bounded stateful replay/fuzzing over zUSD monetary actions and perps
  collateral actions
- bounded app-bridge resilience tests for duplicate tx, expired deadline, stale
  Oracle evidence, and out-of-order signed operations; API-level node-restart
  replay and Docker Tau-node restart plus pause/retry evidence now exist;
  packet-level network partition/latency chaos remains open
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
hardware/OS wallet UX and recovery flows, production Oracle network authority,
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

Additional cross-stream stateful replay evidence added on 2026-05-21:

```bash
python3 tools/zenodex_live_cross_stream_stateful.py --format json
pytest -q tests/integration/test_zenodex_live_cross_stream_stateful.py
```

Results: replay tool accepted `6` bounded scenarios plus `4` deterministic fuzz
seeds of `32` steps each; receipt tests `2 passed`. This covers stream `11`
zUSD monetary, stream `9` zUSD token transport, and stream `8` clearinghouse
perps in one deterministic campaign. The named scenario disaster states are
`balance_drift_after_cross_stream_success`, `duplicate_side_effect_after_replay`,
`cross_stream_partial_mutation`, `expired_deadline_materializes`,
`perps_overdeposit_materializes`, and `stale_or_missing_oracle_evidence_settles`.
The fuzz lane adds `long_horizon_balance_drift`,
`long_horizon_cross_stream_partial_mutation`, and
`long_horizon_nonce_replay_materializes`.

Additional isolated partial-liquidation wallet evidence added on 2026-05-21:

```bash
python3 -m py_compile src/core/perps.py src/core/perp_epoch.py src/integration/perps_wallet_api.py src/integration/tau_testnet_dex_plugin.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_oracle_bridge_template_preflights_required_settle_epoch tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_dex_snapshot.py tests/integration/test_perps_stream8_resilience.py
python3 -m pytest -q tests/integration/test_perp_engine_partial_liquidate.py tests/core/test_perp_v2/test_partial_liquidate.py tests/core/test_perp_epoch_default_adapter.py
python3 -m pytest -q tests/core/test_perp_liquidation_eligibility_gate.py tests/kernels/test_perp_liquidation_eligibility_v1_native_adapter.py
npm run build
```

Results: perps wallet API tests `16 passed`; the new mounted browser
partial-liquidation smoke `1 passed`; existing settle-time bridge browser/API
checks `2 passed`; snapshot plus stream-8 resilience checks `18 passed`;
partial-liquidation engine/core checks `48 passed`; liquidation eligibility
checks `10 passed`; the mounted UI production build passed. This covers the
opt-in gate, typed O3 aggregate-adapter bridge generation for
`liquidate_account`, account-bound stream `8` submission, explicit liquidation
fraction, `0` auto-sizing pass-through, and persisted under-maintenance isolated
accounts reaching the liquidation path.

Additional action-aware Oracle evidence picker evidence added on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge tests/integration/test_perps_wallet_api.py::test_oracle_bridge_template_preflights_required_partial_liquidate tests/integration/test_perps_wallet_api.py::test_oracle_bridge_template_preflights_required_settle_epoch -s
cd tools/dex-ui && npm run build
```

Results: partial-liquidation browser `1 passed`; settle plus bridge-template
checks `3 passed`; UI production build passed. The mounted perps wallet now
loads accepted reads, aggregates, and authorizations from a live local
ZenoOracle service URL and prefers the authorization matching the current wallet
action: `settle_epoch` for clearinghouse settlement and `liquidate_account` for
isolated partial liquidation.

Additional production-wallet compatibility evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_api.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_submit_accepts_external_signed_tau_payload_without_local_signing tests/integration/test_perps_wallet_api.py::test_submit_rejects_external_signed_tau_payload_operation_mismatch
npm run build
```

Results: external signed Tau envelope checks `2 passed`; the mounted UI
production build passed. This covers submit-time validation of externally signed
stream `8` envelopes against expected sender, sequence, expiry, fee, operations,
and BLS signature before `sendtx`, without enabling local private-key signing.

Additional perps wallet-authority preflight evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/zeno_ledger_signature.py src/integration/perps_wallet_authority.py src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_missing_profile_is_blocked tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_complete_profile_is_ready tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_blocks_bad_controls_and_chain_mismatch tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_blocks_signer_key_manager_public_key_mismatch tests/integration/test_perps_wallet_api.py::test_status_exposes_clearinghouse_liquidation_summary_fields tests/integration/test_perps_wallet_api.py::test_status_loads_ready_perps_wallet_authority_profile
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_smoke_through_browser -s
```

Results: py_compile passed; focused wallet-authority/API status checks `6
passed`; mounted perps wallet browser smoke `1 passed`.

This is a public profile and readiness-gate check. It does not custody keys,
prove hardware wallet approval, prove perps ZK execution, or claim production
Oracle truth.

Additional perps Oracle-authority binding evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_status_exposes_clearinghouse_liquidation_summary_fields tests/integration/test_perps_wallet_api.py::test_status_loads_ready_oracle_authority_profile tests/integration/test_perps_wallet_api.py::test_status_blocks_oracle_authority_profile_chain_mismatch
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: py_compile passed; focused Oracle-authority status checks `3 passed`;
mounted settle/browser smoke `1 passed`; full mounted perps wallet browser bridge
suite `6 passed`. The perps wallet status now exposes `oracle_authority` and
`production_oracle_authority`, rejects a chain-mismatched Oracle profile, and the
mounted perps UI renders `oracle authority ready` plus the active signer
threshold next to the Oracle evidence picker.

Additional isolated partial-liquidation Oracle-authority evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: py_compile passed; mounted partial-liquidation browser smoke `1
passed`; full mounted perps wallet browser bridge suite `7 passed`. The
isolated partial-liquidation flow now provisions a production-shaped Oracle
authority profile with a matching chain id and active 2-of-2 signer registry
before loading the local ZenoOracle picker. The mounted UI renders `oracle
authority ready` and `oracle signers 2/2` for the `liquidate_account` path while
still reporting the evidence service network as local.

Additional stream `8` stateful resilience evidence added on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_stream8_resilience.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py tests/integration/test_perps_stream8_resilience.py tests/integration/test_zenodex_live_cross_stream_stateful.py
python3 tools/zenodex_live_cross_stream_stateful.py --format json
```

Results: py_compile passed; adjacent perps wallet, stream `8` resilience, and
cross-stream stateful tests `37 passed`; the replay tool accepted `8` bounded
scenarios plus `4` deterministic fuzz seeds of `32` steps each. The new stream
`8` regressions cover two additional disaster states:
`out_of_order_signed_position_nonce_materializes`, where a skipped account nonce
must reject without changing the app state, and
`stale_oracle_adapter_bridge_settles`, where a stale aggregate-adapter bridge
must reject before `settle_epoch` mutates the market.

Additional perps wallet Tau RPC send-failure retry evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_api.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_submit_external_signed_payload_can_retry_after_tau_send_failure_without_state_drift
```

Results: py_compile passed; focused failure/retry regression `1 passed`. This
covers `tau_rpc_send_failure_state_drift`: an externally signed stream `8`
submit that hits a transient Tau RPC send failure returns `502`, leaves app
state unchanged, does not record a queued transaction, and accepts the same
signed payload after the node recovers while the account sequence is unchanged.
Live Docker process restart and pause/retry evidence are covered separately
below. Packet-level network partition/latency chaos remains open.

Additional perps wallet node-restart replay evidence added on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_api.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_submit_external_signed_payload_replay_after_node_restart_rejected_before_sendtx
python3 -m pytest -q tests/integration/test_perps_wallet_api.py tests/integration/test_perps_stream8_resilience.py
```

Results: py_compile passed; focused restart replay regression `1 passed`; perps
wallet plus stream `8` resilience checks `37 passed`. This covers
`restart_replay_materializes`: after a successful externally signed stream `8`
submit, a restarted Tau client with persisted app state and the advanced sender
sequence rejects the old signed payload with `signed_tau_tx_payload sequence
mismatch` before a second `sendtx`. Live Docker process restart is covered
separately below; packet-level network partition/latency chaos remains open.

Additional Docker Tau-node restart and pause/retry evidence added on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zusd_monetary_wallet_ui_docker.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_docker.py -s
```

Results: py_compile passed; Docker Tau-node browser/restart/pause test `1
passed`. The test starts the local Docker Tau node, mints zUSD through the
mounted browser UI with an externally signed stream `11` envelope, prepares a
signed perps stream `8` collateral deposit, pauses `tau-local`, verifies the
paused-node submit returns `502` with `tau_rpc_error` and no app-state drift,
unpauses the node, submits that same signed perps envelope through the mounted
browser UI, restarts `tau-local`, verifies the post-deposit app state survives
restart, and proves the same signed stream `8` payload is rejected after restart
before state mutation. Packet-level network partition/latency chaos remains
open.

Additional Tau transaction canonicalization and RPC redaction evidence added on
2026-05-21:

```bash
python3 -m py_compile src/integration/tau_net_client.py tests/integration/test_tau_net_client.py
python3 -m pytest -q tests/integration/test_tau_net_client.py -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_api.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_api.py -s
```

Results: py_compile passed; Tau client checks `6 passed`; zUSD monetary wallet
API checks `10 passed`; perps wallet API checks `29 passed`. Tau transaction
signing and nested operation wire encoding now use the canonical JSON encoder,
rejecting noncanonical operation values before signing. Tau RPC connect, send,
receive-reset, and receive-timeout failures are converted to `TauNetRpcError`,
and the socket regressions assert error details do not echo private command text
or partial response bytes. This keeps the mounted stream `8` and stream `11`
submit APIs on the existing `502 tau_rpc_error` fail-closed path when Tau is
unreachable, slow, or resets the connection.

Additional Tau RPC packet-framing chaos evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/tau_net_client.py tests/integration/test_tau_net_client.py tests/chaos/test_tau_net_client_chaos.py
python3 -m pytest -q tests/integration/test_tau_net_client.py -s
python3 -m pytest -q tests/chaos/test_tau_net_client_chaos.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_fails_closed_on_partial_tau_send_timeout -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_fails_closed_on_partial_tau_send_timeout -s
```

Results: py_compile passed; Tau client checks `6 passed`; Tau client chaos `7
passed, 2 skipped`; mounted perps and zUSD partial-response browser regressions
each `1 passed`. `TauNetTcpClient.rpc()` now treats a peer close before the
newline response terminator as a truncated frame and raises `TauNetRpcError`
without including the command text or partial response bytes. This closes the
client-level half-close/truncated-frame gap underneath the mounted stream `8`
and stream `11` submit paths. Broader browser/Toxiproxy packet-loss, jitter, and
multi-surface network chaos campaigns remain open.

Additional multi-surface Tau network-chaos evidence added on 2026-05-21:

```bash
python3 -m py_compile tests/chaos/test_live_surface_tau_network_chaos.py tests/chaos/test_tau_net_client_chaos.py src/integration/tau_net_client.py
python3 -m pytest -q tests/chaos/test_live_surface_tau_network_chaos.py tests/chaos/test_tau_net_client_chaos.py -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_api.py tests/integration/test_perps_wallet_api.py -s
```

Results: py_compile passed; combined Tau client plus live-surface chaos `8
passed, 2 skipped`; adjacent zUSD/perps wallet API suites `39 passed`. The new
campaign drives both stream `11` zUSD monetary submit and stream `8` perps
wallet submit through externally signed Tau payloads. It injects packet loss
before commit on the zUSD path and jitter/timeout before response on the perps
path, then asserts both APIs return `502 tau_rpc_error`, record no accepted Tau
transaction, leave app state unchanged, and do not expose operation, sender, or
signature material in the error detail.

Additional mounted zUSD Tau RPC partial-response chaos evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zusd_monetary_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_fails_closed_on_partial_tau_send_timeout -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py -s
```

Results: py_compile passed; focused browser chaos regression `1 passed`; full
zUSD monetary browser bridge `2 passed`. The mounted stream `11` test uses a
Tau-compatible TCP server that supports normal status and prepare calls, then
sends partial private response bytes on `sendtx` and stalls past the configured
Tau RPC timeout. The live API returns `502 tau_rpc_error`, the mounted UI renders
that fail-closed error without exposing the partial response, the app state is
unchanged, no pending Tau transaction is recorded, and the sender sequence stays
at its pre-submit value. Broader browser/Toxiproxy packet-loss, jitter, and
multi-surface network chaos campaigns remain open.

Additional mounted perps Tau RPC partial-response chaos evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_fails_closed_on_partial_tau_send_timeout -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: py_compile passed; focused stream `8` browser chaos regression `1
passed`; full perps wallet browser bridge `7 passed`. The mounted stream `8`
test uses a Tau-compatible TCP server that supports normal status and preflight
calls, then sends partial private response bytes on `sendtx` and stalls past the
configured Tau RPC timeout. The live API returns `502 tau_rpc_error`, the mounted
UI renders that fail-closed error without exposing the partial response, the app
state is unchanged, no pending Tau transaction is recorded, and the sender
sequence stays at its pre-submit value. Mounted stream `8` and stream `11` now
both have partial-response timeout coverage at the submit boundary. Broader
browser/Toxiproxy packet-loss, jitter, and multi-surface network-chaos campaigns
remain open.

Remaining limits:

- isolated partial liquidation is opt-in; its evidence picker is local/devnet
  mounted evidence until a public-testnet Oracle authority profile is provisioned
  and exercised live;
- the perps wallet has external signed-envelope submit support and a public
  wallet-authority profile preflight, but hardware/OS keychain UX, signer-device
  approval, and recovery flows remain outside the mounted DEX UI;
- no ZK proof wrapper for stream `8` or `11` transitions yet.
