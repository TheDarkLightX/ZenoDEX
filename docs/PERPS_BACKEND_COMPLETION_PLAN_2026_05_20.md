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
profile, public-testnet live exercise of signed production Oracle authority,
proof/ZK wrapping, and final branch/PR cleanup. Docker browser evidence, typed
Oracle bridge fixtures, action-aware local Oracle evidence selection,
clearinghouse liquidation UI evidence, wallet-authority profile preflight,
signed Oracle authority profile preflight, bounded stream `8` replay/freshness
checks, Tau RPC send-failure retry evidence, API-level node-restart replay
evidence, and Docker Tau-node restart plus pause/retry evidence exist for the
current local/testnet lane.

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
The backend-only
`POST /api/perps/wallet/oracle-authorization-request` endpoint derives the
exact `settle_epoch` runtime facts from the current two-party clearinghouse
state when typed authorization is enabled and a canonical receipt-graph root
is configured. The backend-only ZenoOracle
`POST /api/oracle/authorization/build-exact` route accepts that exact owned
runtime object only when the selected accepted read and expected graph root
match. Rejections write no authorization receipt or log row. The legacy local
research route remains separate for existing dashboard and testnet callers.
Both exact endpoints report
`production_authority: false`; verifier-selected root lifecycle and deployed
Oracle authority remain release blockers. The binding scope is the exact
market-local runtime action. The application-state diagnostic hash and request
hash are not authorization fields. Any future settlement dependency outside
that market projection requires an explicit application-state binding and a
noninterference review. The authorization builder also does not synthesize the
required economic-security envelope, so its current output remains
research-only and is not directly admissible by the critical perps engine. A
mounted producer must also derive the adapter bridge and authorization graph
from the same accepted aggregate occurrence; independently generated local
fixtures now reject at composition.
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
  signer registry, external signer and device approval controls, recovery
  policies for active signer keys, stream `8` scope, state-delta witness
  requirements, and an explicit proof/ZK runtime profile
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
  blocks the production Oracle authority claim unless the profile validates, its
  chain id matches the perps wallet chain, and signer-registry BLS envelopes form
  a quorum over the authority profile hash

Still missing from the mounted perps UI:

- actual public-testnet exercise of the signed production Oracle authority
  profile behind the local/devnet picker/viewer
- richer liquidation history
- hardware/OS wallet UX and live signer-device integration behind the public
  wallet-authority profile

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

Additional perps wallet recovery-profile evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_authority.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_complete_profile_is_ready tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_blocks_bad_controls_and_chain_mismatch tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_blocks_signer_key_manager_public_key_mismatch tests/integration/test_perps_wallet_api.py::test_perps_wallet_authority_blocks_active_signer_without_recovery_policy tests/integration/test_perps_wallet_api.py::test_status_loads_ready_perps_wallet_authority_profile -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_smoke_through_browser -s
python3 -m pytest -q tests/integration/test_perps_wallet_api.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
cd tools/dex-ui && npm run build
```

Results: focused wallet recovery/API checks `5 passed`; mounted wallet browser
smoke `1 passed`; full perps wallet API `30 passed`; full mounted perps wallet
browser bridge `7 passed`; Vite production build passed. A ready public
wallet-authority profile now requires `wallet_ux.recovery_policy_required=true`
and a valid social-recovery policy for every active signer key. The mounted UI
renders `wallet recovery 2/2` beside the stream `8` submit result. This reduces
the mounted recovery-posture gap, while hardware/OS signer approval and actual
key recovery execution remain outside the current UI.

Additional signer-device integration evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_authority.py src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_perps_wallet_signer_device_integration_ready_receipt tests/integration/test_perps_wallet_api.py::test_perps_wallet_signer_device_integration_blocks_missing_user_presence tests/integration/test_perps_wallet_api.py::test_status_loads_ready_perps_wallet_signer_device_integration tests/integration/test_perps_wallet_api.py::test_signer_device_evaluate_endpoint_blocks_missing_user_presence tests/integration/test_perps_wallet_api.py::test_signer_device_evaluate_endpoint_blocks_missing_provider
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_smoke_through_browser -s
```

Results: the mounted perps wallet can now load a separate signer-device
integration report through `PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON|FILE`
and `POST /api/perps/wallet/signer-device/evaluate`. That report binds a public
backend descriptor, runtime environment evidence, environment policy, device
label, and approval reference into a deterministic status hash, then exposes
backend kind plus environment posture in the UI. This is stronger than the
synthetic device-approval exercise alone, but it still does not prove live OS
prompt capture, hardware custody, or hardware-wallet execution.

Additional perps wallet recovery-exercise evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_authority.py src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_perps_wallet_recovery_exercise_ready_receipt tests/integration/test_perps_wallet_api.py::test_perps_wallet_recovery_exercise_blocks_early_request tests/integration/test_perps_wallet_api.py::test_status_loads_ready_perps_wallet_recovery_exercise tests/integration/test_perps_wallet_api.py::test_recovery_evaluate_endpoint_blocks_threshold_gap
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_smoke_through_browser -s
python3 -m pytest -q tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py -s
python3 tools/check_dex_live_product_goal.py --json
python3 tools/check_public_claim_scope.py --json
cd tools/dex-ui && npm run build
```

Results: focused recovery-exercise checks `4 passed`; mounted perps wallet
browser smoke `1 passed`; affected perps wallet API plus browser bridge suites
`50 passed`; live-product goal audit returned `ok: true`, `goal_complete:
false`, and `local_testnet_evidence_present_with_open_production_limits`;
public claim-scope audit returned `ok: true`; Vite production build passed. The
live wallet authority status can now evaluate a
concrete public recovery exercise through
`PERPS_WALLET_RECOVERY_EXERCISE_JSON` or
`PERPS_WALLET_RECOVERY_EXERCISE_FILE`, and the mounted API exposes
`POST /api/perps/wallet/recovery/evaluate`. The receipt binds authority id,
chain id, subject key, recovery policy, request epoch, current epoch, guardian
approval ids, the underlying social-recovery evaluation hash, and a status hash.
The mounted UI renders `recovery exercise ready` and a recovery receipt hash
when that exercise is present. This is a public threshold/delay evaluation
receipt, and it now verifies a guardian BLS signature quorum over the recovery
exercise hash. It does not prove custody hardware keys or broadcast a
key-rotation transaction.

Additional perps wallet rotation-broadcast exercise evidence added on
2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_authority.py src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py tools/check_dex_live_product_goal.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_perps_wallet_rotation_exercise_ready_receipt tests/integration/test_perps_wallet_api.py::test_perps_wallet_rotation_exercise_blocks_missing_rotation_transition tests/integration/test_perps_wallet_api.py::test_status_loads_ready_perps_wallet_rotation_exercise tests/integration/test_perps_wallet_api.py::test_rotation_evaluate_endpoint_blocks_bad_broadcast_epoch
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_smoke_through_browser -s
python3 tools/check_dex_live_product_goal.py --json
```

Results: focused rotation-exercise checks `4 passed`; mounted perps wallet
browser smoke `1 passed`; and the live-product goal audit still returned
`goal_complete: false`. The live wallet authority status can now evaluate a
public rotation-broadcast exercise through
`PERPS_WALLET_ROTATION_EXERCISE_JSON` or
`PERPS_WALLET_ROTATION_EXERCISE_FILE`, and the mounted API exposes
`POST /api/perps/wallet/rotation/evaluate`. The receipt binds the current
authority profile, a next public wallet-authority profile, the rotated key id,
the replacement key id, request and broadcast epochs, a broadcast reference,
and current-to-next authority hashes. The mounted UI renders `rotation
exercise ready` and a rotation receipt hash when that exercise is present. This
is public transition evidence for a rotation-broadcast exercise, and it now
verifies a guardian BLS signature quorum over the rotation exercise hash. It
does not verify live device prompts or chain finality.

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

Additional signed Oracle authority quorum evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/zeno_oracle_authority.py tools/zenodex_oracle.py tests/integration/test_zeno_oracle_authority.py tests/integration/test_zeno_oracle_ui_bridge.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_zeno_oracle_authority.py tests/integration/test_perps_wallet_api.py::test_status_loads_ready_oracle_authority_profile tests/integration/test_perps_wallet_api.py::test_status_blocks_oracle_authority_profile_chain_mismatch -s
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_api.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
cd tools/dex-ui && npm run build
```

Results: py_compile passed; focused signed Oracle authority/API checks `12
passed`; full Oracle browser suite `5 passed`; full perps wallet API suite `30
passed`; full mounted perps wallet browser bridge `7 passed`; UI production
build passed. Production Oracle authority now fails closed unless
`signature_envelopes` verify as a signer-registry BLS quorum over the
`authority_hash`. The Oracle Governance UI renders `Signed quorum 2/2`, and the
perps live wallet UI renders `oracle signed quorum 2/2` for settle and
partial-liquidation Oracle authority paths.

Additional bounded Oracle authority-exercise evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/zeno_oracle_authority.py tools/zenodex_oracle.py tests/integration/test_zeno_oracle_authority.py tests/integration/test_zeno_oracle_ui_bridge.py
python3 -m pytest -q tests/integration/test_zeno_oracle_authority.py::test_oracle_authority_local_exercise_is_ready tests/integration/test_zeno_oracle_authority.py::test_oracle_authority_public_testnet_exercise_requires_broadcast_refs tests/integration/test_zeno_oracle_authority.py::test_oracle_authority_exercise_endpoint_reports_ready_local_exercise
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_runs_authority_exercise_flow -s
```

Results: the local Oracle service now exposes
`POST /api/oracle/authority/exercise/evaluate`, and the mounted Governance view
can run an authority exercise that reuses a real local operator flow and binds
the resulting query/report/aggregate/read/authorization/reward receipt ids into
a deterministic exercise receipt. Local or testnet exercise can become ready
when the signed authority profile is ready and the receipt ids are present.
Public-testnet exercise still stays blocked unless the request also carries
concrete `public_broadcast_reference` and `public_settlement_reference`
evidence.

Additional Oracle authority exercise binding evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/zeno_oracle_authority.py tests/integration/test_zeno_oracle_authority.py tests/integration/test_zeno_oracle_ui_bridge.py tools/check_dex_live_product_goal.py
python3 -m pytest -q tests/integration/test_zeno_oracle_authority.py
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_runs_authority_exercise_flow -s
python3 tools/check_dex_live_product_goal.py --json
```

Results: the authority exercise status now carries a deterministic
`receipt_binding_hash` over the operator-flow receipt ids, and when public
references are present it also carries a `public_testnet_evidence_binding_hash`
over the broadcast and settlement references. The mounted Governance view now
renders both hashes. This narrows the exercise claim to one concrete local or
testnet receipt bundle and, when present, one concrete public-reference bundle.
It still does not prove that a real public-testnet broadcast happened unless
those references are backed by genuine external evidence.

Additional ZenoOracle mounted malformed-dashboard resilience evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zeno_oracle_ui_bridge.py
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_fails_closed_on_malformed_dashboard_response -s
```

Results: py_compile passed; focused mounted Oracle browser resilience regression
`1 passed`. The test points the mounted ZenoOracle UI at a reachable local
Oracle-like server whose health endpoint succeeds but whose dashboard endpoint
returns malformed JSON. The browser renders `Local API offline`, does not render
`Production authority ready`, and does not report an accepted write-smoke flow.
This covers malformed reachable dashboard data separately from the existing
unreachable-service and read-only/write-enabled service cases.

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

Additional mounted stream `8`/`11` Tau send-drop browser chaos evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_fails_closed_on_tau_send_drop_before_response -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_fails_closed_on_tau_send_drop_before_response -s
```

Results: py_compile passed; focused mounted zUSD and perps send-drop browser
regressions each `1 passed`. The new handlers support normal status, sequence,
balance, and app-state calls, then drop the `sendtx` connection before returning
any response and before recording a pending Tau transaction. The mounted stream
`11` mint and stream `8` deposit paths both return/render `502 tau_rpc_error`,
preserve app state and sender sequence, leave no pending Tau transaction, and
assert the API error body does not expose operation, sender, or signature
material. Browser/Toxiproxy packet-loss and broader jitter campaigns remain open.

Additional mounted stream `8`/`11` Tau bounded-jitter browser evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_succeeds_under_bounded_tau_send_jitter -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_succeeds_under_bounded_tau_send_jitter -s
```

Results: py_compile passed; focused mounted zUSD and perps bounded-jitter browser
regressions each `1 passed`. The new handlers support normal status and preflight
calls, delay successful `sendtx` responses by 150 ms under a 2 s Tau RPC timeout,
and then let the mounted UI complete the stream `11` zUSD mint and stream `8`
perps collateral deposit. Both tests assert the app state changes exactly once,
the pending Tau transaction is cleared after auto-mine, and the sender sequence
increments by one. This is positive bounded-jitter evidence for the mounted
submit boundary; browser/Toxiproxy packet-loss, higher-latency jitter, and
multi-surface network-chaos campaigns remain open.

Additional mounted stream `8`/`11` packet-fault proxy evidence added on
2026-05-21:

```bash
python3 -m py_compile tests/integration/tau_rpc_fault_proxy.py tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_fails_closed_on_truncated_proxy_sendtx_response -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_fails_closed_on_truncated_proxy_sendtx_response -s
```

Results: py_compile passed; focused mounted zUSD and perps packet-fault browser
regressions each `1 passed`. The new deterministic Tau RPC fault proxy forwards
normal status, balance, sequence, and app-state requests, forwards `sendtx` to
the upstream Tau-compatible server, then truncates the upstream `SUCCESS tx
accepted` frame before the terminating newline. This models the ambiguous
post-commit transport fault `ambiguous_sendtx_commit_materializes_as_success`:
the upstream has a pending transaction, but the client receives a truncated
response. The mounted stream `11` mint and stream `8` collateral deposit UIs both
render `tau_rpc_error`, do not render `SUCCESS tx accepted`, preserve committed
app state and sender sequence, and record the truncated `sendtx` fault. This
does not claim mempool cleanup or mounted browser Toxiproxy-daemon coverage; it
closes a deterministic browser packet-fault regression for the submit boundary.

Additional daemon-backed Toxiproxy Tau client chaos evidence added on 2026-05-21:

```bash
docker compose -f docker-compose.chaos.yml up -d --force-recreate toxiproxy
python3 -m py_compile tools/chaos/toxiproxy_harness.py tests/chaos/conftest.py tests/chaos/test_tau_net_client_chaos.py
python3 -m pytest -q tests/chaos/test_tau_net_client_chaos.py -s
python3 tools/check_container_hardening.py
```

Results: the Toxiproxy container reports healthy with published proxy ports
`8474` through `8480`; py_compile passed; the full Tau Net client chaos suite
ran without skips at `9 passed`; container hardening checks passed. The harness
now creates proxies on Docker-published ports, maps host-local upstreams through
`host.docker.internal`, uses Docker-reachable mock upstreams for daemon tests,
and checks real `limit_data` and `reset_peer` toxics. This is Tau client and
Toxiproxy shell-boundary evidence. At this checkpoint it did not yet prove
mounted browser Toxiproxy submit-boundary behavior, multi-node public-testnet
behavior, or stream `8`/`11` ZK execution.

Additional daemon-backed mounted browser Toxiproxy evidence added on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_perps_wallet_ui_bridge.py
npm run build
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_fails_closed_through_toxiproxy_limit_data -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_fails_closed_through_toxiproxy_limit_data -s
python3 tools/check_container_hardening.py
```

Results: py_compile passed; the DEX UI production build passed; the focused
mounted zUSD and perps Toxiproxy browser regressions each `1 passed`; container
hardening checks passed. The tests launch the mounted browser UI against the
live API, route stream `11` zUSD mint and stream `8` perps collateral submit
through the real Toxiproxy daemon, let status/preflight reach Tau successfully,
then apply a live `limit_data` toxic before releasing the upstream `SUCCESS tx
accepted` frame. Both mounted UIs render `tau_rpc_error`, do not render
`SUCCESS tx accepted`, preserve committed app state and sender sequence, and
leave the upstream Tau-compatible server with a pending transaction. This closes
focused mounted browser Toxiproxy submit-boundary coverage for the ambiguous
post-commit response-truncation fault. Broader mounted browser chaos campaigns,
multi-node public-testnet behavior, mempool cleanup policy, and stream `8`/`11`
ZK execution remain open.

Additional confidential surface claim-scope evidence added on 2026-05-21:

```bash
python3 -m py_compile tools/check_public_claim_scope.py tests/test_check_public_claim_scope.py
python3 -m pytest -q tests/test_check_public_claim_scope.py
python3 tools/check_public_claim_scope.py --json
python3 -m pytest -q tests/integration/test_api_server_confidential.py
python3 -m pytest -q tests/integration/test_confidential_ui_bridge.py -s
python3 -m pytest -q tests/integration/test_zenodex_live_cross_stream_stateful.py
python3 tools/zenodex_live_cross_stream_stateful.py --format json
```

Results: py_compile passed; public claim-scope checks `15 passed`; the public
claim-scope report returned `ok: true` across docs, the DEX UI README, the
confidential UI copy source, and the API status string source; confidential API
tests `12 passed`; mounted confidential browser smoke `1 passed`; cross-stream
stateful tests `2 passed`; the stateful replay tool returned `ok: true` for `9`
bounded scenarios plus `4` deterministic fuzz seeds of `32` steps each. The
claim-scope gate now rejects positive claims such as `verifiably confidential`
or TEE receipt proof of hardware confidentiality, while allowing explicit
negative scope lines. The mounted confidential tab now proves live operator
posture, external-verifier admission, replay rejection, response redaction,
request consumption, and bounded redacted runtime receipts. It does not prove
TEE hardware confidentiality, vendor attestation soundness, fully encrypted
on-chain state, or production FHE confidentiality.

Additional confidential runtime posture-binding evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/confidential_feature_status.py src/integration/confidential_runtime_receipts.py src/integration/confidential_attestation_api.py tests/integration/test_api_server_confidential.py
python3 -m pytest -q tests/integration/test_api_server_confidential.py
python3 -m pytest -q tests/integration/test_confidential_ui_bridge.py::test_confidential_ui_loads_live_status_surface -s
python3 tools/check_dex_live_product_goal.py --json
```

Results: the public confidential status now exposes a deterministic
`status_hash` and `approved_measurements_hash`, while the attestation status
also exposes an `external_verifier_binding_hash`. The bounded runtime receipt
and execute response now bind those public hashes into the mounted evidence, and
the Confidential tab renders all three. This narrows the live claim to one
specific operator posture, one specific measurement allowlist, and one specific
verifier configuration. It still does not prove runtime private execution,
hardware confidentiality, vendor attestation soundness, or encrypted on-chain
state.

Additional live-product goal audit evidence added on 2026-05-21:

```bash
python3 -m py_compile tools/check_dex_live_product_goal.py tests/test_check_dex_live_product_goal.py
python3 -m pytest -q tests/test_check_dex_live_product_goal.py
python3 tools/check_dex_live_product_goal.py --json
python3 -m pytest -q tests/integration/test_zenodex_live_cross_stream_stateful.py
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_fails_closed_on_malformed_dashboard_response -s
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
python3 tools/check_public_claim_scope.py --json
python3 -m pytest -q tests/test_check_public_claim_scope.py
```

Results: py_compile passed; the live-product goal audit checks `4 passed`; the
audit report returned `ok: true`, `goal_complete: false`, and
`local_testnet_evidence_present_with_open_production_limits`; cross-stream
stateful replay checks `2 passed`; the focused mounted Oracle malformed
dashboard fail-closed browser check `1 passed`; the mounted AutoTrader browser
prepare, submit, and execute-once suite `3 passed`; public claim-scope checks
`15 passed`; and the public claim-scope report returned `ok: true`. The audit
now checks the four live-product areas together: mounted UI direction,
ZenoOracle live mount, live transaction surfaces beyond spot, and browser plus
stateful resilience evidence. It also fails if the DEX UI README regresses to
the stale Strategy wording that said the mounted Strategy tab does not submit
local/testnet strategies. The README now records the current gated AutoTrader
local/testnet prepare, submit, and execute-once posture.

Additional perps Oracle-authority exercise receipt evidence added on
2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_submit_settle_epoch_binds_ready_oracle_authority_exercise tests/integration/test_perps_wallet_api.py::test_submit_settle_epoch_requires_ready_oracle_authority_when_enabled
python3 -m pytest -q tests/integration/test_perps_wallet_api.py
```

Results: py_compile passed; focused perps Oracle-authority exercise checks `2
passed`; full perps wallet API checks `32 passed`. The stream `8` proof-intent
receipt now binds a separate `oracle_authority_exercise` hash for
`settle_epoch` and `partial_liquidate` actions. A ready exercise requires both
a ready signed Oracle production-authority profile and an Oracle adapter bridge
inside the submitted operation. When
`PERPS_WALLET_REQUIRE_PRODUCTION_ORACLE_AUTHORITY=1`, the perps wallet API
fails closed before `sendtx` unless that ready authority profile and typed
Oracle bridge are both present. The mounted perps wallet UI now renders the
authority-exercised flag and authority receipt hash from the submit result.

Additional stream `8`/`11` proof-wrapper gate evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/live_proof_wrapper.py src/integration/perps_wallet_api.py src/integration/zusd_monetary_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_zusd_monetary_wallet_api.py tests/integration/test_zusd_monetary_wallet_ui_bridge.py tools/check_dex_live_product_goal.py tests/test_check_dex_live_product_goal.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_prepare_init_market_requires_zk_proof_when_enabled tests/integration/test_perps_wallet_api.py::test_prepare_init_market_accepts_verified_zk_wrapper tests/integration/test_zusd_monetary_wallet_api.py::test_prepare_mint_requires_zk_proof_when_enabled tests/integration/test_zusd_monetary_wallet_api.py::test_prepare_mint_accepts_verified_zk_wrapper
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_api.py tests/integration/test_perps_wallet_api.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_ui_smoke_through_browser -s
python3 -m pytest -q tests/test_check_dex_live_product_goal.py
python3 tools/check_dex_live_product_goal.py --json
python3 tools/check_public_claim_scope.py --json
```

Results: py_compile passed; focused proof-wrapper plus goal-audit regression
checks `8 passed`; affected zUSD monetary wallet and perps wallet API suites
`46 passed`; focused mounted zUSD browser smoke `1 passed`; the live-product
goal audit returned `ok: true`, `goal_complete: false`, and
`local_testnet_evidence_present_with_open_production_limits`; public
claim-scope audit returned `ok: true`. Stream `8` perps wallet prepares and
stream `11` zUSD monetary prepares now bind a shared external proof-verifier
wrapper over their
proof-intent receipts when `PERPS_WALLET_REQUIRE_ZK_PROOF=1`,
`ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF=1`, or
`TAU_DEX_REQUIRE_LIVE_ZK_PROOF=1` is set. If the gate is required, the APIs
fail closed before `sendtx` unless a caller-supplied proof verifies through the
configured verifier command. This is an execution-wrapper gate over
deterministic receipts. It is not yet a production RISC Zero or SP1 circuit
claim.

Additional stream `8`/`11` proof-wrapper submit fail-closed evidence added on
2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_submit_deposit_collateral_rejected_zk_proof_blocks_sendtx tests/integration/test_zusd_monetary_wallet_api.py::test_submit_mint_rejected_zk_proof_blocks_sendtx
```

Results: focused submit-path checks `2 passed`. These checks name
`zk_reject_broadcasts_tx` as the disaster state and prove that a rejected
required proof on stream `8` perps deposit or stream `11` zUSD mint returns a
400 error before any Tau `sendtx` call is made.

Additional artifact-bound proof-wrapper metadata evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/live_proof_wrapper.py src/integration/perps_wallet_api.py src/integration/zusd_monetary_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_zusd_monetary_wallet_api.py tools/check_dex_live_product_goal.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_prepare_init_market_accepts_verified_zk_wrapper tests/integration/test_perps_wallet_api.py::test_prepare_init_market_accepts_artifact_bound_zk_wrapper tests/integration/test_zusd_monetary_wallet_api.py::test_prepare_mint_accepts_verified_zk_wrapper tests/integration/test_zusd_monetary_wallet_api.py::test_prepare_mint_accepts_artifact_bound_zk_wrapper
python3 tools/check_dex_live_product_goal.py --json
```

Results: the shared live proof-wrapper gate can now carry declared verifier and
circuit artifact metadata from `*_PROOF_VERIFIER_ARTIFACT_JSON|FILE` and
`*_PROOF_CIRCUIT_ARTIFACT_JSON|FILE`, expose a public binding hash, and thread
that status into the stream `8` perps and stream `11` zUSD proof profiles.
`promotion_ready` now requires both `zk_proof_verified=true` and
`artifact_binding_complete=true`. This is still a metadata-carrying wrapper
receipt, not a claim that the repo ships production circuit artifacts or proves
their soundness.

Additional bounded AutoTrader supervisor evidence added on 2026-05-21:

```bash
python3 -m py_compile src/integration/autotrader_supervisor_profile.py src/integration/autotrader_live_api.py tests/integration/test_autotrader_live_api.py tests/integration/test_autotrader_live_ui_bridge.py tools/check_dex_live_product_goal.py
python3 -m pytest -q tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
python3 tools/check_dex_live_product_goal.py --json
```

Results: py_compile passed; the AutoTrader API suite `15 passed`; the mounted
browser suite `4 passed`; and the live-product goal audit still returned
`goal_complete: false`. The Strategy surface now exposes a bounded
local/testnet supervisor profile with deterministic preflight and execute
routes. The supervisor lane requires a ready public profile, explicit risk
acknowledgement, an externally signed Tau envelope, release and stage
certificates from the prepared bundle, and a replay-guarded execution key that
is consumed only after successful local/testnet submit. It now also enforces
the declared `max_runs_per_process` budget and exposes consumed and remaining
run counts in the mounted result surface. This is stronger mounted evidence for
supervised local/testnet automation. It still does not claim unattended
production execution, production wallet custody, or production chain
submission.

Additional bounded AutoTrader supervisor surface-binding evidence added on
2026-05-21:

```bash
python3 -m py_compile src/integration/autotrader_live_api.py tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py::test_autotrader_live_supervisor_ui_smoke_through_browser -s
python3 tools/check_dex_live_product_goal.py --json
```

Results: the supervisor preflight now binds the prepared strategy template and
allowed action set into the mounted receipt. The live API rejects supervisor
ticks when the prepared surface drifts outside the public profile's
`allowed_templates` or `allowed_actions`, and the Strategy tab renders the
bound template and action set alongside the supervisor budget. This narrows the
mounted automation claim to a specific public strategy surface. It still does
not claim unattended production execution, scheduler fairness, production
wallet custody, or production chain submission.

Remaining limits:

- isolated partial liquidation is opt-in; its evidence picker and signed Oracle
  authority profile are local/devnet mounted evidence until the signed production
  Oracle authority profile is exercised on public testnet;
- the perps wallet has external signed-envelope submit support and a public
  wallet-authority profile preflight, plus mounted signer-device integration
  reports and public device-approval, recovery, and rotation receipts; live OS
  prompt capture, device custody, and hardware-wallet execution still remain
  outside the mounted DEX UI claim;
- confidential execution is bounded to attested admission, bounded runtime
  receipts, replay protection, redaction, local accounting evidence, and public
  operator or verifier binding hashes; TEE hardware confidentiality and fully
  encrypted on-chain state remain unproved external assumptions;
- stream `8` and stream `11` now have a fail-closed external proof-verifier
  wrapper gate over proof-intent receipts, but no production RISC Zero, SP1, or
  equivalent circuit proof artifact is present yet.
