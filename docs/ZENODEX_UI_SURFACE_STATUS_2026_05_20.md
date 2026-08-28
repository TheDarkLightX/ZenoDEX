# ZenoDEX UI Surface Status (2026-05-20)

This note records the UI surface inventory that existed on 2026-05-20.

Current authority correction (2026-08-28): normal API startup refuses the
stream `8` perps wallet, stream `9` zUSD wallet, stream `11` zUSD monetary, and
AutoTrader live routes. The checked-in local-testnet manifest, seeding,
readiness probes, feature smoke, and browser smoke omit those routes. Release
smoke rejects before reading a manifest or contacting a runtime. The visible
UI surfaces and dated evidence below remain historical donor or shadow
evidence. They do not establish current value-submission reachability,
settlement authority, or an end-user key-control workflow.

The current runtime profile sets the perps, zUSD token-transfer, and zUSD
monetary UI route flags exactly `false`. Perps retains a read-only market view
while hiding its operator console. The zUSD tab renders a read-only quarantine
notice without mounting quick-mint, monetary, token-transfer, or signer
controls. The current UI code ignores runtime, URL, and build-time requests to
enable these routes. Restart refresh overwrites all three runtime fields with
exact `false` values.

An identity-bound prior-profile stack that records any retired value route is
stopped before `up`, `down`, `status`, `smoke`, `release-smoke`, `public-up`,
`logs`, or `reset` proceeds. A forced rebuild must choose a new UI port so a
stale managed tunnel cannot reattach to the replacement local origin. The
lifecycle persists a canonical sibling origin-quarantine marker before deleting
retired state. That marker survives rebuild failure, replacement, and reset;
malformed, conflicting, or unreadable origin evidence quarantines every port
for the selected output-directory identity. Every lifecycle command quiesces a
current-shaped manifest that reuses a marked origin. The current API container
receives no mounted fixture directory and no perps authority, recovery, signer,
or SSS reconstruction file. Retained historical donor helpers begin with the
same typed current-profile refusal as their public replacements.

Every later use of "mounted" in this dated note describes the superseded
2026-05-20 research profile.

## Historical donor surface inventory

| Surface | Mounted in UI | Default posture | Authoritative backend path | Browser evidence |
| --- | --- | --- | --- | --- |
| Swap / Pools | Yes | Live local/testnet spot lane | Yes, mounted spot path through local API and Tau-ledger flow | `tests/integration/test_dex_ui_live_bridge.py` |
| zUSD | UI retained; stream-9 wallet and stream-11 monetary routes unmounted | The current tab shows a read-only quarantine notice. Historical stream `11` monetary and stream `9` wallet components remain available as source donors behind exact false runtime gates. Normal API startup refuses both routes pending current network-domain, durable-reconciliation, route, and release bindings. | Current negative evidence: `tests/integration/test_retired_value_route_ui_quarantine.py`. Historical donor evidence: `tests/integration/test_zusd_monetary_wallet_ui_bridge.py`, `tests/integration/test_zusd_monetary_wallet_ui_docker.py`, `tests/integration/test_zusd_tau_wallet_ui_bridge.py`, and `tests/integration/test_zusd_tau_wallet_ui_docker.py`. |
| Oracle | Yes | Live local operator console with authority preflight | Yes for local read/write API routes, dashboard reads, a write-enabled receipt flow, `/api/oracle/authority` production-authority preflight, and a bounded `/api/oracle/authority/exercise/evaluate` receipt lane with receipt-binding and public-evidence binding hashes. Public-testnet authority exercise still requires concrete public broadcast references. | `tests/integration/test_zeno_oracle_ui_bridge.py`, `tests/integration/test_zenodex_oracle_cli.py`, `tests/integration/test_zeno_oracle_authority.py` |
| Perpetuals | UI retained; stream-8 live wallet route unmounted | Read-only preview; current runtime hides the historical live-wallet donor panel | Historical stream `8` clearinghouse, collateral, position, epoch, Oracle, and settlement donors are retained behind an exact false runtime gate. Normal API startup refuses `/api/perps/wallet/*`. | Current negative evidence: `tests/integration/test_perps_ui_preview_lock.py` and `tests/integration/test_retired_value_route_ui_quarantine.py`. Historical donor evidence: `tests/integration/test_perps_wallet_api.py`, `tests/integration/test_perps_wallet_ui_bridge.py`, and `tests/integration/test_perps_stream8_resilience.py`. |
| Strategy | UI retained; live route unmounted | Historical donor coverage only | Normal API startup refuses `/api/strategy/autotrader/*`, and the local-testnet manifest, readiness, feature smoke, and browser smoke omit it pending client-signed DEX intent envelopes and review. | Historical donor tests: `tests/integration/test_autotrader_live_api.py`, `tests/integration/test_autotrader_execution_journal.py`, `tests/integration/test_autotrader_live_ui_bridge.py` |
| Confidential | Yes | Live operator-status plus local/testnet attestation and bounded runtime-receipt surface | Yes for status via `GET /api/confidential/status`, local/testnet external-verifier attestation receipts via `POST /api/confidential/attestation/verify`, stateful live-admission request consumption via `POST /api/confidential/attestation/admit`, and redacted bounded runtime receipts via `POST /api/confidential/attestation/execute`, now bound to public operator-status, measurement-allowlist, and verifier-configuration hashes. Runtime confidential privacy remains a non-claim. | `tests/integration/test_confidential_ui_bridge.py`, `tests/integration/test_api_server_confidential.py`, `tests/integration/test_zenodex_live_cross_stream_stateful.py` |

## Interpretation

The visible app remains the intended ZenoDEX shell. Visible tabs grant no route,
settlement, or release authority.

The next product-complete backend promotions still required are:

1. public-testnet exercise of a signed production Oracle authority profile, full wallet/key-manager UX, and proof/ZK qualification before any perps live lane is mounted;
2. client-signed DEX intent envelopes, durable ambiguous-outcome reconciliation, and a reviewed strategy route before AutoTrader may be mounted;
3. confidential runtime privacy beyond the external-verifier attestation receipt, live-admission gate, and bounded redacted runtime receipt path.

Normal API startup refuses `/api/zusd/wallet/*` and
`/api/zusd/monetary/*`. Both transport implementations and their historical UI
tests are direct shadow/donor material until current network-domain,
durable-reconciliation, route, and release obligations close.

The perps donor has focused backend and browser evidence for an unmounted live
wallet candidate. In the superseded profile, collateral-minted zUSD could be transferred and used as the quote collateral
asset for signed clearinghouse collateral deposits, and the UI can submit signed
stream `8` market init, oracle price publish, and opt-in isolated partial
liquidation actions through `/api/perps/wallet/*`. Local typed Oracle bridge
fixtures cover both `settle_epoch` and isolated `partial_liquidate` browser
tests. The perps wallet UI now has a verifier-backed Oracle evidence inspector
for pasted or locally built aggregate-adapter bridges, plus a live ZenoOracle
candidate picker/viewer that loads accepted reads, authorizations, and
aggregates from the mounted Oracle service URL and prefers action-matching
authorizations for `settle_epoch` and `liquidate_account`. The perps wallet
submit path also accepts externally signed Tau transaction envelopes and
validates their sender, sequence, expiry, fee, operations, and BLS signature
before `sendtx`, so an external signer or key-manager can drive the live stream
`8` lane without enabling local raw-key signing in the API. The perps wallet API
now emits a deterministic `perps_stream8_live_wallet_v0` proof-intent receipt
that binds chain id, stream key, operation hash, operation-stream hash,
pre-submit app hash, optional post-submit app hash, Tau envelope hash, preflight
result, sender, sequence, fee limit, signing mode, and a public state-delta
witness for changed perps markets after submit. The retained donor UI renders that
proof profile, receipt hash, delta-witness count, the perps wallet-authority
preflight status, public recovery and rotation exercise receipts when present,
and the perps-side Oracle authority preflight status.
`/api/perps/wallet/status` can load a public wallet-authority profile from
`PERPS_WALLET_AUTHORITY_PROFILE_JSON` or
`PERPS_WALLET_AUTHORITY_PROFILE_FILE`; a ready profile requires public
key-manager refs, a matching signer registry, external signer and device
approval controls, recovery policies for active signer keys, stream `8` scope,
state-delta witness requirements, and an explicit proof/ZK runtime profile. The
same status route can load an Oracle production-authority profile from
`PERPS_ORACLE_AUTHORITY_PROFILE_JSON`, `PERPS_ORACLE_AUTHORITY_PROFILE_FILE`,
`ZENO_ORACLE_AUTHORITY_PROFILE_JSON`, `ZENO_ORACLE_AUTHORITY_PROFILE_FILE`, or
`ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE`; that claim is blocked unless the
Oracle profile validates and its chain id matches the perps wallet chain. The UI
reports both authorities as blocked when profiles are absent, invalid, or missing
a signer-registry BLS signature quorum over the authority profile hash, while
keeping `zk_proof_verified=false` until a real RISC Zero or equivalent verifier
is present. The retained perps wallet donor also surfaces `ZK Artifacts` and the
wrapper binding hash when a submit carries declared verifier and circuit
artifact metadata. The completion plan is recorded in
`docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md`. The main blockers are now
public-testnet signed Oracle authority exercise, hardware/OS wallet UX and
runtime signer-device integration behind the public wallet-authority profile,
and production circuit artifacts plus soundness evidence for stream `8`.

The zUSD monetary lane is Liquity-like but does not claim exact Liquity V2
liquidation parity. The current 5% borrower-penalty gap is tracked in
`docs/ZUSD_LIQUITY_PARITY_STATUS_2026_05_20.md`.

The zUSD monetary submit path now accepts externally signed Tau transaction
envelopes for stream `11`. The API validates the signed envelope's sender,
sequence, expiry, fee limit, encoded operations, and BLS signature before
`sendtx`, so collateral, mint, repay, redeem, stability-pool, liquidation, and
SP-claim actions can be driven by an external signer or key-manager without
enabling local raw-key signing in the API.

The historical AutoTrader donor path accepted an externally signed Tau
transaction envelope for the prepared strategy operation bundle and exercised
an execute-once route and bounded supervisor route in isolated tests. The donor
validates the envelope's sender, current sequence, expiry, fee limit,
encoded operations, and BLS signature before `sendtx`; replaying the same
signed envelope is rejected before a second `sendtx`; the execute-once path
durably reserves a caller-provided execution ID immediately before one exact
signed payload is sent, binds the reservation to the chain and payload root,
and blocks replay for both `PENDING` and `SENT` outcomes; and the supervisor
path requires a public local/testnet supervisor profile plus a deterministic
preflight receipt before submit. The supervisor
lane now also enforces the declared per-process run budget and exposes the
remaining run count in donor status and result receipts. This is
Tau-envelope transport, stateful replay-guard, and bounded supervisor evidence
for a possible Strategy panel. Normal API startup now refuses this path, so it
provides no mounted local-testnet or production authority.

The confidential tab now has a live local/testnet attestation receipt,
admission path, and bounded runtime-receipt path. The mounted API invokes a
configured external verifier command, builds a confidential extension receipt
from the verifier's measurement, policy digest, and attestation epoch, then
applies the in-repo receipt hash, freshness, accounting, host-guard,
measurement-allowlist, expected-policy, and stateful request-replay gates
before returning either an admitted receipt or a redacted bounded runtime
receipt. The runtime path exposes only provider family, request binding, public
effect digest, receipt hashes, operator-status hash, measurement-allowlist
hash, and verifier-binding hash. Runtime confidential privacy and in-process
remote-attestation cryptography remain out of scope.

## Historical donor browser checks

Run these from repo root:

```bash
pytest -q \
  tests/integration/test_zusd_monetary_wallet_ui_bridge.py \
  tests/integration/test_zusd_monetary_wallet_ui_docker.py \
  tests/integration/test_zeno_oracle_ui_bridge.py \
  tests/integration/test_perps_wallet_ui_bridge.py \
  tests/integration/test_perps_ui_preview_lock.py \
  tests/integration/test_confidential_ui_bridge.py
```

These checks provide bounded test evidence that:

- the mounted Oracle tab can bind to a real local Oracle service and execute a
  write-enabled local receipt flow when the service is started with
  `--allow-writes`, while an unreachable local Oracle service renders a
  fail-closed offline status and keeps authority blocked;
- the retained zUSD donor exercised stream `11` monetary-vault actions through the historical Tau-node-backed API;
- the retained perps tab fails closed to read-only preview by default for the demo trading grid in non-demo mode;
- the retained perps wallet donor exercised signed stream `8` clearinghouse init
  and oracle price publish actions through the Tau-node-backed API;
- the mounted confidential tab can load live operator posture from the stdlib API server and run a local/testnet external-verifier attestation admission smoke.

Historical backend-only perps bridge checks:

```bash
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_perps_accepts_zusd_token_as_quote_collateral
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral
pytest -q tests/integration/test_zusd_monetary_wallet_api.py
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
python3 tools/zenodex_live_cross_stream_stateful.py --format json
```

Historical AutoTrader donor checks, unmounted as of 2026-08-26:

```bash
pytest -q tests/integration/test_autotrader_live_api.py
pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
```

These historical tests exercised a directly enabled donor API with explicit
risk acknowledgement and local-signing enablement. They covered a signed
receipt-backed operation bundle and local/testnet Tau RPC submission behind
`AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION=true`, and renders the result in the
Strategy tab. The same donor suite also covered a bounded supervisor route that
requires a public local/testnet supervisor profile, emits a supervisor
preflight receipt, consumes a replay-guarded execution key after successful
submit, and enforces the declared per-process run budget. They do not claim
unattended production strategy execution, production wallet key management, or
production chain submission. They are excluded from the current mounted test
list because normal startup refuses the route.

Historical AutoTrader live-prepare pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
```

Results: `4 passed` and `1 passed`.

Historical AutoTrader local/testnet submit pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
npm run build
```

Results: `14 passed`, `4 passed`, and Vite production build passed. The
historical API suite included a Tau app-bridge application check showing that
the default prepared AutoTrader signed intent payload applied against the same
deterministic fixture pool quoted by the live-preparation path. It also accepted
a valid externally signed Tau envelope and rejected duplicate signed-envelope
replay before a second `sendtx`. It exposed `POST
/api/strategy/autotrader/execute-once`, gated by
`AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED=true`, which durably reserves an execution
ID immediately before the first network send and rejected replay before a second
broadcast. Each reservation committed to one exact chain and signed Tau payload;
an ambiguous response remained `PENDING`, while explicit Tau acceptance advanced
the same row to `SENT`. It also exposed `POST
/api/strategy/autotrader/supervisor/preflight` and `POST
/api/strategy/autotrader/supervisor/execute`, gated by
`AUTOTRADER_LIVE_SUPERVISOR_ENABLED=true`, which required a ready public
supervisor profile, emitted a deterministic preflight receipt, bound the prepared
template and allowed action set, required an externally signed Tau envelope,
and used the same durable one-payload execution reservation. The historical browser submit,
execute-once, and supervisor smokes called the donor Strategy tab, sent the
externally signed prepared Tau transaction to a Tau-compatible local/testnet
RPC, and rendered the `sendtx`, preflight, signing mode, strategy surface, and
consumed execution key evidence. These results do not describe a route admitted
by current normal startup.

Historical mixed local browser pass on 2026-05-20:

```bash
pytest -q tests/integration/test_zusd_tau_wallet_ui_bridge.py tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_zeno_oracle_ui_bridge.py tests/integration/test_perps_ui_preview_lock.py tests/integration/test_confidential_ui_bridge.py
pytest -q tests/integration/test_dex_ui_live_bridge.py
```

Results at that historical revision: non-spot browser checks `7 passed`;
spot/pools browser checks `2 passed`. The stream `9` zUSD wallet result does
not describe a route admitted by current normal startup.

Latest Oracle offline fail-closed browser pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zeno_oracle_ui_bridge.py
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_fails_closed_when_local_service_unreachable -s
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py -s
npm --prefix tools/dex-ui run build
```

Results: py_compile passed; focused mounted Oracle offline smoke `1 passed`;
full mounted Oracle UI bridge suite `5 passed`; UI production build passed. The
Oracle tab now renders `Local API offline` when the configured local Oracle
service URL is unreachable, keeps `Authority blocked`, and does not render
`Production authority ready`.

Latest perps live-wallet pass on 2026-05-20:

```bash
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: `4 passed`, `4 passed`, and `1 passed`.

Latest perps proof-intent receipt pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_prepare_init_market_2p_builds_signed_stream_8_and_preflights tests/integration/test_perps_wallet_api.py::test_submit_accepts_external_signed_tau_payload_without_local_signing tests/integration/test_perps_wallet_api.py::test_status_exposes_clearinghouse_liquidation_summary_fields
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_smoke_through_browser -s
npm run build
```

Results: API proof-profile checks `3 passed`, browser proof-profile smoke `1
passed`, and Vite production build passed. This is deterministic proof-intent
and state-delta witness evidence for stream `8`; it does not claim real zkVM
execution.

Latest perps wallet-authority preflight pass on 2026-05-21:

```bash
python3 -m py_compile src/integration/zeno_ledger_signature.py src/integration/perps_wallet_authority.py src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py tests/integration/test_perps_stream8_resilience.py
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
npm run build
```

Results: py_compile passed, perps wallet API plus stream-8 resilience checks `31
passed`, mounted perps wallet browser checks `6 passed`, and Vite production
build passed. The mounted wallet status now reports a public perps
wallet-authority profile as `ready` only when public key-manager refs, signer
registry binding, required external-signing controls, stream `8` scope, and
proof-profile requirements all validate; otherwise the UI renders the authority
as blocked.

Latest perps wallet recovery-profile pass on 2026-05-21:

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
wallet-authority profile now requires recovery-policy metadata for every active
wallet signer key and the mounted UI renders `wallet recovery 2/2` alongside
the signer and authority posture. Recovery and rotation exercise receipts are
separate public lifecycle receipts over threshold/delay satisfaction and
current-to-next authority transitions, and they now include guardian BLS
signature quorum verification over the public exercise hash. They still do not
prove custody of keys, live OS or hardware prompt execution, or chain finality.

Latest perps wallet device-approval pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_perps_wallet_device_approval_exercise_ready_receipt tests/integration/test_perps_wallet_api.py::test_perps_wallet_device_approval_exercise_blocks_missing_user_presence tests/integration/test_perps_wallet_api.py::test_perps_wallet_device_approval_exercise_blocks_reused_nonce tests/integration/test_perps_wallet_api.py::test_status_loads_ready_perps_wallet_device_approval_exercise tests/integration/test_perps_wallet_api.py::test_device_approval_evaluate_endpoint_blocks_missing_user_presence tests/integration/test_perps_wallet_api.py::test_device_approval_evaluate_endpoint_blocks_reused_nonce -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_smoke_through_browser -s
```

Results: focused device-approval checks passed and the mounted browser smoke now
renders `device approval ready`, `device sign admission ok`, and a public
device-approval receipt hash when `PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON`
is present. This is a bounded sign-admission receipt over declared backend,
policy, environment, nonce, and chain binding. It still does not prove live
hardware custody, a real OS prompt, or chain finality.

The mounted perps wallet can now also load
`PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON` or
`PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_FILE` and render a separate signer-device
integration report with backend kind, provider, device-approval mode,
environment posture, and a public status hash. This narrows the signer-device
claim from generic metadata to a concrete local backend plus environment report.
It still does not prove live OS prompt capture, hardware custody, or hardware
wallet execution.

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
state unchanged. The Docker run now also restarts the `tau-local` container
after the perps deposit, verifies the post-deposit app state survives restart,
and rejects the same signed stream `8` payload again after restart without state
mutation.

Latest perps Oracle evidence inspector pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_oracle_bridge_inspector_summarizes_verified_settle_bridge tests/integration/test_perps_wallet_api.py::test_oracle_bridge_inspector_rejects_tampered_action_id
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_oracle_bridge_template_preflights_required_partial_liquidate tests/integration/test_perps_wallet_api.py::test_oracle_bridge_template_preflights_required_settle_epoch
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge -s
```

Results: inspector checks `2 passed`, bridge-template checks `2 passed`, settle
browser `1 passed`, and partial-liquidation browser `1 passed`. The API
inspector accepts a valid settle-time aggregate-adapter bridge, rejects an
action-ID tamper with `adapter_action_id_mismatch`, and the mounted UI renders
accepted Oracle evidence fields before submit. The browser checks now start a
local ZenoOracle service, seed canonical perps index authorizations for
`settle_epoch` and `liquidate_account`, load the service dashboard through
`VITE_ZENO_ORACLE_API_URL`, and render live candidate counts plus the
action-matching selected authorization beside the perps submit flow.

Latest perps Oracle-authority binding pass on 2026-05-21:

```bash
python3 -m py_compile src/integration/perps_wallet_api.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_status_exposes_clearinghouse_liquidation_summary_fields tests/integration/test_perps_wallet_api.py::test_status_loads_ready_oracle_authority_profile tests/integration/test_perps_wallet_api.py::test_status_blocks_oracle_authority_profile_chain_mismatch
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: py_compile passed; focused perps Oracle-authority status checks `3
passed`; mounted settle/browser smoke `1 passed`; full mounted perps wallet
browser bridge suite `6 passed`. The perps wallet status now renders
`production_oracle_authority=false` when the profile is absent, accepts a ready
profile only when the chain id matches, rejects a chain-mismatched profile, and
the mounted perps UI renders `oracle authority ready` plus the active signer
threshold in the live settle flow.

Latest isolated partial-liquidation Oracle-authority pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: py_compile passed; mounted partial-liquidation browser smoke `1
passed`; full mounted perps wallet browser bridge suite `7 passed`. The test now
binds the mounted `liquidate_account` flow to a production-shaped Oracle
authority profile with a matching chain id and active 2-of-2 signer registry,
then renders `oracle authority ready`, `oracle signers 2/2`, and the local
ZenoOracle evidence picker in the same browser run.

Latest stream `8` stateful resilience pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_stream8_resilience.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py tests/integration/test_perps_stream8_resilience.py tests/integration/test_zenodex_live_cross_stream_stateful.py
python3 tools/zenodex_live_cross_stream_stateful.py --format json
```

Results: py_compile passed; adjacent perps wallet, stream `8` resilience, and
cross-stream stateful checks `37 passed`; the replay tool accepted `8` bounded
scenarios plus `4` deterministic fuzz seeds of `32` steps each. New stream `8`
coverage rejects out-of-order signed position nonces without app-state mutation
and rejects stale aggregate-adapter Oracle bridges before `settle_epoch`
mutates the market. Docker restart evidence is covered below; network chaos
remains open.

Latest perps wallet Tau RPC send-failure retry pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_api.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_submit_external_signed_payload_can_retry_after_tau_send_failure_without_state_drift
```

Results: py_compile passed and the focused failure/retry regression `1 passed`.
The mounted perps wallet backend returns `502` for a transient Tau RPC send
failure, preserves app state, avoids recording a queued transaction, and accepts
the same externally signed stream `8` payload after the node recovers while the
sequence is unchanged. Live Docker process restart and pause/retry evidence are
covered below. Packet-level network partition/latency chaos remains open.

Latest perps wallet node-restart replay pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_api.py
python3 -m pytest -q tests/integration/test_perps_wallet_api.py::test_submit_external_signed_payload_replay_after_node_restart_rejected_before_sendtx
python3 -m pytest -q tests/integration/test_perps_wallet_api.py tests/integration/test_perps_stream8_resilience.py
```

Results: py_compile passed; the focused restart replay regression `1 passed`;
perps wallet plus stream `8` resilience checks `37 passed`. The mounted perps
wallet backend accepts an externally signed stream `8` submit, persists the
post-submit app state and advanced sender sequence into a restarted Tau client,
then rejects the old signed payload before a second `sendtx`. Live Docker
process restart is covered by the Docker Tau-node browser lane. Packet-level
network partition/latency chaos remains open.

Latest Docker Tau-node restart and pause/retry pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zusd_monetary_wallet_ui_docker.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_docker.py -s
```

Results: py_compile passed; Docker Tau-node browser/restart/pause test `1
passed`. The mounted browser lane mints zUSD through stream `11`, prepares a
signed perps stream `8` collateral deposit, pauses `tau-local`, verifies the
paused-node submit returns `502` with `tau_rpc_error` and no app-state drift,
unpauses the node, posts the same signed payload into live perps collateral
through the mounted UI, restarts the `tau-local` container, confirms persisted
app state, and rejects the same signed perps payload after restart before any
mutation. Packet-level network partition/latency chaos remains open.

Oracle live-surface note: `tests/integration/test_zeno_oracle_ui_bridge.py`
now proves both the live dashboard read path and a write-enabled local receipt
flow from the mounted Oracle tab. It also proves an unreachable configured local
Oracle service renders `Local API offline` and keeps the mounted authority
status blocked. The write smoke creates an identity,
registers and funds a query, registers and bonds a reporter, registers a
source, submits a report, builds aggregate/read/authorization receipts, and
pays rewards against a local `tools/zenodex-oracle serve --allow-writes`
instance. It also proves the read-only local service fails closed for the same
mounted receipt flow by surfacing `write_api_disabled` instead of accepting a
receipt write when `--allow-writes` is absent. The local service now exposes
`/api/oracle/authority`; `tools/zenodex-oracle authority provision-profile`
writes `authority/production_authority_profile.json` from public key-manager and
signer-registry JSON plus signer-supplied BLS envelopes, and the mounted Oracle
tab renders `Authority blocked` or `Production authority ready` according to
that profile. The mounted Governance view now includes an authority profile
panel with public key-manager refs, active signer mappings, signed-quorum
posture, wallet approval controls, and proof/replay posture. It also includes a
bounded authority-exercise panel that reruns the local operator flow and binds
the resulting query/report/aggregate/read/authorization/reward receipt ids into
a deterministic exercise receipt. Public-testnet exercise still remains blocked
until concrete public broadcast references are supplied. A ready profile
requires key-manager refs, an Oracle authority signer registry, a BLS signature
quorum over the authority profile hash, required wallet approval controls, and a
proof/replay profile.

Latest Oracle browser pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_zeno_oracle_authority.py tests/integration/test_zenodex_oracle_cli.py::test_dashboard_snapshot_and_local_api_server tests/integration/test_zeno_ledger_verify_cli.py::test_bls_signer_registry_enforces_signature_quorum
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py -s
npm run build
```

Result: authority/API/signature checks `10 passed`, Oracle browser checks `4
passed`, and Vite production build passed.

Latest Oracle signed-authority quorum pass on 2026-05-21:

```bash
python3 -m py_compile src/integration/zeno_oracle_authority.py tools/zenodex_oracle.py tests/integration/test_zeno_oracle_authority.py tests/integration/test_zeno_oracle_ui_bridge.py tests/integration/test_perps_wallet_api.py tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_zeno_oracle_authority.py tests/integration/test_perps_wallet_api.py::test_status_loads_ready_oracle_authority_profile tests/integration/test_perps_wallet_api.py::test_status_blocks_oracle_authority_profile_chain_mismatch -s
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_reports_ready_authority_profile -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge -s
python3 -m pytest -q tests/integration/test_zeno_oracle_ui_bridge.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_api.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
cd tools/dex-ui && npm run build
```

Results: Python compile passed; focused Oracle authority/API checks `12
passed`; focused Oracle browser ready-authority check `1 passed`; focused perps
settle browser check `1 passed`; focused perps partial-liquidation browser check
`1 passed`; Oracle browser suite `5 passed`; full perps wallet API `30 passed`;
full mounted perps wallet browser bridge `7 passed`; Vite production build
passed. Production Oracle authority now fails closed unless
`signature_envelopes` verify as a signer-registry BLS quorum over the
`authority_hash`. The Oracle Governance UI renders `Signed quorum 2/2`, and the
perps live wallet UI renders `oracle signed quorum 2/2` for both settle and
partial-liquidation Oracle authority paths.

Latest confidential attestation and bounded runtime-receipt pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_api_server_confidential.py
python3 -m pytest -q tests/integration/test_confidential_ui_bridge.py -s
```

Results: API checks `12 passed`; mounted browser smoke `1 passed`. The accepted
paths now cover both live admission and bounded runtime execution: the execute
route returns a deterministic redacted runtime receipt, exposes only provider
family plus a public effect digest, and consumes the request only after the
runtime receipt is built successfully. Rejection coverage includes sensitive
startup gating, unapproved measurements, stale attestations, host-guard
failure, accounting mismatch, policy-digest mismatch without request
consumption, request replay, bad runtime metadata without request consumption,
and a disabled verifier. The browser smoke renders `attestation accepted`,
`measurement nitro`, `execution admitted`, `request consumed`, `runtime receipt
ready`, and `result redacted` through the mounted Confidential tab. The API
checks also assert that raw attestation payload fields, policy digests, and raw
PCR values are not echoed in accepted execute responses, and the browser smoke
asserts that raw Nitro PCR values and the policy digest are not rendered in the
mounted DOM.

Latest cross-stream stateful replay pass on 2026-05-21:

```bash
python3 tools/zenodex_live_cross_stream_stateful.py --format json
pytest -q tests/integration/test_zenodex_live_cross_stream_stateful.py
```

Results: replay tool accepted `8` bounded scenarios plus `4` deterministic fuzz
seeds of `32` steps each; receipt tests `2 passed`. The covered disaster states
are duplicate zUSD replay side effects, cross-stream partial mutation, expired
zUSD deadline materialization, perps overdeposit materialization, missing Oracle
bridge settlement, balance drift after a zUSD-to-perps success path, and
confidential admission replay/digest drift. The replay also covered the historical
AutoTrader execute-once donor lane: deterministic failures before the send boundary
leave no reservation, every outcome after reservation blocks replay, and an
ambiguous network outcome remains `PENDING` rather than authorizing a second Tau
transaction. Long-horizon fuzz still covers balance/nonce/atomicity drift.

Unintegrated AutoTrader donor-hardening result from 2026-08-23:

```bash
python3 -m pytest -q tests/integration/test_autotrader_execution_journal.py tests/integration/test_autotrader_live_api.py
python3 -m mypy src/integration/autotrader_execution_journal.py src/integration/autotrader_live_api.py
```

Results: `74 passed`; mypy reported no issues. The regressions cover
cross-process reservation races, a 16-case structure-preserving malformed-row
atlas, duplicate JSON fields, exact submission-root binding, sequence-race
second-send prevention, response-loss quarantine, and preservation of `SENT`
after a later block-observation failure. Automatic
reconciliation of `PENDING` submissions remains unimplemented, and this donor
evidence grants no mounted local-testnet or production settlement authority.

Latest Tau transaction canonicalization and RPC redaction pass on 2026-05-21:

```bash
python3 -m py_compile src/integration/tau_net_client.py tests/integration/test_tau_net_client.py
python3 -m pytest -q tests/integration/test_tau_net_client.py -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_api.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_api.py -s
```

Results: py_compile passed; Tau client checks `6 passed`; zUSD monetary wallet
API checks `10 passed`; perps wallet API checks `29 passed`. Tau transaction
signing and nested operation wire encoding now use the repo canonical JSON
encoder, so noncanonical values such as floats are rejected before signing. Tau
RPC connect, send, receive-reset, and receive-timeout failures are normalized to
`TauNetRpcError` so mounted zUSD/perps APIs return `502` fail-closed responses
instead of uncaught socket errors. The socket tests also assert Tau RPC error
details do not echo private command text or partial response bytes.

Latest Tau RPC packet-framing chaos pass on 2026-05-21:

```bash
python3 -m py_compile src/integration/tau_net_client.py tests/integration/test_tau_net_client.py tests/chaos/test_tau_net_client_chaos.py
python3 -m pytest -q tests/integration/test_tau_net_client.py -s
python3 -m pytest -q tests/chaos/test_tau_net_client_chaos.py -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_fails_closed_on_partial_tau_send_timeout -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_fails_closed_on_partial_tau_send_timeout -s
```

Results: py_compile passed; Tau client checks `6 passed`; Tau client chaos `7
passed, 2 skipped`; mounted perps and zUSD partial-response browser regressions
each `1 passed`. `TauNetTcpClient.rpc()` now rejects peer-close responses that
arrive without the newline frame terminator, so truncated packet closes cannot
be mistaken for accepted Tau RPC responses and partial bytes are not exposed in
error text.

Latest multi-surface Tau network-chaos pass on 2026-05-21:

```bash
python3 -m py_compile tests/chaos/test_live_surface_tau_network_chaos.py tests/chaos/test_tau_net_client_chaos.py src/integration/tau_net_client.py
python3 -m pytest -q tests/chaos/test_live_surface_tau_network_chaos.py tests/chaos/test_tau_net_client_chaos.py -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_api.py tests/integration/test_perps_wallet_api.py -s
```

Results: py_compile passed; combined Tau client plus live-surface chaos `8
passed, 2 skipped`; adjacent zUSD/perps wallet API suites `39 passed`. The new
campaign drives both stream `11` zUSD monetary submit and stream `8` perps
wallet submit through externally signed payloads, injects packet loss before
commit for zUSD and jitter/timeout before response for perps, and asserts both
routes return `502 tau_rpc_error` with no accepted Tau transaction, unchanged
app state, and no operation, sender, or signature material in the error detail.

Latest mounted zUSD Tau RPC partial-response chaos pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_zusd_monetary_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py::test_zusd_monetary_wallet_browser_fails_closed_on_partial_tau_send_timeout -s
python3 -m pytest -q tests/integration/test_zusd_monetary_wallet_ui_bridge.py -s
```

Results: py_compile passed; focused browser chaos regression `1 passed`; full
zUSD monetary browser bridge `2 passed`. The new harness runs the mounted zUSD
tab, live API server, and a Tau-compatible TCP server that accepts normal status
and prepare calls but, on `sendtx`, sends partial private response bytes without
a newline and stalls past the configured Tau RPC timeout. The API returns `502`
with `tau_rpc_error`, the mounted UI renders that fail-closed error without
leaking the partial response, the Tau app state is unchanged, no pending
transaction is recorded, and the sender sequence remains unchanged. Broader
browser/Toxiproxy packet-loss, jitter, and multi-surface network-chaos campaigns
remain open.

Latest mounted perps Tau RPC partial-response chaos pass on 2026-05-21:

```bash
python3 -m py_compile tests/integration/test_perps_wallet_ui_bridge.py
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py::test_perps_wallet_ui_fails_closed_on_partial_tau_send_timeout -s
python3 -m pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: py_compile passed; focused stream `8` browser chaos regression `1
passed`; full perps wallet browser bridge `7 passed`. The new harness runs the
mounted perps tab, live API server, and a Tau-compatible TCP server that accepts
normal status and preflight calls, then sends partial private response bytes on
`sendtx` and stalls past the configured Tau RPC timeout. The API returns `502`
with `tau_rpc_error`, the mounted UI renders that fail-closed error without
leaking the partial response, the app state is unchanged, no pending transaction
is recorded, and the sender sequence remains unchanged. Together with the
stream `11` zUSD chaos pass, mounted stream `8` and stream `11` now both cover
partial-response timeout at the submit boundary. Broader browser/Toxiproxy
packet-loss, jitter, and multi-surface chaos campaigns remain open.

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
