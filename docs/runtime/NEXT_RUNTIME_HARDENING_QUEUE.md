# Next Runtime Hardening Queue

Priority-ordered remaining work after the 2026-05-29 disaster-state campaign
(branch `codex/rust-authority-promotion`). Bounded-evidence language: items
below are findings/blockers, not proofs. "Confirmed" = reproduced; "documented" =
verified-but-not-patched-by-design-or-scope.

## P0 — funding-auto liveness vs zero-sum (S4-F3, fixed)

`apply_funding_auto` requires `projected_net == 0` exactly, but per-account
floor-divided `funding_payment` does not sum to zero for a balanced book
(repro: positions `[2000, -1000, -1000]` at 9 bps → payments `[1, 0, 0]`, net=1).
Empirically ~82% of random configs are blocked → funding is de-facto disabled,
removing mark-price anchoring. It is **fail-closed** (no value moves), so this is
a *liveness* gap, not a safety hole.

- File: `src/core/perp_apply_funding_auto_gate.py` (net check), `src/integration/perp_engine.py` (projected_net computation/application).
- **Fix landed after this report:** auto-funding now rejects true net base exposure (`sum(position_base) != 0` when the rate is non-zero), but permits integer rounding residuals on zero-net books. The residual is assigned deterministically to a counterparty account so adjusted payments sum to zero and `fee_pool_quote` is not used as a hidden subsidy source.

Formula:
`raw_net := sum(raw_payment_i)`, `adjustment_target_delta := -raw_net`, `sum(adjusted_payment_i) = 0`.

The practical effect is that funding liveness returns for balanced books without allowing fragmented books to drain the fee pool.

## P1 — port companion-repo deploy-profile hardening into runtime-main-sync (fixed)

The companion repo (`Autonomous Tau DEX`) has deploy-profile hardening that did
NOT land here:

- ~~**S5-INFO-001:** signed `tau_tx_payload` echoed by default~~ — **DONE this session:** `perps_wallet_api.py`/`zusd_tau_wallet_api.py` now strip the BLS signature from responses by default (opt-in flags), preserving operations/metadata; full payload still submitted to the node. Tests: `tests/runtime/test_signed_payload_redaction_regression.py`.
- **Fixed:** `src/integration/deploy_profile.py` now loads `config/deploy/*.yaml`, and `api_server.main()` enforces `ZENODEX_DEPLOY_PROFILE` before binding. The gate covers `key_policy.raw_private_key_flags_allowed`, `runtime_policy.local_only_routes_allowed`, and `required_auth.public_api`.

## P2 — deploy-profile validator coverage (S5-GAP-003, fixed)

`RUNTIME_FACT_KEYS` (companion `deploy_profile.py`) covers `perps_wallet_allow_local_signing`
but NOT `ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING`, `ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING`,
`AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING`. Under `raw_private_key_flags_allowed: false`
these three are not checked → a production-strict deploy with `ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING=1`
emits zero conflicts. Add the three facts + checks. (When porting deploy_profile to main-sync, include them.)

Fixed here: the runtime facts include perps, zUSD Tau wallet, zUSD monetary wallet,
AutoTrader local signing, and signed-payload echo flags. Regression:
`tests/runtime/test_deploy_profile_enforced_at_startup.py`.

## P3 — settle-epoch oracle freshness (S4-F1, deployment-gated)

`guard_settle_epoch` uses `oracle_last_update_epoch >= now_epoch` as an
idempotency check, not a freshness check; `max_oracle_staleness_epochs` is not
consulted, so settlement proceeds on a stale index (PnL clamps to a stale
reference). This remains a **documented design tradeoff** (liveness over
freshness; `test_regression_stale_oracle_settle_epoch_accept_reject_parity`
verifies the accept). The deployment gap is now closed for strict profiles:
`config/deploy/{public-testnet,production-strict}.yaml` require the isolated
settle adapter and typed authorization flags through `oracle_policy`, and
`api_server.main()` refuses to bind if the matching environment facts are not
enabled. Local-dev keeps the tradeoff available for replay/debug loops.

Residual: the core guard still accepts by idempotency rather than staleness.
Changing that requires a deliberate kernel/semantic decision, not a
deploy-profile hardening change.

## P4 — pre-existing baseline test failures to triage (not this campaign)

Both committed (not dirty), outside the audited surfaces:
- `tests/core/test_cpmm.py::test_compute_lp_mint_uses_integer_isqrt` — test uses `n = 1<<70` exceeding `DEX_LP_AMOUNT_MAX = 1_000_000_000` (domain tightened after the test). Decide: stale test vs. a domain regression.
- (FIXED this campaign) `test_perp_epoch_isolated_v3_native_initial_state_keeps_epoch_phase` — asserted `"Open"` vs the v3 int ABI (`0`).

## P5 — coverage gaps left open by this campaign (negative-receipt boundaries)

- Clearinghouse (CH2P/CH3P) settlement oracle path: strict deploy profiles now
  require `TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH=1`
  before startup. A typed clearinghouse-specific oracle-authorization path is
  still future work; current hardening is aggregate-adapter enforcement.
- OCaml runtime conformance (needs `opam`/`dune`) and SPARK/Ada formal verification (needs `gnatprove`) — not run here; advisory.
- Golden-trace differential replay for the committed kernels supported by
  `tools/runtime/rust_shadow_replay.py` is now a regression gate:
  `tests/runtime/test_rust_shadow_golden_trace_replay.py` rebuilds the Rust CLI
  and replays `smoke.json`, `replay_guard_smoke.json`, `balance_smoke.json`,
  `zusd_smoke.json`, `burn_smoke.json`, and `cpmm_smoke.json`. Residual:
  perps isolated-op traces are still covered by their per-op materializer/live
  shadow suites rather than the generic golden-trace replayer.
- Multi-hop/multi-pool batch proofs and large-batch state/support-root computations — not stress-tested.
- Confidential sealed-bid API — absent from runtime-main-sync (present in companion); no surface here.
