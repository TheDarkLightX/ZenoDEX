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

## P4 — pre-existing baseline test failures to triage (fixed)

- `tests/core/test_cpmm.py::test_compute_lp_mint_uses_integer_isqrt` — fixed by replacing the out-of-domain `1<<70` fixture with an in-domain precision witness (`1_000_000_000 * 999_999_998`) where `int(sqrt(product))` would round the floor up by one.
- (FIXED this campaign) `test_perp_epoch_isolated_v3_native_initial_state_keeps_epoch_phase` — asserted `"Open"` vs the v3 int ABI (`0`).

## P5 — coverage gaps left open by this campaign (negative-receipt boundaries)

- Clearinghouse (CH2P/CH3P) settlement oracle path: strict deploy profiles now
  require `TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH=1`
  and `TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH=1`
  before startup. CH2P/CH3P `settle_epoch` now accepts `oracle_authorization`
  and checks the typed bundle against the clearinghouse runtime action id,
  pre-state hash, facts hash, query id, profile id, observed epoch, and published
  clearing price. Regressions cover missing, matching, and mismatched bundles.
  Residual: this is a runtime authorization binding, not a proof of the
  clearinghouse kernel transition itself.
- OCaml runtime conformance is now pytest-backed:
  `tests/runtime/test_ocaml_spec_oracle.py` checks that Python-derived vectors
  are current and runs `opam exec -- dune test` when the local opam switch has
  dune. SPARK/Ada formal verification still needs `gnatprove`; without it the
  SPARK kernels remain advisory/vector-checked only.
- Golden-trace differential replay for the committed kernels supported by
  `tools/runtime/rust_shadow_replay.py` is now a regression gate:
  `tests/runtime/test_rust_shadow_golden_trace_replay.py` rebuilds the Rust CLI
  and replays `smoke.json`, `replay_guard_smoke.json`, `balance_smoke.json`,
  `zusd_smoke.json`, `burn_smoke.json`, and `cpmm_smoke.json`. Residual:
  perps isolated-op traces are covered by their per-op conformance suites rather
  than the generic golden-trace replayer; `test_perp_golden_trace_coverage.py`
  now fails if a committed perps trace lacks an explicit conformance-test owner.
- Tau app-bridge stream selection now fails closed on unsupported reserved
  stream `5`, ambiguous DEX aliases (`2`+`5`, `3`+`6`, `4`+`7`), and
  list-wrapped JSON custom stream entries are decoded before engine selection.
  The wrapped Tau app-state loader also rejects unknown top-level wrapper fields
  before nested DEX/proof-mining/zUSD state dispatch.
- zUSD monetary wrapper state now rejects unknown top-level and
  stability-pool-entry fields instead of silently dropping them during
  app-state load.
- Proof-mining runtime wrapper state now rejects unknown top-level and
  claimed-slot row fields, and canonicalizes/rejects the reward-pool pubkey at
  load/initialization.
- Large mixed-batch support-root computation now has a deterministic stress
  regression in `tests/core/test_support_root.py`: many pools, balances, LP
  duration metadata, nonces, derived support sorting, tracked deltas, and
  untracked-state insensitivity. The projected recompute-batch proof verifiers
  now reject witness snapshots carrying nonzero balances, pools, LP balances, LP
  duration metadata, or nonces outside the intent-derived support set. Residual:
  multi-hop/multi-pool batch proofs and large-batch settlement/support-root
  integration remain future work.
- Settlement commitment normal-form hardening now rejects unbound fields inside
  balance/reserve/LP delta rows and rejects negative `delta_add`/`delta_sub`
  amounts before hashing. Residual: this is a boundary/commitment guard, not a
  proof that every settlement-producing path can only construct canonical rows.
- Optimized-Python fail-closed hardening: central batch-clearing and
  settlement end-to-end packet helpers no longer rely on bare `assert` for
  consensus-path invariants. Missing CREATE_POOL generated state, missing
  CREATE_POOL liquidity fields, missing AB-ordering context, missing greedy
  ordering choice, and missing endogenous LP value packet now raise explicit
  `RuntimeError`/`ValueError` under normal and `python -O` execution. Residual:
  other lower-priority bare asserts remain in integration helpers and routing
  search code; they should be converted as their surfaces enter the trusted
  core.
- Rust zUSD receipt hashing no longer reparses a just-produced hex state root
  with `expect`. The canonical layer now exposes raw SHA-256 bytes, and zUSD
  commits those bytes directly into the receipt preimage. This removes a panic
  edge from the Rust functional core and avoids a needless encode/decode cycle
  on a consensus commitment path.
- BLS release-signature and local-key-manager helpers no longer rely on
  `assert G2Basic is not None` after their optional-dependency checks. A single
  explicit helper now validates the actual `py_ecc.bls.G2Basic` object before
  signing, public-key derivation, or verification, preserving the same
  fail-closed dependency error under `python -O`.
- Confidential sealed-bid API — absent from runtime-main-sync (present in companion); no surface here.

---

# 2026-05-31 campaign additions

Ranked remaining work from the 2026-05-31 disaster-hardening campaign
(branch `claude/runtime-disaster-hardening-iso`, base `917d7b1e`). Full context:
`docs/runtime/RUNTIME_DISASTER_HARDENING_CAMPAIGN_2026-05-31.md`. Fixed this
campaign: **D-1** (floor_div_i128 totality), **F-2** (deploy-profile unknown-key
rejection); **E-1** refuted + locked.

## P0(new) — pre-existing red posture-gate tests in `deployment_profiles.py` — ✅ RESOLVED
**Resolved same day** (commits `3f8d8bd3` + `467e5146`): the 1 likely-real gap
closed by a config-coherence check, the 2 stale tests modernized;
`tests/integration/test_deployment_profiles.py` is now 11 passed. Detail below.

Three tests fail at the clean baseline `d1f9d493` (in `DexEngineConfig` posture
validation — NOT the `deploy_profile.py` YAML loader F-2 fixed). Root cause is
**not uniform** (per-test, reproduced + corrected after Codex review):
- `test_public_testnet_profile_rejects_unsafe_boundary_switches` — was **stale test
  wording** (validator flags legacy settlement as `"...must be strong_proof_carrying"`;
  test asserted old `"...must not be legacy"`). RESOLVED: assertion updated (`467e5146`).
- `test_production_strict_profile_requires_upba_and_oracle_posture` — was **stale test
  field** (`TypeError` on removed kwarg `require_uniform_batch_certificate` in
  `replace(...)`; rename expanded the strict-UPBA check 3→5). RESOLVED: config +
  assertions updated to current fields (`467e5146`).
- `test_profile_rejects_proof_required_without_enabled_verifier` — was a **real
  config-coherence gap** (`validate_deployment_profile` returned `ok=True` for
  `require_proof_when_present=True` without an enabled verifier; that config would
  start a node that rejects all intent-bearing traffic). RESOLVED: coherence check
  added to `production_config_violations` (`3f8d8bd3`).

## P1(new) — canonical-identifier domain split (accept ⊄ committable) [C-1 high-class, C-2 medium]
`recipient` and pool `asset0/asset1` (and snapshot identifiers) flow through the
accept path as raw strings (`operations.py:531` validates `recipient` only as a
non-empty ≤512-char string), but `compute_state_root` requires 0x-prefixed
fixed-length lowercase hex and dedups by decoded bytes. A signed swap with a
non-canonical `recipient`, or a snapshot with case-variant keys, is accepted/loaded
but **un-rootable** (case-variants double-count one logical pubkey). Latent today:
`dex_state_root_v0` has no `src/` callers (no wired block-producer roots the
post-state); proof-carrying / snapshot lanes that do compute roots fail closed.
- **Fix:** enforce canonical identifiers in the **consensus/ledger lane** — gate
  `recipient`/pool-asset canonicalization on the same posture that already requires
  hex senders (`require_intent_signatures=True`), OR validate per-tx rootability
  when the block-producer is wired. Do **not** enforce hex globally (breaks the
  permissive friendly-name test/dev regime). Canonicalize snapshot identifiers on
  the root's key; add an `accept ⊆ committable` property test. Both reproduced.

## P2(new) — medium documented
- **F-1:** runtime deploy-profile gate never enforces `allowed_routes`. Add an
  enforcement arm to `evaluate_deploy_profile_consistency` taking enabled-surface
  facts + a profile→surface map; refuse any enabled privileged surface absent from
  `allowed_routes`. Append as the last check (preserve existing reject precedence).
- **G-1:** claim `smt:perp_epoch_isolated_v2` is verified only as v3 by its evidence
  cmd. Repoint the claim to `…v3.yaml` (or add a v2 `verify-multi` line), and harden
  `check_claims_registry.py` to assert an smt:/shell: claim's evidence cmd actually
  references the named artifact. Do in an assurance-reviewed change.

## P3(new) — low / latent documented
- **A-3:** make `perp_isolated_op.rs` `as_bool` reject `Value::Number` and
  `req_balance_available` reject unparseable values (no `i128::MAX` saturation).
  **First verify** `_build_isolated_op_request` never serializes a bool-ish field as
  an int (else it breaks the live `rust_shadow` comparison).
- **B-1:** define a shared explicit `AMOUNT_MAX` enforced identically in Python
  `compute_state_root` and the Rust bridge (fail-closed via disagreement today).
- **A-2:** only if a future canonical caller consumes the reject code — make
  `diff_results` compare codes on dual-reject AND have `_py_case` emit a
  Rust-identical canonical reject code (else it breaks the live canonical shadow).
- **G-3:** require `rc==0` in `run_tau_spec_steps_spec_mode_with_trace` (confirm
  tau's clean-EOF exit code first). **F-3:** optional trusted-proxy XFF mode.
  **G-4:** commit a hash-pinned disaster-coverage summary. **A-1:** soften the
  "blocked regardless of mode" doc wording (gate+convention, not an in-code block)
  without obstructing the sign-off-gated promotion path.

## P4(new) — close negative-receipt boundaries
Strongest single guard for the D-surface reject-order/code parity (verified by
reading): a **committed randomized differential pytest** running representative txs
under both `python_authority` and a forced `rust_authority_with_python_shadow`,
asserting accept/reject + reject-code parity. Not yet committed.
