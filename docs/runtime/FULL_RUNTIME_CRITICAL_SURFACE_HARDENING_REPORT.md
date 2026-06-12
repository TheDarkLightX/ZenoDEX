# Full Runtime & Critical-Surface Disaster Hardening Report

> Bounded-evidence language throughout. "Confirmed" = reproduced with a witness;
> "documented" = verified but intentionally not patched (by design or scope);
> "negative receipt" = hypothesis tested, no witness found under stated bounds.
> This campaign shrinks disaster space with evidence; it does not certify the
> codebase secure, bug-free, or zero-day-free.

```
branch:   codex/rust-authority-promotion (worktree runtime-main-sync)
date:     2026-05-29
baseline: state-root v5 (FEE/fee_accumulator binding) + Rust shadow + proof-mining
          flag binding + support-root v3/v4 unbound-state rejection — all GREEN
authority: Python authoritative; Rust/OCaml/SPARK are assurance sidecars (not promoted)
```

## Method

Per-surface disaster-state tables, then sequence-sensitive hunting (double-submit,
copied proof vs later state, mutated witness, stale oracle through a batch,
cross-module balance leak, flag-flip after claim). Every candidate was reproduced
with a deterministic repro before being claimed; surfaces with no witness got a
bounded negative receipt. Four surfaces were audited by parallel sub-agents; **every
agent finding was independently re-reproduced before any fix** (this refuted several
over-reports in the prior round).

## Surface coverage & findings

### S1 — tau_testnet_dex_plugin (stream selection / replay / faucet) — sound + locked
Negative receipt (proof, not just test): the stream-"5" overload (upstream DEX
intents `_DEX_INTENTS_KEY="5"` vs legacy perp `_LEGACY_PERP_OPS_KEY="5"`) **cannot
double-apply** — `_select_dex_ops` selects iff `dex_like`; the perp ingress gate
selects iff `¬dex_like ∧ perp_like` (complementary). Verified empirically: a
payload that is *both* dex-like and perp-like routes to DEX only, perp gets `{}`.
Faucet is env-gated (`TAU_DEX_FAUCET`), rejects when disabled, and cannot mint the
native asset. `apply_app_tx` is atomic (any sub-stream rejection returns the
original `app_state_json`); native balances are re-sourced from `chain_balances`
each tx and only native diffs patch back. **Regression added:** `tests/runtime/test_tau_plugin_stream_faucet_regression.py` (8 tests, incl. the previously-untested both-like-ambiguous case + faucet gating).

**FIXED — S1-STREAM-002 (reserved stream fail-open):** reserved stream `5` could
carry an unsupported shape, select neither the DEX nor legacy-perps engine, and
return a successful sync-only response. The plugin now recursively decodes
list-wrapped JSON custom stream entries, rejects ambiguous DEX aliases (`2`+`5`,
`3`+`6`, `4`+`7`), and rejects stream `5` unless it is recognized as TauSwap
intents or legacy TauPerp ops. Regression:
`tests/integration/test_tau_testnet_dex_plugin.py`.

**FIXED — S1-APP-STATE-001:** the wrapped Tau app-state loader now rejects
unknown top-level wrapper fields instead of silently dropping them before
dispatching nested DEX, proof-mining, or zUSD state. Regression:
`tests/integration/test_tau_testnet_dex_plugin.py`.

### S2 — dex_engine + proof verifiers — 1 fix + 8 negative receipts
**FIXED — S2-CQ-001 (D-PROOF-COMPRESS, defense-in-depth):** a *corrupt* (vs
truncated) zlib witness made `_zlib_decompress_limited` raise `zlib.error`, which
escaped `_verify`'s `(TypeError, ValueError)` handler → verifier subprocess crash
(exit 1 + traceback to stderr). Already fail-closed (engine rejects on non-zero
exit, no state mutation), but the boundary must fail cleanly. Fixed in
`recompute_batch_v{2,3,4}.py` with a narrow `zlib.error → ValueError` at the
decompression boundary (not a broad `except Exception`, which would mask real
bugs). Repro: byte-flip mid-stream → was `zlib.error`, now `ValueError`.
**Regression:** `tests/runtime/test_recompute_witness_zlib_fail_closed_regression.py` (12 tests). Negative receipts confirm baseline invariants intact: v3/v4 reject unbound fee/vault/oracle; v1/v2 fee binding; engine-level pre-commit binding before subprocess; no-mutation-on-reject; scheme cross-dispatch rejected; tampered settlement rejected.

### S3 — zUSD (core + monetary bridge + tau wallet) — conservation holds, strict wrapper parsing
**Conservation fully holds** across mint/repay/redeem/liquidate (8 negative
receipts): `free_debt + sp_debt == debt`; liquidation splits exactly; redemption
exact; rounding is round-**up** so value creation is impossible; oracle freshness
gate on mint works; liquidation eligibility enforced; SP conservation exact; no
staking-reward accumulator (no double-count). Findings are known-design (H-RG-004
base-rate coupling — costly + bounded), intentional (recovery-mode redemption is
Liquity-style + post-MCR-gated), config-risk (protocol-collateral cap), or
**FIXED — S3-ZUSD-SNAPSHOT-001:** the zUSD monetary wrapper now rejects unknown
top-level fields and unknown stability-pool account-entry fields during app-state
load instead of silently dropping them. This keeps consensus state evolution
explicit across versions. Regression:
`tests/integration/test_zusd_monetary_wallet_api.py`.

### S4 — perps + oracle — 1 fix + 2 documented + safe-idempotency receipts
- Negative receipts: double-settle, re-settle-after-advance, split-brain oracle packets — all correctly rejected (idempotency marker `oracle_last_update_epoch=now_epoch`; `OracleRegistry` enforces one-commit-per-epoch + strict monotone sequence). Insurance/margin non-negativity enforced.
- **F-1 (documented, intentional):** `guard_settle_epoch` checks `oracle_last_update_epoch >= now_epoch` as *idempotency*, not freshness; `max_oracle_staleness_epochs` is not consulted → settlement proceeds on a stale index. This is a documented liveness-over-freshness tradeoff (`test_regression_stale_oracle_settle_epoch_accept_reject_parity` verifies the accept; opt-in `require_oracle_authorization_for_isolated_settle_epoch`). Strict deploy profiles now require the isolated settle Oracle adapter and typed authorization flags at startup. → queue P3.
- **FIXED — S4/S5-ORACLE-PROFILE-001 (deployment posture):** the fail-closed
  ZenoOracle helper required perps/zUSD/routing Oracle gates, but
  `ZENODEX_DEPLOY_PROFILE` did not enforce those runtime facts. Public-testnet
  and production-strict profiles now carry an explicit `oracle_policy`, and
  `api_server.main()` refuses to bind unless routing, zUSD, isolated-perps, and
  clearinghouse-perps Oracle adapter/authorization flags required by that policy
  are enabled. Local-dev keeps all flags optional. Regression:
  `tests/runtime/test_deploy_profile_enforced_at_startup.py`.
- **FIXED — F-3 (confirmed, fail-closed liveness):** `apply_funding_auto` required `projected_net == 0`, but floor-divided `funding_payment` doesn't sum to zero for a balanced book (`[2000,-1000,-1000]@9bps → [1,0,0]`, net=1 → blocked; ~82% of configs). The fix rejects true net base exposure, then assigns integer rounding residuals on zero-net books to a deterministic counterparty account so adjusted payments sum to zero and `fee_pool_quote` is not used as a hidden subsidy source.
- **FIXED — F-5 (stale test):** `test_perp_epoch_isolated_v3_native_initial_state_keeps_epoch_phase` asserted `epoch_phase == "Open"`, but the v3 native ABI uses int enums (`Open=0`). Aligned the assertion to the documented int ABI.

### S5/S6 — wallet-API boundary + Rust/OCaml/SPARK sidecars — 1 HIGH fix + receipts
**FIXED — S5-CRIT-001 (D-CONFIG-002, HIGH):** `api_surface_profiles.py` models
`production-strict` (forbids demo/value-moving routes) but `main()` **never called
it** — a configured production-strict API surface could serve perps/zUSD/DEX writer
routes. Wired a fail-closed gate (`ZENODEX_API_SURFACE_PROFILE`, plus the existing
`API_SURFACE_PROFILE` alias used by local config) into `api_server.main()` that
refuses to start on any violation, unknown profile id, or inconsistent aliases.
Repro: `production-strict` + perps → `main()` returns 2 ("forbids demo/value-moving
API routes"). **Regression:** `tests/runtime/test_api_surface_profile_enforced_at_startup.py` (8 tests).
- Negative receipts: no `unsafe` in Rust (`#![forbid(unsafe_code)]`); Rust `state_root` byte-exact with Python v5 incl. `fee_accumulator` (differential vectors invoke the Rust CLI: static + 4 random seeds + invalid-encoding-rejects-both); `cargo test` 68 ok, `clippy -D warnings` clean; no private key/seed/share in API responses (AST scan); loopback bind default enforced; SPARK/Ada advisory (`gnatprove` unavailable).
- **FIXED — SR-DRIFT-001 (state_root Rust shadow):** the Rust state-root shadow
  accepted `last_nonce = 2^32`, while Python's `NonceTable` rejects nonces above
  `0xFFFFFFFF`. Rust now rejects the same boundary with stable code
  `nonce_too_large`; selector coverage verifies `rust_authority_with_python_shadow`
  sees an agreed rejection instead of a drift. Regression:
  `tests/runtime/test_state_root_disaster_state.py`.
- **FIXED — S5-INFO-001 (D-KEY-001):** the signed `tau_tx_payload` was echoed in default API responses (perps + zUSD tau wallet) — a replay-capable BLS-signature artifact. Now the response **strips the signature** by default (`signature_redacted: true`, opt-in via `PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD` / `ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD`); operations/sender/sequence/fee_limit are preserved and the FULL signed payload is still SUBMITTED to the node (`sendtx`). Exhaustive no-leak regression: `tests/runtime/test_signed_payload_redaction_regression.py` (5); updated the one prior test that asserted the insecure exact-echo contract.
- **FIXED — S5-GAP-003 / deploy-profile gap:** `api_server.main()` now enforces
  `ZENODEX_DEPLOY_PROFILE` with `src/integration/deploy_profile.py` before
  binding. The gate checks raw-key/local-signing flags for perps, zUSD Tau
  wallet, zUSD monetary wallet, and AutoTrader, plus signed-payload echo flags,
  local-only fixture flags, public-auth posture, and strict-profile Oracle
  adapter/authorization posture. Regression:
  `tests/runtime/test_deploy_profile_enforced_at_startup.py`.
- **FIXED — S5-PROOF-MINING-STATE-001:** proof-mining runtime state now rejects
  unknown top-level fields, unknown `claimed_slots` row fields, and non-canonical
  reward-pool pubkeys during app-state load. Regression:
  `tests/integration/test_proof_mining_context_edges.py`.

## Evidence (commands + results)

```
# required verification (all green)
pytest tests/state/test_state_root_determinism.py tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_injectivity_proof.py tests/core/test_proof_mining_manager.py \
  tests/integration/test_recompute_batch_proof_verifier.py            -> 58 passed
python3 tools/runtime/state_root_injectivity.py                       -> OK (all obligations)
cd rust-runtime && cargo fmt --check                                  -> clean
                  cargo test -q                                       -> 68 passed
                  cargo clippy -q -- -D warnings                      -> clean
test_state_root_vectors.py (Rust CLI invoked, incl fee_accumulator)   -> 11 passed
# new regressions this campaign
tests/runtime/test_tau_plugin_stream_faucet_regression.py             -> 8 passed
tests/runtime/test_recompute_witness_zlib_fail_closed_regression.py   -> 12 passed
tests/runtime/test_api_surface_profile_enforced_at_startup.py         -> 8 passed
tests/core/test_perp_epoch_isolated_v2_native.py (F-5)                -> passes (was failing)
tests/core/test_perp_apply_funding_auto_gate.py +
  tests/integration/test_perp_engine.py -k funding_auto                -> 14 passed
tests/runtime/test_deploy_profile_enforced_at_startup.py +
  profile/API-surface/authority selectors                              -> 47 passed
tools/check_deployment_profiles.py --json                              -> ok
2026-05-31 follow-up:
python3 tools/check_deployment_profiles.py                             -> ok
python3 -m py_compile src/integration/deploy_profile.py
  src/integration/api_server.py tools/check_deployment_profiles.py      -> clean
pytest -q tests/runtime/test_deploy_profile_enforced_at_startup.py
  tests/integration/test_zeno_oracle_fail_closed_config.py              -> 50 passed
pytest -q tests/integration/test_api_server_main.py
  tests/integration/test_zeno_oracle_fail_closed_config.py              -> 13 passed
pytest -q tests/runtime                                                -> 674 passed
```

## Residual risk
P3 settle-epoch oracle freshness (strict-profile deployment-gated; core
idempotency-vs-freshness tradeoff remains); typed clearinghouse-specific oracle
authorization path, OCaml/SPARK conformance, golden-trace differential,
multi-hop batch proofs — not fully exercised. Full list:
`NEXT_RUNTIME_HARDENING_QUEUE.md`.

---

## PR Summary

```
Summary
- Hardened 6 runtime-critical surfaces on the green v5/Rust baseline. 3 confirmed
  fixes (1 HIGH config gate, 1 defense-in-depth proof-verifier fail-closed, 1 stale
  test) + 1 documented blocker + many baseline-confirming negative receipts. Did not
  weaken any trusted-baseline invariant.

Bugs Found
- S5-CRIT-001 (HIGH, D-CONFIG-002): api_surface_profiles defined but unenforced in
  main(); production-strict could serve value-moving routes. FIX: fail-closed
  ZENODEX_API_SURFACE_PROFILE/API_SURFACE_PROFILE gate in api_server.main(). TEST:
  tests/runtime/test_api_surface_profile_enforced_at_startup.py (8).
- S2-CQ-001 (LOW, defense-in-depth, D-PROOF-COMPRESS): corrupt zlib witness crashed
  the verifier (fail-closed but ungraceful). FIX: zlib.error -> ValueError at the
  decompression boundary in recompute_batch_v{2,3,4}.py. TEST:
  tests/runtime/test_recompute_witness_zlib_fail_closed_regression.py (12).
- S5-INFO-001 (LOW-MED, D-KEY-001): signed tau_tx_payload echoed by default in perps/zUSD
  wallet responses. FIX: strip BLS signature by default (opt-in flag), keep ops/metadata,
  still submit full payload to node. TEST: test_signed_payload_redaction_regression.py (5).
- S5-GAP-003 (MEDIUM, D-CONFIG-002): deployment profiles were richer than startup
  enforcement, and zUSD/AutoTrader local-signing facts were not covered. FIX:
  ZENODEX_DEPLOY_PROFILE startup gate, updated profile YAML runtime policy, and
  zUSD/AutoTrader fact coverage. Follow-up hardening adds strict-profile
  `oracle_policy` enforcement for routing, zUSD, isolated perps, and
  clearinghouse perps Oracle gates. TEST: test_deploy_profile_enforced_at_startup.py.
- SR-DRIFT-001 (state_root Rust shadow): Rust accepted nonce 2^32 while Python rejected it.
  FIX: enforce the u32 nonce bound in Rust with `nonce_too_large`. TEST:
  test_state_root_disaster_state.py.
- S4-F5 (LOW, stale test): v3 epoch_phase int-ABI assertion. FIX: assert == 0.
- S4-F3 (MEDIUM, liveness, fail-closed): funding_auto net==0 too strict.
  FIX: reject true net exposure, assign zero-net rounding residual to a deterministic
  counterparty account, and leave fee_pool_quote unchanged. TEST:
  test_perp_engine.py funding_auto residual cases.

Evidence
- required verification green (pytest 58, cargo fmt/68/clippy, Rust<->Python v5 parity 11),
  injectivity proof OK, 31 new or updated regression tests pass. See Evidence section above.

Residual Risk
- P3 settle-epoch oracle freshness (strict-profile deployment-gated; core
  idempotency-vs-freshness tradeoff remains). See NEXT_RUNTIME_HARDENING_QUEUE.md.
  Not a claim of zero bugs — bounded coverage only.
```
