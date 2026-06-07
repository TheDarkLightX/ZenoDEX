# Refactor Hotspots (complexity roadmap)

Cyclomatic + cognitive complexity has been climbing. This is the objective,
prioritized roadmap — produced by the `zenodex-refactoring` design-metrics scanner
(`churn × complexity`, stdlib + git) — so refactors target where the effort pays off
and don't collide across agents.

**Discipline (non-negotiable):** behavior on critical paths (rounding, dust,
ordering, nonce, serialization, proof bindings) must be **byte-identical** unless
deliberately version-bumped with new tests. Run the verification gate
(`tools/run_critical_quality_gate.sh` + `tools/type_coverage_audit.py --check`)
before and after. Refactor the **top hotspots first; leave stable low-churn code
alone even when it looks complex.**

## Top hotspots (churn × complexity)

| Rank | File | churn | cx | LOC | Playbook move | Safety | Owner note |
|---|---|---|---|---|---|---|---|
| 1 | `src/integration/perp_engine.py` | 68 | 1086 | 4659 | Split the mutable shell into `validate`/`transition`/`emit_effects`; push pure math into `perp_v2/` | **consensus** — byte-identical + gate | HOT (batch agents) — coordinate |
| 2 | `src/integration/api_server.py` | 38 | 1619 | 6651 | Break the **5478-line** `_maybe_handle_dex_api` into per-action handlers (dispatch table) | API path; behavior-identical | HOT (batch agents) — coordinate |
| 3 | `tools/zeno_ledger_node.py` | 38 | 1410 | 5932 | Extract phase handlers; typed config over flag soup | tooling (lower risk) | check active edits |
| 4 | `src/integration/dex_engine.py` | 33 | 572 | 1564 | Split the 549-line `apply_ops` god-adapter into per-op `transition` fns | **consensus** — byte-identical + gate | HOT (batch agents) — coordinate |
| 5 | `tools/zenodex_oracle.py` | 14 | 1265 | 4967 | Extract cohesive blocks; typed receipts | tooling | — |
| 6 | `tools/zenoctl_testnet_local/lifecycle.py` | 15 | 842 | 4007 | Split `_seed_api_state` (535 lines); extract setup steps | tooling | — |
| 7 | `src/core/batch_clearing.py` | 15 | 842 | 1943 | Extract integer-math helpers from `clear_batch_single_pool` (258) / `compute_settlement` (165) | **consensus** — Lean+test armored; byte-identical | user's warm zone (touched 2d ago) — coordinate |
| 8 | `tools/zenoproof_verify.py` | 23 | 441 | 1886 | DRY expected-binding checks + name error-class sets | tooling | ✅ **DONE** (demonstration, this branch) |
| 9 | `tools/stateful_scenario_bridge.py` | 8 | 1249 | 5839 | Low churn — **leave** unless actively edited | — | skill: leave stable low-churn |
| 10 | `src/integration/perps_wallet_api.py` | 10 | 831 | 3302 | Typed request/receipt structs over raw dicts at the API boundary | consensus-adjacent | HOT (batch agents) |

## Worst single functions (god-functions / param-bloat / boolean-blindness)

| Function | Smell | Playbook move |
|---|---|---|
| `api_server.py:_maybe_handle_dex_api` | **5478 lines** | dispatch table → one handler fn per action |
| `autotrader_live.py:prepare_autotrader_live_quote_receipt` | 1925 lines, **35 params** | typed `QuoteContext` dataclass; split build stages |
| `tau_trace_cases.py:production_tau_trace_cases` | 1051 lines | data-driven case table, not inline |
| `dex_snapshot.py:state_from_snapshot` | 622 lines, 10 params, bool-blindness | per-section deserializers — **JMT/state-root zone, coordinate** |
| `settlement_strong_validator.py:_validate_settlement_strong_impl` | 612 lines, 10 params, bool-blindness×4 | typed `ValidationConfig`; split sub-validators — **consensus, gate** |
| `dex_engine.py:apply_ops` | 549 lines, 5 params | per-op transition fns |

## Rules for whoever picks one up

1. **Pure extraction first** (named helpers, signature unchanged) → zero behavior
   risk, biggest cognitive-load drop per unit effort. Do this before any
   signature/typed-config change.
2. **Consensus files** (perp_engine, dex_engine, batch_clearing, settlement_*,
   dex_snapshot): the diff must be byte-identical (state roots, reject codes,
   replay receipts unchanged) or it needs a version bump + new tests. Run the
   critical gate before+after.
3. **Don't race the batch agents.** Files marked HOT are in the live UI/wallet/perp
   wiring inventory; coordinate before refactoring them.
4. **Typed config beats flag soup**, but a signature change has blast radius — do it
   as a separate, reviewed step after the pure-extraction pass lands.

## Demonstration (done, this branch)

`tools/zenoproof_verify.py` — the proof-artifact verifier — was refactored as the
low-risk demonstration of the pattern:
- Extracted `_check_expected_binding(...)` — the strict expected-binding rule stated
  **once** instead of ~6 repeated `if expected is not None and actual != expected`
  sites across `verify_zenoproof_artifact` / `verify_o5_independence_witness` /
  `verify_oracle_o4_bridge`.
- Named the four error-class code sets as frozensets (`_BINDING_ / _POLICY_ /
  _FRESHNESS_ERROR_CODES` + their union), eliminating the duplicated 14-code literal
  that had to be hand-synced across four partition comprehensions.
- `verify_zenoproof_artifact`: 152 → 119 lines; behavior **test-verified identical**
  (18/18 relevant tests; the one pre-existing failure is an unrelated environmental
  sub-pytest replay, fails identically on clean main).
