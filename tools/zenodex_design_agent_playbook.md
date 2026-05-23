# ZenoDEX Design Agent Playbook (ZAG + Morph + Lean + ESSO)

## Purpose
This playbook teaches the design agent to produce *innovative* hypotheses that are also *executable* in the current supervised pipeline.

Target outcome:
- Stage 1 (design): high-novelty algorithm ideas and representation shifts.
- Stage 2 (compile): runnable `support_recipe` / `falsification_recipe` check IDs.
- Stage 3 (execute): falsify-first supervised run with conclusive outcomes.

## Two-Stage Workflow

### Stage 1: Discovery-First Design (ZAG + Morph)
Use ZAG and Morph to search representation space and mine adversarial counterexamples.

Required structure per hypothesis:
- `hypothesis_id`
- `mechanism_change`
- `representation_shift_used`: `equiv|reduce|relax|restrict|heuristic`
- `expected_metric_delta` (5-vector)
- `null_hypothesis`
- `falsification_recipe`
- `support_recipe`
- `formal_obligations`
- `risk_modes`
- `status`
- `timeout_s`

Design rules:
1. Pair each claim with a counterclaim branch when possible.
2. Prefer mechanism-level shifts (decomposition, canonicalization, dualization), not pure parameter tweaks.
3. Keep each hypothesis tied to one dominant bottleneck class:
   - timeout fragility,
   - CEGIS grammar unrealizability,
   - deterministic automation,
   - UX/performance routing latency,
   - perps adversarial safety.

### Stage 2: Executable Recipe Compilation (Lean + ESSO + Existing Checks)
Before execution, map design recipes to *known runnable check IDs*.

Run lint:
```bash
python3 tools/zenodex_design_recipe_lint.py \
  --hypotheses-json <pack.json> \
  --key top20 \
  --json-out <lint_report.json> \
  --strict --allow-unmappable
```

If lint reports `unknown`, compile/replace recipes with supported families.

## Runnable Check Families (Use These)

Base checks from `CHECK_DISPATCH` in `tools/zenodex_autonomous_checks.py`:
- `settlement_normal_form`
- `state_root_determinism`
- `batch_clearing_no_gap`, `batch_clearing_gap_exists`
- `split_routing_no_gap`, `split_routing_gap`
- `route_exact_out_2hop_value`, `route_exact_out_no_2hop_value`
- `perp_v2_invariants`, `perp_v2_invariant_break_exists`
- `perp_v2_oracle_equiv`, `perp_v2_oracle_divergence_exists`
- `cpmm_overdelivery_witness`, `cpmm_no_overdelivery_guarded`
- `intent_normal_form_tests`, `intent_normal_form_regression_exists`
- and other mapped base checks.

Dynamic families:
- `pytest_pass::<tests/.../test_x.py>`
- `pytest_fail::<tests/.../test_x.py>`
- `pytest_repeatN::<tests/.../test_x.py>`
- `lean_pass::<lean-mathlib/.../X.lean>`
- `lean_fail::<lean-mathlib/.../X.lean>`
- `lean_repeatN::<lean-mathlib/.../X.lean>`
- `esso_verify::<src/kernels/...yaml>`
- `esso_fail::<src/kernels/...yaml>`
- `esso_verify_solver::cvc5,z3::<src/kernels/...yaml>`
- `esso_verify_solver_timeout::cvc5,z3::<ms>::<src/kernels/...yaml>`
- `esso_fail_solver_timeout::cvc5,z3::<ms>::<src/kernels/...yaml>`
- `esso_repeatN_solver::cvc5,z3::<src/kernels/...yaml>`
- `esso_spec_debug_class::GRAMMAR_UNREALIZABLE::<model.yaml>::<synth.json>`
- `esso_synth_solver_timeout::cvc5::<ms>::<model.yaml>::<synth.json>`
- `esso_synth_fail_solver_timeout::cvc5::<ms>::<model.yaml>::<synth.json>`
- `perp_oracle_lp_attack_(exists|absent)::rb=...,rq=...,fee_bps=...,pfs=...,lp_share_bps=...,max_r=...,max_pos_abs=...,max_move_bps=...,target_profit_quote=...,pfr=...`
- `split_routing_tradeoff::...`
- `exact_out_split_tradeoff::...`
- `exact_out_gate_tradeoff::...`
- `routing_split_case_(optimal|gap_exists)::...`

## Mapping Strategy (Design -> Runnable)

Use this mapping when converting abstract ideas:
- Timeout-robust verification decomposition:
  - `esso_verify_solver_timeout` + paired `esso_fail_solver_timeout`
  - add `lean_repeat3` if theorem file exists.
- CEGIS grammar pruning:
  - `esso_spec_debug_class::GRAMMAR_UNREALIZABLE::...`
  - paired `esso_synth_solver_timeout` / `esso_synth_fail_solver_timeout`.
- Deterministic automation:
  - `state_root_determinism`, `intent_normal_form_tests`,
  - paired counterclaims (`*_nondeterminism_exists`, `*_regression_exists`),
  - plus `pytest_pass/fail` on integration tests.
- UX/performance routing:
  - `route_exact_out_2hop_value`, `split_routing_no_gap`,
  - dynamic `split_routing_tradeoff` and `exact_out_gate_tradeoff`.
- Perps hardening:
  - `perp_v2_invariants`, `perp_v2_oracle_equiv`,
  - dynamic `perp_oracle_lp_attack_(exists|absent)`,
  - kernel timeout posture checks on perps YAMLs.

## Evidence Gates (Promotion Policy)
Promote only if all are true:
1. Conclusive (`supported` or `falsified`), never `inconclusive`.
2. Replay-stable for formal claims (`lean_repeat3` / `esso_repeat` where applicable).
3. Counterclaim branch resolves in expected direction for the same mechanism family.
4. No unresolved `unknown_check_id` in lint report.

## Failure Patterns and Fixes
- `unknown_check_id`:
  - Recipe not mapped to supported family. Re-map using this playbook and re-lint.
- High inconclusive rate:
  - Reduce check complexity or split into staged checks (gate -> replay -> counterclaim).
- Saturated support/falsify outcomes:
  - Add boundary probes (`*_tradeoff`, perps dynamic attack parameters).
- Design novelty without executability:
  - Keep the mechanism text; only replace recipes with runnable surrogates and annotate semantic distance.

## Minimal Standard Command Sequence
1. Build design pack.
2. Lint top20 recipes.
3. Compile unknown recipes to runnable families.
4. Re-lint in strict mode.
5. Execute top20 with `zenodex_manual_supervised_runner.py`.
6. Record outcome deltas vs design-only run.

This is the standard to scale deep algorithm discovery without losing scientific rigor.
