# Tau Lang Optimization Experiments

This directory holds experimental Tau specs that try to improve on the main
project specs along three axes:

- lower Tau-side complexity, especially around temporal warmup and repeated
  arithmetic subexpressions;
- better observability, by exposing intermediate checks instead of a single
  opaque final gate.
- cleaner decomposition boundaries, by separating compact production gates from
  heavier explained or proof-gated variants.

## Main insights

1. Keep definitions single-line.
   Tau's file runner is stricter than the authoring style used in this repo.
   Multi-line `always` blocks are recoverable via normalization, but multi-line
   `:=` definitions are fragile.

2. Avoid temporal indexing when the host already supplies aligned history.
   Several settlement-style specs describe `i5..i7` as `prevprev/prev/curr`,
   but still reference `t-2` and `t-1`. If history is already bundled at the
   current step, same-step predicates are simpler and cheaper.

3. Decompose wide gates into named checks, but do not compose outputs into other
   outputs inside the same `always`.
   Tau is better used as a validator/composer than as a giant monolithic
   arithmetic engine. Exposing subchecks makes traces easier to debug, but
   final gates are more stable when flattened back to the underlying formulas.

4. Bound multiplication separately from transition structure.
   For bitvector CPMM checks, safe-range guards should be explicit. If the host
   already computes `k` or pricing witnesses, passing them as `sbf` flags is a
   good hybrid pattern.

5. Prefer host-computed flags for expensive or redundant logic.
   Ordering canonicalization, full CPMM pricing, and cross-field arithmetic are
   often already computed outside Tau. Tau can then validate the boolean
   structure and fail closed.

6. Keep both a compact gate and an explained gate when the logic is important.
   The compact gate is the production candidate. The explained gate is the
   debugging surface. They serve different jobs.

7. For hard positive cases, decompose and externally join.
   The strongest example is batching: Tau struggled to prove the whole positive
   witness quickly in one compact spec, but the same semantics became
   trace-backed when split into distinctness, membership, and ordering rails.

## Measured result so far

Using `python3 experiments/tau_lang_optimizations/benchmark_specs.py` and the
repo's `run_tau_spec_steps` harness:

- `batching_v1_4.tau`: mean `6603.70ms`
- `batching_v1_5_compact_single_gate.tau`: mean `2679.05ms`
- `batching_v1_5_explained.tau`: mean `6194.95ms`

That means the compact batching rewrite is both:

- stronger than the baseline, because it also requires executed IDs to be
  distinct and the included/executed sets to match in both directions;
- materially faster in the current Tau runner, about 59% lower mean runtime in
  this one-step benchmark.

The explained batching variant is also stronger than the baseline and slightly
faster in this benchmark, but it remains much heavier than the compact form
because of its extra diagnostic outputs.

The swap and settlement families remain timeout-prone under the current Tau
runner with a `10s` per-case budget even after flattening and flag-gating, so
those results are currently inconclusive rather than wins.

## Trace-backed status

Execution-trace analysis is now built into this folder.

- Harness: `python3 experiments/tau_lang_optimizations/trace_harness.py`
- Regression test: `TAU_OPT_TRACE_TESTS=1 pytest -q tests/tau/test_tau_lang_optimization_experiment_traces.py`
- Latest harness report path:
  `generated/tau_lang_optimization_traces/report.json`

Current status:

- batching:
  - direct compact negative case is trace-backed,
  - direct explained diagnostic case is trace-backed,
  - direct compact positive case is too expensive as one Tau trace,
  - decomposed batching rails plus external join are trace-backed.
- swap:
  - proof-gated structural traces are backed,
  - the extra safe-range policy is backed as a separate Tau trace,
  - composed exact-in decisions are trace-backed.
- settlement:
  - price/order rails are backed,
  - module-flag bundle is backed,
  - aligned compact bundle is backed in spec mode,
  - composed rails+module decisions are trace-backed.

## Files

- `settlement_v5_aligned_inputs.tau`
  Aligned-input settlement composite. Removes duplicated warmup/base-case logic
  and uses same-step `prevprev/prev/curr` inputs.

- `settlement_v5_module_flags.tau`
  Compact settlement composite that keeps only canonical ordering, anti-
  sandwich, stability, and host/module flags inside Tau.

- `settlement_canonical_order_v1.tau`
  Tiny canonical ordering rail for settlement traces.

- `settlement_no_sandwich_aligned_v1.tau`
  Tiny aligned anti-sandwich rail.

- `settlement_price_stability_v1.tau`
  Tiny bounded price-move rail.

- `settlement_price_rails_aligned_v1.tau`
  Compact aligned rail bundle used in spec-mode traces.

- `settlement_module_flag_bundle_v1.tau`
  Compact non-price module/proof flag bundle.

- `settlement_v5_aligned_compact_bundle.tau`
  Compact aligned settlement bundle with one final output.

- `swap_exact_in_v5_hybrid_flags.tau`
  Exact-in swap validator with local structural checks plus host-computed proof
  flags for fee math and `k` monotonicity.

- `swap_exact_in_v5_compact_single_gate.tau`
  Compact exact-in variant with a single output gate and host proof flags.

- `swap_exact_out_v5_hybrid_flags.tau`
  Exact-out counterpart to the above.

- `swap_exact_out_v5_compact_single_gate.tau`
  Compact exact-out variant with a single output gate and host proof flags.

- `swap_bv32_safe_range_guard_v1.tau`
  Independent bv[32] range policy that can be composed with proof-gated swap
  traces.

- `swap_exact_in_v5_traceable_bundle.tau`
  Diagnostic exact-in bundle experiment. Still slower than the recommended
  proof-gated posture.

- `swap_exact_out_v5_traceable_bundle.tau`
  Diagnostic exact-out bundle experiment. Still slower than the recommended
  proof-gated posture.

- `batching_all_distinct_4_v1.tau`
  Tiny 4-way distinctness rail for compositional batching traces.

- `batching_left_in_right_4_v1.tau`
  Tiny 4-element membership rail for compositional batching traces.

- `batching_executed_sorted_4_v1.tau`
  Tiny strict ordering rail for compositional batching traces.

- `batching_v1_5_compact_single_gate.tau`
  Stronger-than-baseline batching validator with one output and no diagnostic
  fan-out. This is the current best production-shaped batching candidate.

- `batching_v1_5_explained.tau`
  More explicit batching validator that exposes distinctness, set equality, and
  ordering as separate outputs.

- `TAU_DEEP_INSIGHTS.md`
  Language-specific notes on parser quirks, normalization, operator families,
  output composition costs, and decomposition patterns.

- `TRACE_ANALYSIS.md`
  Trace-backed status, commands, composed-case reasoning, and artifact paths.

- `trace_cases.py`
  Curated hand-checked Tau trace cases for this experiment folder.

- `trace_harness.py`
  Standalone trace harness that records artifacts under `generated/`.

- `benchmark_specs.py`
  Harness to compare actual `run_tau_spec_steps` runtime for selected baseline
  and experimental specs. Timeout-prone cases are reported as inconclusive
  instead of aborting the whole run.

## Running

```bash
python3 experiments/tau_lang_optimizations/benchmark_specs.py
python3 experiments/tau_lang_optimizations/trace_harness.py
```

The harness uses the same Tau execution path the repo uses in practice and
reports `ok`, `timeout`, or `error` per case.
