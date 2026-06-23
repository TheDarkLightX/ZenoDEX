# Tau Optimization Trace Analysis

This folder now has trace-backed evidence for concrete experiment inputs.

## Commands

Run the standalone harness:

```bash
python3 experiments/tau_lang_optimizations/trace_harness.py
```

Run the gated regression test:

```bash
TAU_OPT_TRACE_TESTS=1 pytest -q tests/tau/test_tau_lang_optimization_experiment_traces.py
```

Artifacts are written to:

```text
generated/tau_lang_optimization_traces/
```

The harness summary is:

```text
generated/tau_lang_optimization_traces/report.json
```

## What is trace-backed now

### Batching

Positive batching is now established compositionally:

- `batching_all_distinct_4_v1.tau`
- `batching_left_in_right_4_v1.tau`
- `batching_executed_sorted_4_v1.tau`

Composed pass result:

- included distinct = `1`
- executed distinct = `1`
- executed in included = `1`
- included in executed = `1`
- executed sorted = `1`
- composed batch validity = `1`

Negative batching is also trace-backed directly:

- `batching_v1_5_compact_single_gate.tau` on a non-permutation trace returns `0`
- `batching_v1_5_explained.tau` exposes the expected diagnostic breakdown:
  - `o1=1`
  - `o2=1`
  - `o3=0`
  - `o4=0`
  - `o5=1`
  - `o6=0`

### Swap

The reliable posture is:

- use the proof-gated production swap specs for structure;
- use `swap_bv32_safe_range_guard_v1.tau` as a separate range policy;
- compose the final decision outside Tau.

Trace-backed cases:

- exact-in proof gate pass = `1`
- exact-in proof gate fail on slippage = `0`
- exact-in proof gate with large values = `1`
- safe-range guard on those same large values = `0`
- composed exact-in result on large values = `0`

This is the concrete demonstration that decomposition adds a meaningful safety
policy without forcing Tau to prove the whole stronger swap gate monolithically.

### Settlement

The reliable posture is:

- trace the price/order rails separately;
- trace the non-price module flags separately;
- use `settlement_v5_aligned_compact_bundle.tau` as the compact aligned bundle.

Trace-backed cases:

- canonical order pass/fail
- no-sandwich pass/fail
- price stability pass/fail
- module flag bundle pass/fail
- aligned compact bundle pass/fail
- composed rails+module pass/fail

## Current conclusion

There are now two evidence-backed upgrade patterns in this folder:

1. A direct runtime win:
- `batching_v1_5_compact_single_gate.tau`

2. A decomposition win:
- swap and settlement become tractable when split into small traceable Tau
  components plus an explicit external join.

The monolithic swap and settlement experiments are still useful as design
probes, but the decomposed bundles are the variants with real trace-backed
evidence today.
