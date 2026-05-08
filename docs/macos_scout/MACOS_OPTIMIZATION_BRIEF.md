# MacOS Optimization Brief

This package is intended for a 128GB M3 Max class Mac. The receiving agent
should actively tune the scout to use the machine, rather than treating the
defaults as final.

## Required First Checks

Run:

```bash
bash tools/macos_scout/run_macos_scout.sh smoke
```

Then inspect:

```text
internal/macos_scout_runs/<timestamp>_smoke/host_info.txt
internal/macos_scout_runs/<timestamp>_smoke/review.md
```

Confirm:

- Julia reports the expected thread count;
- the run used `Threads.@threads`;
- output files were written under `internal/`;
- counterexamples and top candidates are non-empty.
- `regression_gate.json` reports `status = accepted`, which means every
  observed counterexample reason is mapped to the tracked regression manifest
  and every strict promotion candidate satisfies the fail-closed budget gate.

## CPU Strategy

Use Julia thread parallelism as the main engine:

```bash
JULIA_NUM_THREADS=auto bash tools/macos_scout/run_macos_scout.sh scout
```

Avoid nested thread pools:

```bash
OPENBLAS_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1
OMP_NUM_THREADS=1
```

These are set by the launcher unless already overridden.

## Memory Strategy

The Mac's 128GB unified memory should be used for retained corpora and reranking,
not for unreviewed raw logs.

Preferred pattern:

```text
large candidate screen -> retain all scores -> retain first counterexample per candidate
  -> rerank top/Pareto candidates at higher path counts
  -> promote repeated counterexample reasons
```

Recommended runs:

```bash
bash tools/macos_scout/run_macos_scout.sh scout
bash tools/macos_scout/run_macos_scout.sh deep
```

If the machine remains responsive and memory pressure is low:

```bash
bash tools/macos_scout/run_macos_scout.sh soak
```

Manual tuning:

```bash
CANDIDATES=1000000 PATHS=96 STEPS=128 RERANK_TOP=500 RERANK_PATHS=768 RERANK_STEPS=256 \
  bash tools/macos_scout/run_macos_scout.sh soak
```

## GPU Strategy

Metal GPU acceleration is optional. It should be used as a prefilter or scoring
accelerator only after smoke testing.

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl
```

If the smoke test passes:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_prefilter.jl \
  --n 1000000 \
  --out internal/macos_scout_runs/metal_prefilter
```

Or let the launcher run it:

```bash
RUN_METAL_PREFILTER=1 METAL_PREFILTER_N=1000000 bash tools/macos_scout/run_macos_scout.sh scout
```

The current CPU path simulation remains the authoritative evidence path. The
Metal prefilter is a candidate generator and ranking accelerator.

## Profiling Requirement

For the first serious Mac run, record:

- wall-clock time;
- Julia thread count;
- candidate throughput;
- memory pressure from Activity Monitor;
- whether Metal.jl works;
- which mode best saturates the machine without swapping.

If CPU is underused, increase `CANDIDATES`, `PATHS`, or `RERANK_PATHS`.
If memory pressure is low, increase `CANDIDATES` and `RERANK_TOP`.
If the machine swaps, reduce `RERANK_TOP` or path counts first.

## Promotion Rule

Promote only after a second seed:

```bash
SEED=20260509 bash tools/macos_scout/run_macos_scout.sh scout
```

A candidate that fails on the second seed becomes a counterexample class, not a
mechanism claim.

## Hardening Gate

Every local run now writes a regression-gate receipt:

```bash
python3 tools/macos_scout/check_scout_regression_gate.py \
  --run-dir internal/macos_scout_runs/<timestamp>_<mode>
```

The gate is intentionally narrow. It does not prove a mechanism safe; it blocks
two unsafe workflow failures:

- a new simulator disaster reason appears without being classified in
  `tools/macos_scout/scout_regression_manifest.json`;
- a candidate is promoted despite nonzero disaster rate, illegal fee/payout
  shape, underfunded insurance, or excessive reliance on emergency guards.

## Witness-Space Reduction

The `what-if-witness-spaces` method reduces disaster-state work by choosing a
quotient that preserves gate-relevant observations, then checking every
materialized witness in that quotient with deterministic receipts. The scout
translation is:

```bash
python3 tools/macos_scout/build_witness_space_receipt.py \
  --run-dir internal/macos_scout_runs/<timestamp>_<mode>
```

The receipt uses `tools/macos_scout/witness_space_atlas.json` to materialize
single-surface, edge-composition, order-inversion, terminal-chain, fan-out,
convergence, re-entry, cycle-amplification, and independent co-reachability
witnesses for the scout disaster classes. It opens only when all supplied run
directories have zero reachable counterexamples, the regression gate accepts,
synthetic fail-closed mutations reject as expected, and release runs using
`--require-clean` have no dirty gate-critical checker or atlas paths. The
bounded graph frontier is recorded in the receipt, while independent
co-reachability above the materialized order is kept as a compressed frontier
count rather than expanded into raw witness rows.
