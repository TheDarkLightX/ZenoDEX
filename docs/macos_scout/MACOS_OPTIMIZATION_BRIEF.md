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
