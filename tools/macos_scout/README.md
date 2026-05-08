# MacOS Scout Tools

These tools prepare and run a local M3 Max scout campaign before using Runpod.
They are intentionally self-contained and write outputs under `internal/`.

## Quick Start

```bash
chmod +x tools/macos_scout/run_macos_scout.sh
bash tools/macos_scout/run_macos_scout.sh smoke
bash tools/macos_scout/run_macos_scout.sh scout
```

Modes:

- `smoke`: quick syntax/runtime check.
- `scout`: useful local campaign.
- `deep`: larger run suitable for an overnight Mac session.
- `soak`: maximum local CPU/memory campaign for the 128GB machine.

The launcher sets `OPENBLAS_NUM_THREADS=1`, `VECLIB_MAXIMUM_THREADS=1`, and
`OMP_NUM_THREADS=1` by default so Julia task threads get the CPU instead of
nested helper pools.

## Optional Metal Check

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl
```

If Metal.jl is missing:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl --install
```

Optional GPU prefilter:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_prefilter.jl --n 1000000 --out internal/macos_scout_runs/metal_prefilter
```

Set `RUN_METAL_PREFILTER=1` when calling `run_macos_scout.sh` if the local Metal
stack has passed smoke testing.

## Output Files

Each run writes:

- `summary.json`
- `summary.md`
- `all_scores.csv`
- `top_candidates.jsonl`
- `pareto_front.jsonl`
- `counterexamples.jsonl`
- `reranked_top_candidates.jsonl`
- `host_info.txt`

Review `counterexamples.jsonl` before reviewing top candidates.

## Promotion Rule

Promote only:

- counterexamples that can become public regression tests;
- candidate formulas that survive repeated seeds;
- mechanisms whose payout and burn flows are sourced from realized protocol
  activity and capped by explicit budgets.
