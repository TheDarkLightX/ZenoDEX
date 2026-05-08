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

## Optional Metal Check

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl
```

If Metal.jl is missing:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl --install
```

## Output Files

Each run writes:

- `summary.json`
- `summary.md`
- `all_scores.csv`
- `top_candidates.jsonl`
- `pareto_front.jsonl`
- `counterexamples.jsonl`
- `host_info.txt`

Review `counterexamples.jsonl` before reviewing top candidates.

## Promotion Rule

Promote only:

- counterexamples that can become public regression tests;
- candidate formulas that survive repeated seeds;
- mechanisms whose payout and burn flows are sourced from realized protocol
  activity and capped by explicit budgets.
