# ZenoDEX MacOS Scout Handoff

This file is the starting prompt for a fresh Codex session on the Mac.

## Objective

Use the 128GB Apple Silicon Mac as the first compute target before spending Runpod
budget. The goal is to run deterministic local scout campaigns that reduce
ZenoDEX, ZenoOracle, and ZenoProof disaster states, with first focus on:

- derivatives mechanism search;
- yield-like funding shapes that are sourced from realized protocol activity;
- proof-mining and payout boundary regressions;
- stress paths that expose liquidation, oracle-delay, insurance, or funding
  disasters.

Treat every result as bounded evidence. Do not claim a design is safe because a
scout run did not find a counterexample.

## Machine Assumption

Expected machine: MacBook Pro with M3 Max, 16-core CPU, 40-core GPU, and 128GB
unified memory. Apple documents the 128GB option for M3 Max with the 16-core CPU,
and the 40-core GPU variant has 400GB/s memory bandwidth.

Primary source links:

- https://support.apple.com/en-us/117736
- https://www.apple.com/newsroom/2023/10/apple-unveils-m3-m3-pro-and-m3-max-the-most-advanced-chips-for-a-personal-computer/
- https://metal.juliagpu.org/stable/
- https://metal.juliagpu.org/stable/usage/overview/

## First Commands

From the repo root:

```bash
chmod +x tools/macos_scout/run_macos_scout.sh
bash tools/macos_scout/run_macos_scout.sh smoke
```

If the smoke run passes:

```bash
bash tools/macos_scout/run_macos_scout.sh scout
```

For a larger overnight run:

```bash
bash tools/macos_scout/run_macos_scout.sh deep
```

Optional Metal GPU check:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl
```

If Metal.jl is not installed and you want to test it:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl --install
```

## Output Location

Runs write to:

```text
internal/macos_scout_runs/<timestamp>/
```

Expected files:

- `summary.json`
- `summary.md`
- `all_scores.csv`
- `top_candidates.jsonl`
- `pareto_front.jsonl`
- `counterexamples.jsonl`
- `host_info.txt`

`internal/` is git-ignored. Promote only distilled, replayable artifacts into
public tracked files after review.

## Review Rules

Use this filter before promoting a candidate:

```text
CandidateOK :=
  no_disaster_under_bounds
  and payout_source_is_realized_activity
  and burn_or_treasury_flow_is_capped
  and no_fixed_passive_return_claim
  and replay_script_reproduces_metrics
```

The practical reading is that a candidate can advance only when its funding or
deflationary pressure is tied to realized fees, spread, liquidation penalty, or
explicit work output, with caps and replayable evidence.

## What To Do After A Run

1. Read `summary.md`.
2. Inspect `counterexamples.jsonl` first.
3. Re-run top candidates with a different seed.
4. Promote regressions for any counterexample class.
5. Promote only candidate formulas that survive two seeds and have clear
   bounded assumptions.
6. Write a short public note only after the mechanism has a replay script and a
   formal proof target.

## Do Not Do

- Do not commit raw internal run directories.
- Do not claim legal compliance from the math scout.
- Do not treat Metal.jl as required for progress.
- Do not use private keys, production credentials, or live treasury data.
