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
- `review.md`
- `all_scores.csv`
- `top_candidates.jsonl`
- `pareto_front.jsonl`
- `counterexamples.jsonl`
- `reranked_top_candidates.jsonl`
- `reason_counts.json`
- `promotion_candidates.jsonl`
- `regression_gate.json`
- `witness_space_receipt.json`
- `host_info.txt`

Review `counterexamples.jsonl` before reviewing top candidates.

The launcher also runs:

```bash
python3 tools/macos_scout/check_scout_regression_gate.py --run-dir <outdir>
```

That gate fails closed if a scout run emits a counterexample reason not tracked
in `tools/macos_scout/scout_regression_manifest.json`, or if a candidate is
written to `promotion_candidates.jsonl` without satisfying the strict
no-disaster/legal-shape budget checks.

The launcher also builds a compact what-if witness-space receipt:

```bash
python3 tools/macos_scout/build_witness_space_receipt.py --run-dir <outdir>
```

That receipt applies the `what-if-witness-spaces` pattern to the scout lane:
materialize named surface, edge, terminal-chain, fan-out, convergence, re-entry,
cycle, and independent co-reachability witnesses from
`tools/macos_scout/witness_space_atlas.json`, record the bounded graph frontier,
count the compressed independent frontier, run synthetic fail-closed checks, and
emit a stable receipt hash.

For release evidence, include a blocked witness run:

```bash
python3 tools/macos_scout/build_witness_space_receipt.py \
  --run-dir tests/fixtures/macos_scout/post_hardening_zero \
  --blocked-run-dir tests/fixtures/macos_scout/pre_hardening_blocked \
  --require-clean
```

The blocked run ratchets the repeat-regression surfaces: they must be witnessed
as reachable in the blocked fixture and absent from the current hardened run.

## Promotion Rule

Promote only:

- counterexamples that can become public regression tests;
- candidate formulas that survive repeated seeds;
- mechanisms whose payout and burn flows are sourced from realized protocol
  activity and capped by explicit budgets.
