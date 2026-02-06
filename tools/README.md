# Tools

## Zeno Burn Demo (HTML)

Open in a browser:
```
open tools/zeno_burn_demo.html
```

This visualizes the Zeno-style burn: each step burns a fixed percentage of remaining supply.

## Tau Spec Runner (GUI)

Run:
```
python3 tools/tau_spec_runner_gui.py
```

- Choose a Tau binary (auto-detected if built in `external/tau-lang/build-Release/tau`).
- Choose a `.tau` spec.
- Paste input values line-by-line and run.

Note: Specs with long runs may take time; the GUI uses a 30s timeout.

## Perps Counterexample Miner (GPU)

Randomized, seedable counterexample mining for perp kernels using Torch MPS/CUDA (CPU fallback).

Run:
```
tools/esso/.venv/bin/python tools/mine_perps_ce_gpu.py --prefer-gpu --steps 2000 --batch 16384
```

## Perps Math Hazard Counterexamples (GPU)

Mines *math-level* counterexamples that justify "symmetric" constructions (abs+sign) and quantization-safe clamps.

Run:
```
tools/esso/.venv/bin/python tools/mine_perp_math_hazards_gpu.py --prefer-gpu --kind funding
tools/esso/.venv/bin/python tools/mine_perp_math_hazards_gpu.py --prefer-gpu --kind pnl
```

## Perps Mechanical Scientist Campaign

Runs a strict-gated Morph campaign over the perps parity domain and archives promoted hypotheses.

Run:
```
python3.11 tools/mechanical_scientist_perps.py campaign \
  --config docs/derivatives/mechanical_scientist_perps_config.yaml
```

Note: per-hypothesis run timeout is controlled via `campaign.run_timeout_seconds` in the config.
Use `campaign.hard_timeout_seconds` for a strict wall-clock kill in the wrapper, and `campaign.max_parallel_bundles` to run bundle evaluations concurrently.
Use `campaign.holdout_top_k` to evaluate all candidates on train seeds first, then run holdout only for the top-K train performers.
Promotion can be configured to require actual success outcomes (`SOLVED`) or to archive strict-valid high-coverage frontiers via `promotion.allow_coverage_frontier_promotion`.
Use `promotion.require_holdout_for_coverage: true` to ensure coverage promotions still include holdout validation.
Campaign telemetry now records `visited` and `frontier_remaining` per evaluation and surfaces aggregate coverage metrics in `round_aggregates.jsonl`.
`campaign_summary.json` now includes throughput metrics (`elapsed_seconds`, `evaluations_per_minute`, `unique_hypotheses_per_minute`, `visited_per_second`).

Replay strict doctor over a completed campaign:
```
python3.11 tools/mechanical_scientist_perps.py replay \
  --campaign-dir runs/morph/mechanical_scientist_perps/<campaign_timestamp>
```

Fail-closed evidence smoke:
```
bash tools/run_mechanical_scientist_evidence.sh
```
