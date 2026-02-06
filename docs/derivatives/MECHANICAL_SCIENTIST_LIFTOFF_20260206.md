# Mechanical Scientist Liftoff Report (2026-02-06)

## Summary

This iteration achieved two meaningful improvements while preserving strict fail-closed evidence rules:

1. Search-policy liftoff
- Promotions moved from archive fallback to `coverage_frontier` on new `grid:*` hypotheses.
- Campaign `measurement_coverage_iter_20260206_065217` promoted 4 hypotheses across 2 rounds, all strict-valid and non-archive.

2. Throughput liftoff
- Added hard wall timeout and parallel bundle execution to the mechanical-scientist loop.
- Matched A/B benchmark shows 3.06x faster wall-clock and 2.87x higher strict-valid coverage throughput.

## Implemented Changes

- `tools/mechanical_scientist_perps.py`
  - Added frontier metrics (`frontier_remaining`) and duration tracking (`duration_seconds`) per eval.
  - Added wrapper-level hard timeout handling (`campaign.hard_timeout_seconds`).
  - Added concurrent bundle execution (`campaign.max_parallel_bundles`).
  - Added campaign/round throughput metrics:
    - `elapsed_seconds`
    - `evaluations_per_minute`
    - `visited_per_second`
    - per-round elapsed/eval-rate/strict-rate totals
  - Maintains strict promotion gating (`strict_rate` requirements unchanged).

- `docs/derivatives/mechanical_scientist_perps_config.yaml`
  - Added defaults:
    - `max_parallel_bundles: 3`
    - `hard_timeout_seconds: 150`

- `tools/README.md`
  - Documented new timeout/parallel knobs and summary throughput metrics.

## Measurement Evidence

### Coverage liftoff run

- Run dir: `runs/morph/mechanical_scientist_perps/measurement_coverage_iter_20260206_065217`
- Results:
  - `total_evaluations`: 12
  - `total_unique_hypotheses_evaluated`: 6
  - `total_promotions`: 4
- Promotion reasons: all `coverage_frontier`
- Example promoted non-archive hypotheses:
  - `hyp:cc2f0272dcaf76ee` (`grid:solve_then_step:core`)
  - `hyp:5755d70d595abf10` (`grid:solve_step_solve:core`)
  - `hyp:3ba2b076acffd473` (`grid:solve_then_step:stress`)

### Throughput A/B (matched workload)

Sequential baseline:
- Run dir: `runs/morph/mechanical_scientist_perps/ab_seq_20260206_071018`
- `elapsed_seconds`: 208.93
- `evaluations_per_minute`: 1.72
- `visited_per_second`: 2224.14
- `strict_ok_rate`: 1.00

Parallel + hard-timeout:
- Run dir: `runs/morph/mechanical_scientist_perps/ab_par_20260206_071400`
- `elapsed_seconds`: 68.30
- `evaluations_per_minute`: 5.27
- `visited_per_second`: 6386.13
- `strict_ok_rate`: 1.00

Improvement:
- Wall-clock speedup: 3.06x
- Eval throughput: 3.06x
- Coverage throughput (`visited/s`): 2.87x

## Validation

- `python3.11 -m py_compile tools/mechanical_scientist_perps.py`
- `python3.11 -m py_compile tests/morph_perps_parity_domain.py`
- `bash tools/run_mechanical_scientist_evidence.sh`
  - quick campaign + strict replay passed (`failed: 0`)

## Remaining Gap

- No strict root `SOLVED` witness yet for perps parity.
- Current major progress is on search pressure and strict-valid throughput, not proof completion.

## Next Loop Hypothesis

Use the higher throughput budget to widen hypothesis generation (template/tactic composition and budget ladders) while keeping strict evidence gating fixed.

## Iteration 2 (DEX hardening + candidate diversity)

### 1) New stress primitives added to parity domain

Added high-stress macro primitives in `tests/morph_perps_parity_domain.py`:

- `BreakerPulse`
- `EpochWarpFlip`
- `InsuranceOscillation`

These are now available to the mechanical-scientist campaign via tactic packs.

### 2) Deterministic stress parity regression tests

Added `tests/core/test_perp_parity_stress_scenarios.py`:

- Replays seven stress traces directly against native and generated reference implementations.
- YAML parity checks are included but skipped when ESSO is not installed (fail-closed optional-toolchain behavior).

Latest run:
- `7 passed, 7 skipped`

### 3) Two-stage holdout scheduler (train-first, holdout top-K)

Implemented in `tools/mechanical_scientist_perps.py`:

- Evaluate all selected hypotheses on train seeds first.
- Rank by train coverage and strictness.
- Run holdout only for top-K hypotheses (`campaign.holdout_top_k`).
- Keep promotion fail-closed via `promotion.require_holdout_for_coverage`.

This is an optimization mode, not an unconditional default win.

#### A/B evidence (same evaluation budget target: 12 evals)

Baseline (all holdouts):
- Run dir: `runs/morph/mechanical_scientist_perps/ab_holdout_all_20260206_083349`
- `total_unique_hypotheses_evaluated`: 6
- `unique_hypotheses_per_minute`: 3.87
- `visited_per_second`: 11191.47

Top-K holdout (10 train candidates, holdout top 2):
- Run dir: `runs/morph/mechanical_scientist_perps/ab_holdout_top2_20260206_083534`
- `total_unique_hypotheses_evaluated`: 10
- `unique_hypotheses_per_minute`: 4.33
- `visited_per_second`: 10362.72

Tradeoff:
- `unique_hypotheses_per_minute`: **+11.8%**
- `unique_hypotheses_per_eval`: **+66.7%**
- `visited_per_second`: **-7.4%**

Interpretation:
- Top-K holdout improves exploration diversity and candidate turnover.
- Full holdout remains better for raw visited-throughput on this specific workload.

## Iteration 3 (long-budget policy decision + evidence hardening)

### 1) Long-budget policy A/B (matched 24-eval budget)

All-holdout policy:
- Run dir: `runs/morph/mechanical_scientist_perps/policy_all_holdout_long_20260206_101356`
- `total_evaluations`: 24
- `total_unique_hypotheses_evaluated`: 12
- `evaluations_per_minute`: 7.76
- `visited_per_second`: 14155.30
- `total_promotions`: 4

Top-K holdout policy (`holdout_top_k=2`):
- Run dir: `runs/morph/mechanical_scientist_perps/policy_topk_holdout_long_20260206_101718`
- `total_evaluations`: 24
- `total_unique_hypotheses_evaluated`: 12
- `evaluations_per_minute`: 5.20
- `visited_per_second`: 10200.35
- `total_promotions`: 0

Decision for this domain/config:
- Prefer **all-holdout** for long runs.
- Top-K holdout remains a niche mode for novelty-starved settings where hypothesis space is much larger than round budget.

### 2) DEX hardening landed

- Added stress scenario parity suite with invariant checks:
  - `tests/core/test_perp_parity_stress_scenarios.py`
  - Native-vs-ref parity over stress traces
  - Native invariant checks under accepted and rejected commands
  - Optional native-vs-YAML parity (ESSO-gated)

### 3) Evidence pipeline strengthened

Updated `tools/run_mechanical_scientist_evidence.sh` to run stress parity regression before campaign smoke:

- `14 passed, 7 skipped` (ESSO-dependent checks skipped when unavailable)
- quick campaign + strict replay still pass (`failed: 0`)
