# MacOS Scout Hardening Report - 2026-05-08

## Objective

Use the local M3 Max scout to reduce reachable ZenoDEX derivatives disaster
states before spending remote GPU budget. The result is bounded scout evidence,
not a production safety claim.

## Baseline Scout

Command:

```bash
JULIA_NUM_THREADS=auto bash tools/macos_scout/run_macos_scout.sh scout
```

Baseline run:

```text
internal/macos_scout_runs/20260508_172456_scout
```

Result:

```text
candidates = 50000
paths = 64
steps = 96
counterexamples = 50000
zero_disaster_legal_shape_candidates = 0
screen_seconds = 3.346308333
rerank_seconds = 0.064482042
```

Observed first-counterexample classes:

```text
liquidity_floor_breach_under_oracle_gap = 46732
funding_too_aggressive_in_thin_liquidity = 2665
payout_cap_exceeded_initial_budget = 603
```

Interpretation: the pre-hardening scout could find high-scoring formulas, but
every sampled candidate reached a disaster state under the full local scout
bounds. No mechanism candidate should be promoted from that run.

## Hardening Applied

The scout model now applies three fail-closed controls before a candidate can
avoid disaster accounting:

1. Oracle-gap/liquidity guard: when liquidity is below the candidate floor and
   the mark/oracle gap is material, payout-bearing risk transfer is blocked.
2. Initial epoch payout budget: payout caps bind to the initial epoch insurance
   budget instead of inflated current insurance.
3. Thin-liquidity funding clamp: funding is capped more tightly when executable
   liquidity is below the thin-liquidity bound.

The runner also emits a regression receipt:

```bash
python3 tools/macos_scout/check_scout_regression_gate.py \
  --run-dir internal/macos_scout_runs/<timestamp>_<mode>
```

The gate rejects unclassified scout disaster reasons and rejects any candidate
written to `promotion_candidates.jsonl` unless it passes the strict
no-disaster/legal-shape/guard-use criteria.

## Post-Hardening Evidence

First seed:

```text
internal/macos_scout_runs/20260508_173037_scout
candidates = 50000
counterexamples = 0
zero_disaster_legal_shape_candidates = 50000
regression_gate = accepted
strict_promotion_candidates = 0
```

Second seed:

```text
internal/macos_scout_runs/20260508_173056_scout
candidates = 50000
counterexamples = 0
zero_disaster_legal_shape_candidates = 50000
regression_gate = accepted
strict_promotion_candidates = 0
```

Deep run:

```text
internal/macos_scout_runs/20260508_173348_deep
candidates = 250000
paths = 96
steps = 128
counterexamples = 0
zero_disaster_legal_shape_candidates = 250000
screen_seconds = 29.576628833
rerank_seconds = 0.351331292
regression_gate = accepted
strict_promotion_candidates = 0
```

The two seeded 50k-candidate runs plus the 250k-candidate deep run show that
the three repeated baseline disaster classes are now blocked under these
bounded scout settings.

## Promotion Status

No formula is promoted. The best reranked candidates still rely too heavily on
emergency guards or fail the insurance-margin threshold used by the strict
promotion filter. They remain search evidence only.

## Witness-Space Reduction Receipt

The `what-if-witness-spaces` reduction pattern was applied to the hardened
macOS scout lane. The scout quotient keeps the gate-relevant observations:
oracle/liquidity guard, epoch payout budget, thin-liquidity funding clamp,
insurance solvency, and fee-budget legal shape.

Command:

```bash
python3 tools/macos_scout/build_witness_space_receipt.py \
  --run-dir internal/macos_scout_runs/20260508_173037_scout \
  --run-dir internal/macos_scout_runs/20260508_173056_scout \
  --run-dir internal/macos_scout_runs/20260508_173348_deep \
  --output internal/macos_scout_runs/witness_space_receipt_20260508.json
```

Receipt:

```text
gate = OPEN_FOR_BOUNDED_RESEARCH
stable_receipt_hash = sha256:dcb59ebe501770d0cec67953e838276668ddbe84dea8af3e76fd6b494f08710a
materialized_witness_count = 21
reachable_witness_count = 0
verdict_counts = {"NO_REACHABLE_WITNESS_BOUNDED": 21}
```

The pre-hardening baseline run blocks under the same witness-space gate:

```text
gate = BLOCKED_REACHABLE_WITNESS
reachable_witness_count = 17
```

Next promotion work should target lower guard-block rates and higher
min-insurance ratios, then rerun two-seed scout and deep campaigns before
drafting a Lean or SMT proof target.
