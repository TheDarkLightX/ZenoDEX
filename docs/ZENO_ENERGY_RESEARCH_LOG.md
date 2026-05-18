# ZenoEnergy Research Log

Date: 2026-05-17

This log records bounded ZenoEnergy evidence and negative knowledge that should
guide later scorer work.

## Set-Aware Linear Comparison

Artifact:
[ZENO_ENERGY_SET_AWARE_COMPARISON.md](./ZENO_ENERGY_SET_AWARE_COMPARISON.md)

Static JSON:
`data/upba_energy/upba_v2_energy_set_aware_compare_120x80_seed20260523_20260524.json`

Command:

```bash
python3 tools/compare_upba_energy_set_aware.py \
  --train-batches 120 \
  --holdout-batches 80 \
  --candidates-per-batch 20 \
  --train-seed 20260523 \
  --holdout-seed 20260524 \
  --epochs 6 \
  --learning-rate 0.03 \
  --output-json data/upba_energy/upba_v2_energy_set_aware_compare_120x80_seed20260523_20260524.json \
  --output-markdown docs/ZENO_ENERGY_SET_AWARE_COMPARISON.md \
  --output-model-dir data/upba_energy
```

Observed result:

| model | top1 | top5 | top10 | mean verifier calls | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| aggregate learned | 0.9625 | 1.0000 | 1.0000 | 1.0375 | 2 | 0 |
| set-aware learned | 0.9500 | 1.0000 | 1.0000 | 1.0625 | 2 | 0 |

Negative knowledge:

```text
Extra set-aware moment features did not improve the current linear ranker on
this bounded synthetic comparison. Keep the aggregate gap-weighted checkpoint as
the measured default until cross-seed evidence supports a change.
```

Research consequence: set-aware features need stronger cross-seed evidence,
regularization, a nonlinear scorer, or a hard-case-focused objective before
promotion.

## Gap-Weighted Default

Artifacts:
[ZENO_ENERGY_GAP_WEIGHTED_STRESS.md](./ZENO_ENERGY_GAP_WEIGHTED_STRESS.md),
[ZENO_ENERGY_GAP_WEIGHTED_HARD_CASES.md](./ZENO_ENERGY_GAP_WEIGHTED_HARD_CASES.md),
[ZENO_ENERGY_MODEL_AUDIT.md](./ZENO_ENERGY_MODEL_AUDIT.md)

Static JSON:
`data/upba_energy/upba_v2_energy_gap_weighted_cross_seed_stress_250x3x3.json`,
`data/upba_energy/upba_v2_energy_gap_weighted_hard_cases_500x3x3.json`,
`data/upba_energy/upba_v2_energy_gap_weighted_model_audit.json`

Observed cross-seed aggregate:

| model | configs | top1 mean | top10 min | mean verifier calls | p99 max | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| hand energy | 9 | 0.7819 | 1.0000 | 1.3261 | 5 | 0 |
| gap-weighted learned | 9 | 0.9825 | 1.0000 | 1.0175 | 2 | 0 |

Observed hard-case aggregate:

| batches with winner | top1 | top5 | top10 | top5 misses | top10 misses | max p99 winner position |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4,466 | 0.9854 | 1.0000 | 1.0000 | 0 | 0 | 2 |

Positive knowledge:

```text
The gap-weighted learned linear scorer is the current measured default. It
keeps the verifier authoritative, has zero invalid accepts in the replayed
bounded artifacts, preserves top-10 recall, and improves mean verifier calls
over hand energy on the nine-config cross-seed stress run.
```

Residual limit:

```text
This is still bounded synthetic evidence. Promotion requires real or
production-shadow candidate distributions, adversarial distribution-shift
tests, and the deterministic fallback/certificate path remaining available.
```

Research consequence: use the gap-weighted linear checkpoint as the baseline
for future ranker and repair-selector experiments. Record a stronger model only
if it beats this baseline under the same replay gate and preserves zero invalid
accepts.

## AutoTraderEnergy Hard Cross-Seed

Artifact:
[AUTOTRADER_ENERGY_HARD_CROSS_SEED.md](./AUTOTRADER_ENERGY_HARD_CROSS_SEED.md)

Static JSON:
`data/upba_energy/autotrader_energy_hard_cross_seed_3x_seed20260522_20260527.json`

Command:

```bash
python3 tools/benchmark_autotrader_energy_cross_seed.py \
  --profile hard \
  --train-contexts 2500 \
  --holdout-contexts 1000 \
  --candidates-per-context 16 \
  --epochs 6 \
  --learning-rate 0.001 \
  --margin 1.0 \
  --init hand \
  --seed-pairs 20260522:20260523,20260524:20260525,20260526:20260527 \
  --output-json data/upba_energy/autotrader_energy_hard_cross_seed_3x_seed20260522_20260527.json \
  --output-markdown docs/AUTOTRADER_ENERGY_HARD_CROSS_SEED.md
```

Observed aggregate:

| mode | mean guard calls | top1 mean | top5 min | invalid accepts |
| --- | ---: | ---: | ---: | ---: |
| random | 8.393 | 0.066 | 0.302 | 0 |
| hand energy | 4.312 | 0.217 | 0.680 | 0 |
| learned energy | 1.010 | 0.990 | 1.000 | 0 |

Positive knowledge:

```text
The hard synthetic AutoTraderEnergy scorer reduced guard calls on every
evaluated seed pair while preserving deterministic policy-guard authority.
```

Residual limit:

```text
This is synthetic pre-production evidence. Real value still depends on
production-shadow observations with live-like strategy proposals, market
states, policy bundles, and rejected action candidates.
```

Research consequence: the ZenoEnergy pattern transfers cleanly to AutoTrader as
an advisory ordering layer for deterministic policy guards. The next useful
step is a shadow-data replay that compares learned order against real rejected
and accepted AutoTrader candidate plans.

## AutoTraderEnergy Shadow Bridge

Artifact:
[AUTOTRADER_ENERGY_SHADOW_BRIDGE.md](./AUTOTRADER_ENERGY_SHADOW_BRIDGE.md)

Static JSON:
`data/upba_energy/autotrader_energy_shadow_bridge_baseline_seed20260528.json`

Command:

```bash
python3 tools/evaluate_autotrader_energy_shadow_bridge.py \
  --synthetic-train-contexts 1500 \
  --candidates-per-context 16 \
  --train-seed 20260528 \
  --epochs 5 \
  --learning-rate 0.001 \
  --margin 1.0 \
  --output-json data/upba_energy/autotrader_energy_shadow_bridge_baseline_seed20260528.json \
  --output-markdown docs/AUTOTRADER_ENERGY_SHADOW_BRIDGE.md
```

Observed result:

| mode | mean guard calls | objective guard calls | exact top1 | objective top1 | top5 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 3.250 | 2.000 | 0.250 | 0.500 | 1.000 | 0 |
| hand energy | 2.000 | 1.000 | 0.000 | 1.000 | 1.000 | 0 |
| learned energy | 2.000 | 1.000 | 0.000 | 1.000 | 1.000 | 0 |

Positive knowledge:

```text
The shadow bridge converts recorded ZenoGraph AutoTrader observations into the
same advisory row schema and keeps deterministic policy guards authoritative.
The fixture is nonvacuous, with 4 contexts, 20 rows, 12 valid candidates, 8
invalid candidates, and zero invalid accepts. Objective-equivalent argmax
recall is 1.000 for hand and learned ordering because the first checked valid
candidate is in the tied maximum-objective class.
```

Negative knowledge:

```text
The built-in shadow bridge is a deterministic fixture derived from accepted
ZenoGraph store exports. It is useful for schema and boundary replay, but it is
not live production distribution evidence. Exact top1 recall is 0.0 for hand
and learned ordering because the exact winner is a hash-selected representative
inside a tied valid argmax class.
```

Research consequence: the next AutoTraderEnergy improvement should train and
evaluate on larger recorded shadow corpora with multiple candidate plans per
decision context and report both exact-winner and objective-equivalence metrics.
The current bridge is ready for that data, but it should stay below the policy
guard boundary.

## Listwise Set Ranker

Artifact:
[ZENO_ENERGY_LISTWISE_SET_RANKER.md](./ZENO_ENERGY_LISTWISE_SET_RANKER.md)

Static JSON:
`data/upba_energy/upba_v2_energy_listwise_set_ranker_seed20260532_20260533.json`

Model:
`data/upba_energy/upba_v2_energy_listwise_set_ranker.json`

Command:

```bash
python3 tools/compare_upba_energy_listwise_set_ranker.py \
  --train-batches 120 \
  --holdout-batches 80 \
  --candidates-per-batch 24 \
  --train-seed 20260532 \
  --holdout-seed 20260533 \
  --pairwise-epochs 6 \
  --listwise-epochs 10 \
  --pairwise-learning-rate 0.03 \
  --listwise-learning-rate 0.08 \
  --l2 0.0001 \
  --output-json data/upba_energy/upba_v2_energy_listwise_set_ranker_seed20260532_20260533.json \
  --output-markdown docs/ZENO_ENERGY_LISTWISE_SET_RANKER.md \
  --output-model-dir data/upba_energy
```

Observed result:

| model | top1 | top5 | top10 | mean verifier calls | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| aggregate pairwise | 0.987 | 1.000 | 1.000 | 1.026 | 1 | 0 |
| set-aware pairwise | 0.987 | 1.000 | 1.000 | 1.026 | 1 | 0 |
| listwise set | 0.947 | 1.000 | 1.000 | 1.066 | 2 | 0 |

Positive knowledge:

```text
The listwise set-context ranker preserved top-10 recall, had zero invalid
accepts, zero permutation violations, and checked-stop-at-winner rate 1.0.
```

Negative knowledge:

```text
The first listwise set-context ranker did not improve mean verifier calls
against the strongest pairwise baseline on this bounded synthetic split.
```

Research consequence: listwise training is now wired into the replay harness,
but the current linear context feature set is unpromoted. The next listwise
attempt needs either nonlinear scoring, outcome-weighted list labels, or a
hard-case-focused train split.

## Listwise Cross-Seed Stress

Artifact:
[ZENO_ENERGY_LISTWISE_SET_RANKER_CROSS_SEED.md](./ZENO_ENERGY_LISTWISE_SET_RANKER_CROSS_SEED.md)

Static JSON:
`data/upba_energy/upba_v2_energy_listwise_set_ranker_cross_seed_seed20260532_20260537.json`

Command:

```bash
python3 tools/stress_upba_energy_listwise_set_ranker.py \
  --train-batches 80 \
  --holdout-batches 60 \
  --candidates-per-batch 24 \
  --pairwise-epochs 6 \
  --listwise-epochs 10 \
  --pairwise-learning-rate 0.03 \
  --listwise-learning-rate 0.08 \
  --l2 0.0001 \
  --seed-pairs 20260532:20260533,20260534:20260535,20260536:20260537 \
  --output-json data/upba_energy/upba_v2_energy_listwise_set_ranker_cross_seed_seed20260532_20260537.json \
  --output-markdown docs/ZENO_ENERGY_LISTWISE_SET_RANKER_CROSS_SEED.md
```

Observed aggregate:

| model | top1 mean | top10 mean | mean verifier calls | p99 mean |
| --- | ---: | ---: | ---: | ---: |
| aggregate pairwise | 0.9828 | 1.0000 | 1.0172 | 1.0000 |
| set-aware pairwise | 0.9259 | 1.0000 | 1.0741 | 2.0000 |
| listwise set | 0.9319 | 1.0000 | 1.0681 | 2.0000 |

Positive knowledge:

```text
The listwise set ranker preserved top-10 recall and checked-stop-at-winner
audits on every seed pair with zero invalid accepts and zero permutation
violations.
```

Negative knowledge:

```text
The listwise set ranker did not strictly improve over the best pairwise baseline
on every seed pair.
```

Research consequence: this strengthens the unpromoted status of the current
linear listwise formulation. The next listwise attempt should change the model
class or the training signal rather than only adding more identical seed pairs.

## Neighborhood Repair Baseline

Artifact:
[ZENO_ENERGY_NEIGHBORHOOD_REPAIR.md](./ZENO_ENERGY_NEIGHBORHOOD_REPAIR.md)

Static JSON:
`data/upba_energy/upba_v2_energy_neighborhood_benchmark_seed20260525.json`

Command:

```bash
python3 tools/benchmark_upba_energy_neighborhood.py \
  --batches 80 \
  --candidates-per-batch 24 \
  --candidate-budget 6 \
  --repair-seed-count 4 \
  --max-proposals-per-seed 6 \
  --seed 20260525 \
  --order-mode hand \
  --output-json data/upba_energy/upba_v2_energy_neighborhood_benchmark_seed20260525.json \
  --output-markdown docs/ZENO_ENERGY_NEIGHBORHOOD_REPAIR.md
```

Observed result:

| mode | candidates | added | full winner present | best dominates full winner | mean calls | mean volume regret | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 6.0000 | 0.0000 | 0.2125 | 0.2125 | 4.9500 | 278.3375 | 0 |
| neighborhood | 15.9000 | 9.9000 | 0.2750 | 0.9500 | 12.6125 | 4.7000 | 0 |

Positive knowledge:

```text
Deterministic neighborhood proposals sharply reduce best-valid volume regret in
this limited-budget synthetic benchmark, and the best verifier-accepted
augmented candidate weakly dominates the original full-list winner in 95% of
batches.
```

Negative knowledge:

```text
The neighborhood generator adds verifier work. It increases mean calls from
4.95 to 12.61 in this benchmark and is not an exact bounded-grid certificate by
itself.
```

Research consequence: the next repair-policy question is whether a tiny learned
selector can keep most of the regret reduction while proposing fewer repairs.

## Learned Repair Selector

Artifact:
[ZENO_ENERGY_REPAIR_SELECTOR.md](./ZENO_ENERGY_REPAIR_SELECTOR.md)

Static JSON:
`data/upba_energy/upba_v2_energy_repair_selector_benchmark_seed20260526_20260527.json`

Model:
`data/upba_energy/upba_v2_repair_selector_linear_seed20260526.json`

Command:

```bash
python3 tools/benchmark_upba_repair_selector.py \
  --train-batches 120 \
  --holdout-batches 80 \
  --candidates-per-batch 24 \
  --candidate-budget 6 \
  --proposal-budget 2 \
  --repair-seed-count 4 \
  --max-proposals-per-seed 6 \
  --step-denominator 4 \
  --epochs 10 \
  --learning-rate 0.05 \
  --margin 1.0 \
  --train-seed 20260526 \
  --holdout-seed 20260527 \
  --output-model data/upba_energy/upba_v2_repair_selector_linear_seed20260526.json \
  --output-json data/upba_energy/upba_v2_energy_repair_selector_benchmark_seed20260526_20260527.json \
  --output-markdown docs/ZENO_ENERGY_REPAIR_SELECTOR.md
```

Observed result:

| mode | candidates | added | best dominates full winner | mean calls to dominance | mean calls to full winner | mean volume regret | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 6.0000 | 0.0000 | 0.2250 | 4.8750 | 4.8750 | 271.4750 | 0 |
| full_neighborhood | 16.2750 | 10.2750 | 0.9625 | 1.6750 | 12.8750 | 3.2000 | 0 |
| hand_selected | 8.0000 | 2.0000 | 0.9625 | 1.3500 | 6.5875 | 3.2000 | 0 |
| learned_selected | 8.0000 | 2.0000 | 0.9625 | 1.3125 | 6.6500 | 3.2000 | 0 |

Positive knowledge:

```text
Two selected repair proposals preserve the full-neighborhood mean volume regret
and weak-dominance rate on this held-out synthetic seed, while reducing mean
candidate count from 16.275 to 8.000.
```

Negative knowledge:

```text
The learned selector does not strictly beat the hand-selected two-proposal
subset on mean volume regret in this run. The current deterministic repair
recipes are easy enough that hand energy remains a strong selector baseline.
```

Research consequence: use the selector as a compact benchmark harness for
future learned repair policies. Promotion needs cross-seed replay and a stricter
win over the hand-selected proposal subset.

## Repair Selector Cross-Seed Stress

Artifact:
[ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md](./ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md)

Static JSON:
`data/upba_energy/upba_v2_repair_selector_cross_seed_seed20260526_20260531.json`

Command:

```bash
python3 tools/stress_upba_repair_selector.py \
  --train-batches 80 \
  --holdout-batches 60 \
  --candidates-per-batch 24 \
  --candidate-budget 6 \
  --proposal-budget 2 \
  --repair-seed-count 4 \
  --max-proposals-per-seed 6 \
  --step-denominator 4 \
  --epochs 8 \
  --learning-rate 0.05 \
  --margin 1.0 \
  --seed-pairs 20260526:20260527,20260528:20260529,20260530:20260531 \
  --output-json data/upba_energy/upba_v2_repair_selector_cross_seed_seed20260526_20260531.json \
  --output-markdown docs/ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md
```

Aggregate result:

| metric | value |
| --- | ---: |
| compression_pass_count | 3 |
| compression_fail_count | 0 |
| strict_hand_win_count | 1 |
| strict_hand_win_fail_count | 2 |
| invalid_accept_count | 0 |
| original_subset_violation_count | 0 |

Mean across seed pairs:

| mode | candidates | added | best dominates full winner | calls to dominance | calls to full winner | volume regret |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 6.0000 | 0.0000 | 0.2547 | 4.7381 | 4.7381 | 285.4150 |
| full_neighborhood | 16.3211 | 10.3211 | 0.9434 | 1.9906 | 12.2533 | 5.9369 |
| hand_selected | 8.0000 | 2.0000 | 0.9434 | 1.4814 | 6.4166 | 6.2477 |
| learned_selected | 8.0000 | 2.0000 | 0.9434 | 1.4416 | 6.4102 | 5.9369 |

Positive knowledge:

```text
The learned selector compressed full neighborhood expansion on all three
train/holdout seed pairs while preserving full-neighborhood mean volume regret
and weak-dominance rate.
```

Negative knowledge:

```text
The learned selector strictly beat the hand-selected two-proposal subset on only
one of three seed pairs. Hand-selected repair remains a strong baseline.
```

Research consequence: the repair selector is useful as a proposal-budget
compression tool. The next model objective should target a stronger hand-baseline
win, probably by adding listwise proposal-set features or training directly on
the chosen two-proposal subset outcome.

## Repair Selector Formal Boundary

Lean target:
`lean-mathlib/Proofs/UniformBatchOptimality.lean`

New theorem names:

```text
def AdvisorySelectedRepairSet
theorem advisory_selected_repair_set_implies_candidate_subset
theorem advisory_selected_repair_set_upper_bound_certificate_implies_base_weak_optimal
```

Command:

```bash
cd lean-mathlib && lake env lean Proofs/UniformBatchOptimality.lean
```

Focused regression:

```bash
pytest -q tests/formal/test_lean_uniform_batch_optimality.py
```

Meaning: a learned or hand-selected repair proposal subset is formally safe as
an advisory selector when it preserves the base candidate list and the
deterministic verifier supplies the upper-bound certificate over the selected
set. The theorem proves weak optimality over the preserved base list only. A
global bounded-grid claim still needs exact full fallback, a dominance cover, or
another exactness certificate.

## Fallback And Checked-Stop Formal Boundary

Artifact:
[ZENO_ENERGY_FALLBACK_CHECKED_STOP_FORMAL.md](./ZENO_ENERGY_FALLBACK_CHECKED_STOP_FORMAL.md)

Static JSON:
`data/upba_energy/upba_v2_fallback_checked_stop_formal_receipt.json`

Commands:

```bash
cd lean-mathlib && lake env lean Proofs/UniformBatchOptimality.lean
pytest -q tests/formal/test_lean_uniform_batch_optimality.py
```

Observed result:

| command | result |
| --- | --- |
| `lake env lean Proofs/UniformBatchOptimality.lean` | pass |
| `pytest -q tests/formal/test_lean_uniform_batch_optimality.py` | pass |

The formal receipt records the full-fallback and checked-stop theorem names:

```text
def FullFallbackEquivalentOrder
theorem full_fallback_equivalent_order_preserves_membership_iff
theorem full_fallback_equivalent_order_preserves_weak_optimality_iff
def CheckedStopCertificate
theorem checked_stop_certificate_with_exact_full_implies_global_weak_optimal
theorem upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
theorem upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
theorem upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
```

Research consequence: ranked search has a precise formal boundary. Full
fallback needs a permutation of the exact finite candidate list. Checked early
stop needs dominance over both the checked prefix and unchecked suffix, plus the
exact finite candidate family premise. Top-k recall remains empirical evidence
unless those proof obligations are supplied.

## SOTA Decision Map

Artifact:
[ZENO_ENERGY_SOTA_DECISION_MAP.md](./ZENO_ENERGY_SOTA_DECISION_MAP.md)

Static JSON:
`data/upba_energy/upba_v2_sota_decision_map_receipt.json`

The decision map ties current energy-model, set-ranking, and solver-learning
literature to concrete ZenoEnergy experiments. It records these decisions:

```text
full generative EBM: defer
pairwise linear ranking: keep as baseline
listwise set ranker: test next
larger transformer: defer
learned repair selector: continue
top-k without fallback: reject
online checked stop: prototype only with suffix-bound certificate
```

Research consequence: the next high-value experiments are a listwise set ranker,
an outcome-level repair selector, refreshed hard negatives, and a
dominance-cover certificate prototype. The map is guidance for the research
queue. It does not change the verifier-authoritative settlement boundary.

## Research Evidence Replay Gate

Artifact:
[ZENO_ENERGY_RESEARCH_EVIDENCE_REPLAY.md](./ZENO_ENERGY_RESEARCH_EVIDENCE_REPLAY.md)

Static JSON:
`data/upba_energy/zenoenergy_research_evidence_replay_receipt.json`

Command:

```bash
python3 tools/check_zenoenergy_research_evidence.py \
  --output-json data/upba_energy/zenoenergy_research_evidence_replay_receipt.json \
  --output-markdown docs/ZENO_ENERGY_RESEARCH_EVIDENCE_REPLAY.md
```

Observed result after adding AutoTraderEnergy hard cross-seed checks:

| checks | passed | failed |
| ---: | ---: | ---: |
| 83 | 83 | 0 |

The gate checks that the committed set-aware, neighborhood, repair-selector,
listwise set-ranker, listwise cross-seed, gap-weighted default, cross-seed,
AutoTraderEnergy hard cross-seed, formal-boundary, fallback/top-k, SOTA
decision-map, and PopperPad doctor evidence still support the current research
story. It also preserves negative knowledge: set-aware linear features have no
measured win over the aggregate ranker, the listwise set-context ranker has no
measured mean-call win, the listwise cross-seed run does not strictly improve
over the best pairwise baseline, deterministic neighborhood expansion reduces
regret while increasing verifier work, and the learned repair selector has not
consistently beaten the hand-selected two-proposal subset.

Research consequence: future ZenoEnergy changes should update this replay gate
when they promote or retire a research claim. A failing gate means either the
underlying receipt changed, PopperPad status drifted, or the current summary is
overstating the recorded evidence.

## PopperPad Refs

Pad: `internal/popperpad/zenoenergy`

```text
domain_ref:                 sha256:491ffd61981b5fa5b0ca2e54afc3fea3b80bb75ac5d923176dae8063ddd9d82b
context_ref:                sha256:1ef45b750735a7c69c8c60de46065dca43e60935405692f903986615c658e8ed
report_artifact_ref:        sha256:0e7b79069af9d8b319fe877c8a7f0deb96db35a8dc2a56826872eec0cc6f78bd
negative_artifact_ref:      sha256:b56a3bdbcb41292230ee5bfc3fb52b1d569199a97b59e113cfd22a388137f897
safety_hypothesis_ref:      sha256:0bce1eec24d7cad22fdaeba989fac2c33d88bcc48cfa6bd2a931af2d57060b77
improvement_hypothesis_ref: sha256:08b6bfc25d399d08567099e49b8b8624f3e5737ca265d6ef761c1da2d4bbe6a7
checkpoint_ref:             sha256:552ced0c5ce4e38d8a2fd66b74f41da4edfe56c993db8a4fd36c1725fca890b6
```

Neighborhood repair refs:

```text
context_ref:                sha256:8e4a85c00f00f65d1794f3acce81c90467496d1e7326b202f4f7937324d66106
report_artifact_ref:        sha256:729beed3a979fe8dd66689e6dd6f876bea6b54363c8ea4f602b1e524e5df7bc1
note_artifact_ref:          sha256:224f626747e30f2aadc85174020ce58d9a11e1d810281bc40032978c69b990c6
safety_hypothesis_ref:      sha256:98380edb22a5e4a45d683312409f89dea54c3a50e18a94fe373ca85fbe1367fc
regret_hypothesis_ref:      sha256:d84a675f6fd352db15f6156c37fa55926cad09c3853deb639c76171c9b22bc47
call_cost_hypothesis_ref:   sha256:c46675b22a8f09f0a3caa7cfadbcb3a9320e8654b6d31c3c64b6b0acdd066039
checkpoint_ref:             sha256:997899ef79e597d9058230d79d5ee2a847c026fa11bf0013a8673dc81100e2a9
```

Repair selector refs:

```text
context_ref:                sha256:423e05436ade42ffacfc2d8e6f5c80737b66389b5ba61e2441b2648dbd05f2ae
report_artifact_ref:        sha256:a333de8eb3f573a7270ba724406a847eea3366bc347b35d5759dfdebf8f59922
markdown_artifact_ref:      sha256:f43edf5accf668b559fb54c20d123fe57034e35660e5ebe4982a49b9777bf86e
model_artifact_ref:         sha256:9a51f33e40af1f1df3d75e784a2c6d5241258a23f955f5cb39b689fbddea10ea
safety_hypothesis_ref:      sha256:cc2d3f85bb83e5efb445fd0b2e20a0a01bef04e2dd6bd884e83eac40e879b352
compression_hypothesis_ref: sha256:c2e7e42762e2248f25abd6c1d353d07a0184fa4ea8a7c6178e41116404e7d1b1
hand_beat_hypothesis_ref:   sha256:047ebf186912ebee4ec402f805469432f86d81cdba76a2f793e828470678d3ad
checkpoint_ref:             sha256:e19e2f458b0e559f358f74b3502e5cd6b7e2d32cb3dd5eba5b1dcd9da02adec1
```

Repair selector cross-seed refs:

```text
context_ref:                sha256:61f2b6607f71f7c77318bc1750974004c5bb4c84f9b536fb5352f4c89c0627a7
report_artifact_ref:        sha256:204cca386fa6b48a0aa7d63ef5191bdcf91f0965ca0c50c11e59b8d59bb1df3b
markdown_artifact_ref:      sha256:050ac5d66e050bd5294e57cd4437f52452309c0f6dbf1d9111aafd08632b30b1
safety_hypothesis_ref:      sha256:11f4ac5be458dcf6b85404859746637e78dae1ff88b49efc8b1a5f950b48a603
compression_hypothesis_ref: sha256:c73f8cde1d40121a70156485602b0acd3eba6f62ba9f3c34d47f5e1e6fee549c
hand_beat_hypothesis_ref:   sha256:bc668d679f48705fdba26de502c2e4ac2ea59e806a8dd463d1b4b035e5c7fedf
checkpoint_ref:             sha256:f30e1571f5decf6c92f465aeee88fd5d3b89ddf257250904dd41b530239f0bb5
```

Repair selector formal-boundary refs:

```text
context_ref:                sha256:816d10e42113d2e25d54e8fbf831824e691aa6ce80f70d3f99db3af1eea13a45
receipt_artifact_ref:       sha256:84328e7d90dd6c0fe3f775b46ac898a7fad73ca4aebf1ee770f742076c2b91ee
receipt_hypothesis_ref:     sha256:3c61e2c848da522e7db1b45fbfe2f8803dfccf7cedb94d1461d7b243c576f47b
checkpoint_ref:             sha256:9e51d623aaa3572497be49f2d28fa61654444ea2bc9317d5eb86a9e62b241c4d
```

Fallback and checked-stop formal-boundary refs:

```text
receipt_blob_ref:           sha256:bfa4f5828c15c1cf6ce41928ecef704d5dfef7dded9074e604503ed39b2caba0
context_ref:                sha256:cc4c29f0e7c90f7d60a851c99254568e52f042a320b57fe7af6597a4de633662
artifact_ref:               sha256:4c1657dcb6f992e00af2ddc74668a9c5976f2aaf19d071f0787ec944a242c33f
recipe_ref:                 sha256:e4dc7978d7c94e226a384219133c43a957b0c89169628c73784bfe1d48d54323
hypothesis_ref:             sha256:46b0ce2b178ff8c6ad03963a5059442f1902b41b69e2f5bc3cf000b813262925
evidence_ref:               sha256:9bb153f2d83a3a3d2b0f7535c70e2657ae167a4a1773c91a9d24ca984cd78f4f
support_edge_ref:           sha256:5fee29d8c677fd602446163b981a461eb68d6dd38ff71b67209f671f6f4b931c
checkpoint_ref:             sha256:65e180a97ba7d4257338127532cde0190c17173d503a23e15dfc81db9476078b
```

Research evidence replay refs:

```text
json_blob_ref:              sha256:4c89e2cbdd7016e2ee5b5f6035736fd96422f29013cbfebf0760d8cbaa3ede92
markdown_blob_ref:          sha256:94277a813cd076685a78704563c9dc7dc3938f30e40dd0070af1d58de50cfaa1
context_ref:                sha256:bb984b70f6f3f8e5ad2e96f9321d9d925e7bf337de5b21c68ff7d81bf05b6d21
json_artifact_ref:          sha256:2312c5275ff16f85e3bddf78f6ea27865460e5eb7cb5380051c474248cb4e0e1
markdown_artifact_ref:      sha256:5bd505286881a36b63f5d4a62714a599038de331286837b8a12da4fba3221c41
recipe_ref:                 sha256:2d4a6a5e335d8ee9a37d2e1bfdd2aee8cbb7815aefddf3eb50687ef58509eb6f
hypothesis_ref:             sha256:ab016895b0939b9696ad6ec66932bf2a225d966943c7ad882baf146b9f70fc09
evidence_ref:               sha256:426bfb6451ba54406294e50d887b71120e656a6f0315e15e45fb49b2ab307525
support_edge_ref:           sha256:6ab48e8f170738b4039c5466a0c8e467dfabfbeae7fece7948ddcd61c002b833
checkpoint_ref:             sha256:00433cf11b3856baecdb5787d85e5d9f7a75345e621cab6a163519a1ec1dabf1
```

Research evidence replay v2 refs:

```text
json_blob_ref:              sha256:79cee72a63feff30f024e6ef1789ce7e79c4b906e59ed15f96ad23f9aed68c9f
markdown_blob_ref:          sha256:054432e92e605e15d59bd5586964e7ddc214b197e0e09c583d031fba5fb9d113
context_ref:                sha256:4d05eaa79aa5a0aec8c8bd255fe8705c4231543fa5eca01b25bcd5d42370f84e
json_artifact_ref:          sha256:97055a45995f5172424e0e3ee1e15610d96c28de96d4cef1f864bc70b2eff3a4
markdown_artifact_ref:      sha256:6c0b554c8e132c4ec149ef5c83aa5140a682581cfe616bf9248cce36f554d7ef
recipe_ref:                 sha256:01529bf754b3dbcdb1744e12b3c71d5224ff021d1bf692c1cdb2c6febeacda9a
hypothesis_ref:             sha256:137383d526e160be7a028e0b2572a2bd56064d343fd01948217cfdf6da47a991
evidence_ref:               sha256:4b68f09850aae9cd5341b1067da694d49be985e26ed443d9215d69e3d9b0f692
support_edge_ref:           sha256:e8495444432fae5381c6b59beec1910dddd43b6a46c89a599ddb90f33db39b64
checkpoint_ref:             sha256:3aa0418be9bbaa8e81655128a724b6be1a9b32702626cc8e5e1513671cb6d41d
```

SOTA decision-map refs:

```text
receipt_blob_ref:           sha256:6fa3b68ffe639bed30ac8d10771da0fd8614a26b65d10007bee2153682c8cb67
doc_blob_ref:               sha256:32a5e8eb9dbc47bc2e5c4068d268fa3862c2ab1b09cb523dce6d7d1125a25521
context_ref:                sha256:568e41025a02d49fb7f63e78ebfedabaa286cd162925d42f56901b17a4d6dcf2
receipt_artifact_ref:       sha256:f0155890c5a08a79c3e4e96dfa4c37d42e0b44d96633067a0ada537e076c3965
doc_artifact_ref:           sha256:c30c09ef36db090b0c89e725888b86507169130d9d303bc3e0fd79ab8ea8f3d0
recipe_ref:                 sha256:a6ef2642f0ec9d817919250eae6081113d4cdf56b7be1de7cff2eb4f80ab37e3
hypothesis_ref:             sha256:01ed80d3b2939df31ac04a954aeef626bbae2f9f1974b501df0d6d27ec2f2440
evidence_ref:               sha256:9b0f1e7334e0c4b610a99421426e57f06d6bfbce42d6096ecd4131bbed15ab4f
support_edge_ref:           sha256:a2eef8393a30ad21bec02ec01f1ffc2ef6cdf7d5f5e987543a17a3c464a981ab
checkpoint_ref:             sha256:42ab7699c464cfe590c0a397280d60dce9d604ac9ba044f3ff060662d9df4df9
```

Listwise set-ranker refs:

```text
report_blob_ref:            sha256:293511c9f61167fd71e9d018ad99e44418be6323a44b06370479b84cada385be
markdown_blob_ref:          sha256:5af20b303f8d86f218b7a8bfd764d86c105b11bb5ec6c49751f311f1ef53c004
model_blob_ref:             sha256:0aff9e96b55a10529dc348ae077af546383c72febc96275c4f1d1ba591cb8604
context_ref:                sha256:29d53bcb1b09c51cab843f9bb85511d36a495ae8386c1dda3e3fe00b3e57c97c
report_artifact_ref:        sha256:6205e8974f1f03522b60ce5f69e715a9f1533812b9234db4f3e3f49b29115da2
markdown_artifact_ref:      sha256:86b66adddba8011fc2796f92f3ed186d9be5c7cca996f7e76de89a31a40e041c
model_artifact_ref:         sha256:8d0ae0435a2cff57f284ce3299d7e04ce41420662b613032a1397c094fa7131d
safety_recipe_ref:          sha256:1a6a52e07ed029d7265ea818f00aa6a870f6fc58c62ecca5242184d065b09c8b
improvement_refuter_ref:    sha256:26aee8dbf38cca45bfc2b1b90596d31ec47a23448f6c9d68fa44842982e33e9c
safety_hypothesis_ref:      sha256:0e188ae7b2a0df908cb892856c84cfd83240ccf8fa9f37fc17480db758e518c8
improvement_hypothesis_ref: sha256:e0387de43381ebdef9964a3633a70c228be2cb8cd3a48eddfae2e47face604fe
safety_evidence_ref:        sha256:4a548a1878a1e2ced40014a7b3861734f245186717e2e3862b8ad15767b8f6ed
safety_support_edge_ref:    sha256:af7410f063ccae34f5de79ff7d1e3eac3b5681afbaa9a9d6618f19d06831aa60
improvement_evidence_ref:   sha256:d2d4295f21dc11e5bacb3a7dab725b84166c45a94390d62a27e38d1a08b79f7a
improvement_refute_edge_ref: sha256:733220eb675e45d3097c3f2a4195b3be180d0b9f3cdf6745c40842236315f025
checkpoint_ref:             sha256:c08368fc23424e3da6ceab3d2fe4521f8394cab785356263c3b22efdc12162fb
```

Listwise cross-seed refs:

```text
report_blob_ref:            sha256:4645a8def80a2fd53c5088cf3c9a6e3b40a75042fa76807228d5fb5432cc165c
markdown_blob_ref:          sha256:955a4bcdca90926652b969d23ff70224aa46b1b5895df9fc5cce3539d3f5cad1
context_ref:                sha256:b1f28230e0f80ea49326ae3b7351e214e99d73a0670159af22e09a1f2bdefb26
report_artifact_ref:        sha256:dbb151b06e784d3d03d45942559a92148e78f7060081680af92a72f198b3dbbc
markdown_artifact_ref:      sha256:74cb4fe8faec1e1df2b7d5a85d13464ac11ad132efb69ceb50e6e9890dbdee2b
safety_recipe_ref:          sha256:6c4b6664a102e479a53821b43827e2a6f6c1f0ff5e74246dacc4d18390458496
improvement_refuter_ref:    sha256:b4a7b39877743e5b5971370922024b6b94f70f517c74264a93566fa9d5838eda
safety_hypothesis_ref:      sha256:446fca953f8907bfdd4fd92831cef7ee05658bdd8a9a4d267c9c635bde81c480
improvement_hypothesis_ref: sha256:5d6ba8b60a0174e8b1319ff5b40a6c3b789ecaf72f16043847343d22f3237e35
safety_evidence_ref:        sha256:e7d0436c5cda8897d1959c7df4ebcea5341c9cb829f3798be695b57ca913ae09
safety_support_edge_ref:    sha256:7a7903cac075b551a93f09e435194e75e88efacaeabf7b387552792f401d9a0f
improvement_evidence_ref:   sha256:ec6fcdb9fb8620edcc8a7a3c0ecd4129b8cba9ce87660ddb3bd0c6448a375e67
improvement_refute_edge_ref: sha256:469deb9aeff847ee23e1dc38f1444007f1d683f505cedf3960b529d9def50112
checkpoint_ref:             sha256:bf781978378530bccdc8aeb41e41c8dcffa1b40361306789841f754a04d52dbc
```

Gap-weighted default refs:

```text
stress_blob_ref:            sha256:9773617ff7c73c9d6c56b81fc82afdb303fcc2c7f00c25389c0df9a047d49ad7
hard_cases_blob_ref:        sha256:57c5f3b928cbfd4f7916d1290989c7499cca895d731e3528e5f9a25f1ba3b15c
model_audit_blob_ref:       sha256:f0491799090e8568725cf04d3c365ca913585acb50e1779de5bd4e9239e4aaf9
model_blob_ref:             sha256:1a665e8fc07c1b24dd1ae0110f4509b73c0d975805f0a7ac807fc1f0de157c0a
context_ref:                sha256:501cf904d6afdc8ec39f2b7d0aa8454864999bb89562fd2fdd95827f8365188a
stress_artifact_ref:        sha256:9df99e4b3773f8ca4ef3732fdb32572b7f53a8b6dbc4b1f703954602b4588ab8
hard_cases_artifact_ref:    sha256:2f2ce058239714108001ef1e79029e5dd9b13a974a3ee47c34fe4f8eb0f57be3
model_audit_artifact_ref:   sha256:1e16a6b0f5a3927d6d803d195433bc45cbff0bc3032e034a23fce7d517c8f5cd
safety_recipe_ref:          sha256:a842bc46a056355dfe1b570afcaa0a15fb4a55fefc3fd2f48ec02126c79448b0
beats_hand_recipe_ref:      sha256:5de096d00be1d069bc5c90a57e7fa4c717169667d79fa0268978704d2fd96cf1
safety_hypothesis_ref:      sha256:e62f81665f71a17778f7744192e487c5e1ab4bec2685b976c1642b70cba1a833
beats_hand_hypothesis_ref:  sha256:daf3d2c4a0547549625e025996a90d2f0cca69fddb284f0e313f946dec96b8b8
safety_evidence_ref:        sha256:41497b1032188340643251b87a2a54aa8123d12244def5e85929dc0d34fcbd0b
safety_support_edge_ref:    sha256:00b1930390bcecb498f7dff1a3dcb53930c0195a4e06829e4bfd9ab35fe017e3
beats_hand_evidence_ref:    sha256:639cbe2f55b9edf8463b4615d35adf9955fed19f9886fc8fc0494fc98ae655e4
beats_hand_support_edge_ref: sha256:70bd65bfe8aff7cd2f532c05a5e3005525e5ac00917b14830485df1b7a891175
checkpoint_ref:             sha256:6aed84ddf6214db69fd7e61c12614ee96379004dbd7074e9ba78de6d14cb6e27
```

AutoTraderEnergy hard cross-seed refs:

```text
json_blob_ref:              sha256:70c21350465beed0d7409d8a4ae3d6f8a03d30f63942da7a506655bf9fe52b78
markdown_blob_ref:          sha256:ba27fef93a6013d460513d5755ed94e425496886e5057d52cc3db100236e8bc0
context_ref:                sha256:04fd880536ef2488f9480a1efacba3c76a7c1ebafbfcb60d48edcf95345016a4
json_artifact_ref:          sha256:a8c1767ce02ccb4b09c4558f5ce7c2c454a60cf68b144ee0b95bd50f60132500
markdown_artifact_ref:      sha256:0e59bb1e12d1681d6ff57a29141faf361d0eeb446c3d4b997a6257540989d992
safety_recipe_ref:          sha256:8da69586cb83520501931370f6ce8808b1c12485bcb34fa4e98bf4d300564a7f
beats_hand_recipe_ref:      sha256:78bfca23f65ec4cb63c47482c277eca4a393cb22916d9294afc703d26e6c6368
profile_recipe_ref:         sha256:ee60a2e1d6961bf50fa048f85ee2c8408344d37f43bbdb5e6b23b6f9954f19c0
safety_hypothesis_ref:      sha256:53088aad688f418e6b2caa2ddaf4c4e19da88fc6ef48d1189cebb8c4ef3cae5d
beats_hand_hypothesis_ref:  sha256:ccb70800bec0f3ea02b7a20a3d7fff6455ada25bc8c3c17764aacf363b56d5e6
profile_hypothesis_ref:     sha256:5371e8f4a880f9cc5c8eb0910376dfebc118a95d5dea31fe62036ca21ea3d70c
safety_evidence_ref:        sha256:defd4af25179ff95635a90587afbe1d436607802311e329fa5b9f3b06caaf018
safety_support_edge_ref:    sha256:83cc1e455f490874a04afe2df0b651432e5e4b8474e2fbec961cf3f057f10e3d
beats_hand_evidence_ref:    sha256:66e14cfd8ce180dace51ff357b63a15b6e0db6bc61cf7784472cff49eb9d6bb4
beats_hand_support_edge_ref: sha256:518216423fab2484c7ed62a13e960a26655fdc530d0a89feb208787ea8cf76c8
profile_evidence_ref:       sha256:7f25aeac3f25eaeb7ebbeb25e5911c706020993314430268412477de409b68be
profile_support_edge_ref:   sha256:8ccf14e263f5e6199c1c75aaae39b0a1039f48ce8652fe096268354a70738140
checkpoint_ref:             sha256:5e5c4af70657ebf7438866dc5a33008b4fc5aaa816bc050a5e05edac7b57ceea
```

Research evidence replay v3 refs:

```text
json_blob_ref:              sha256:eacec80f4699b916b3a469ad9292a6b15f10b1831e7beee341138bfbdfff9999
markdown_blob_ref:          sha256:c5ba84e0f920b513f63ffe78b5b92d0d0807acfaf3a4be737bd7525b09bfa4f4
context_ref:                sha256:0dd989904d54586081bdb157a09343a0f7f3787a813e36bb0c5cf3773e50d1c3
json_artifact_ref:          sha256:cc2d4beb131232d19ee147456036de5b66c360b7524e8cfffaba09514220cc10
markdown_artifact_ref:      sha256:68e3ef55518ed41a01f15faad3b924b22a16578b90f5f9d6ba5e2dc6f75566e2
recipe_ref:                 sha256:178fa1b54800590359208bdd91b77831d623f38b82a37a22198bf7c9f7a61eb9
hypothesis_ref:             sha256:dabd7314ae604ff9bd3a47480cfa75dc2d5230ac4b3806191c703c6dbb0f34a8
evidence_ref:               sha256:3021a12d485552d89dcc222696920b1e12a2beb940df538f398f93a2c134b4e4
support_edge_ref:           sha256:9d50089ff73d13b26a29bb9af97292bad7ff0f098ccaa5a265ee4b43cf7d3079
checkpoint_ref:             sha256:26c16f6e1063a395e12d5dc5827c9f3d7e5389bdbe5e232efcc55be7281e423d
```

Research evidence replay v4 refs:

```text
json_blob_ref:              sha256:f17dff68647cb4bf30d251e4955fc2700fd875abb4e302341f260aaece452613
markdown_blob_ref:          sha256:4814bb6531e3f5aea90f3cf09f7e4a2959d8bf8dcd9f1b5e2dd38d08198b2c50
context_ref:                sha256:46274df7ab3ac57f1b559d3fe26c4f0b85dc5d6b5ae106ab51d1b9c80fece133
json_artifact_ref:          sha256:08cd5ce2866b00368fb5c5929a63a7a3f19bdbcec01a0e0e8aab925f7f339469
markdown_artifact_ref:      sha256:3733bd21a61387db61d256c0140a67fce3a415ddd845b20629ded2a3e3b656db
recipe_ref:                 sha256:b8f74ff910d3ed9c7165c8671103ed64c91603bb1a540bb038ff7baf237be427
hypothesis_ref:             sha256:f4ec01de32118120b4cda7cae7903b3a525c226448e83f83f2532672477d0918
evidence_ref:               sha256:e9f7efadac2901b060795c2ac782fd8ae6dd9fa37ff7003e73fc3ef7134e7cb1
support_edge_ref:           sha256:ee3e6a8640308b9fe7ae76a5afa7534f22a88ef62458d1181b1c6e8edc08b07f
checkpoint_ref:             sha256:457347c6b0933fe1f6b0e7488384bb62c66d1636aa1824e3ba075d0737a79c79
```

Research evidence replay v5 refs:

```text
json_blob_ref:              sha256:7e0185772251353e3720e12b211a677b497397d01486bd193b22f48ea6676e8c
markdown_blob_ref:          sha256:20a449774a968bf744d4d011fd045c2bd961bbde0e6c83cd5d00a3e6734885cd
context_ref:                sha256:5fb9db1fd9ac44ba0ef7a1d40abc167f558a15a089431ee8009641742be0b1a0
json_artifact_ref:          sha256:02fedeb78ae4c433a7ce04327cbb644842fe5c139429adef5da02daceb3a2e65
markdown_artifact_ref:      sha256:b0319024ef8b890f003adaef7308683c88b2cb82a6553b322b76a05e4138b878
recipe_ref:                 sha256:efdcd111786eec5527bd176f26b1bfee6c55aae595599b14d49c610a54666bf1
hypothesis_ref:             sha256:507cdadd9c4c00815224de2b57bd3a3386d82929663cccb174ac7f3c4e7cf60b
evidence_ref:               sha256:095b9834f1e1d1c98328e3b61f1a6521cd2ecb4faae87acad1aa57a6416c394f
support_edge_ref:           sha256:c66484dfa8357510764e6e6c12cdf7648f74f9195bb9310436e62d7f3620638f
checkpoint_ref:             sha256:5f3da5e6ee234d6b958d67c4c98b84d29bc2456981eafe237752a76e2854dd1f
```

Research evidence replay v6 refs:

```text
json_blob_ref:              sha256:b7cc53aa563e1648c018a8a397712b9b22ce6b482559be9fc66be84cffb64a03
markdown_blob_ref:          sha256:55798606714565cff58770b468e45733f0c0f2aae8d1a115a1784d8827766c16
context_ref:                sha256:3fa3962f11e99c61ad7f079ffea18ea6205c32750545f0fa9b07d8e904038633
json_artifact_ref:          sha256:25b2afd7baaf0a8c059bee37fccf4f129202b9e1dba814deed55be410041d2cc
markdown_artifact_ref:      sha256:4d008cb32c87a0342a771ee1710f53c789ffb9a1f2b09085d4a7e55233503eed
recipe_ref:                 sha256:560d28cccff44539bca61bdaf37d164a8ec3040bbcba38dc99b7adb92b649e50
hypothesis_ref:             sha256:c558cab9a196a46c7e9efc00eb62a8465e94b74fd53e04bf2ef8be1a343759a8
evidence_ref:               sha256:542579c87da7db395209ed9623a74a300e251f065bf04bc6608db3b6c42a88f9
support_edge_ref:           sha256:a8cbb42fb76f7da3700c4c0bcdb637b1f55491e8a602fa97ff618e71da370bca
checkpoint_ref:             sha256:c9f36a31dead32d4814dd62e011b775d48a4e6e6b23470ef8393249244646c4a
```

Derived PopperPad status:

```text
H_ZENOENERGY_SET_AWARE_COMPARE_SAFETY_20260517: supported
H_ZENOENERGY_SET_AWARE_LINEAR_STRICTLY_IMPROVES_AGGREGATE_20260517: falsified
H_ZENOENERGY_NEIGHBORHOOD_SAFETY_SUBSET_20260517_V2: supported
H_ZENOENERGY_NEIGHBORHOOD_REDUCES_REGRET_20260517_V2: supported
H_ZENOENERGY_NEIGHBORHOOD_REDUCES_VERIFIER_CALLS_20260517_V2: falsified
H_ZENOENERGY_REPAIR_SELECTOR_SAFETY_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_COMPRESSES_FULL_NEIGHBORHOOD_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_STRICTLY_BEATS_HAND_SELECTED_20260517: falsified
H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_SAFETY_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_COMPRESSES_FULL_NEIGHBORHOOD_20260517: supported
H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_STRICTLY_BEATS_HAND_SELECTED_20260517: falsified
H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517: supported
H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517: supported
H_ZENOENERGY_RESEARCH_EVIDENCE_REPLAY_GATE_20260517: supported
H_ZENOENERGY_RESEARCH_EVIDENCE_REPLAY_GATE_20260517_V2: supported
H_ZENOENERGY_SOTA_DECISION_MAP_RECEIPT_20260518: supported
H_ZENOENERGY_RESEARCH_EVIDENCE_REPLAY_GATE_20260518_V3: supported
H_ZENOENERGY_LISTWISE_SET_RANKER_SAFETY_20260518: supported
H_ZENOENERGY_LISTWISE_SET_RANKER_STRICTLY_IMPROVES_PAIRWISE_20260518: falsified
H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_SAFETY_20260518: supported
H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_STRICTLY_IMPROVES_PAIRWISE_20260518: falsified
H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_SAFETY_20260518: supported
H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_BEATS_HAND_ENERGY_20260518: supported
H_ZENOENERGY_RESEARCH_EVIDENCE_REPLAY_GATE_20260518_V4: supported
H_ZENOENERGY_RESEARCH_EVIDENCE_REPLAY_GATE_20260518_V5: supported
H_ZENOENERGY_RESEARCH_EVIDENCE_REPLAY_GATE_20260518_V6: supported
doctor_ok: true
```

Use:

```bash
PYTHONPATH=external/PopperPad/src python3 -m popperpad \
  --pad internal/popperpad/zenoenergy doctor
```
