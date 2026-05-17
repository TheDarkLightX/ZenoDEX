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
doctor_ok: true
```

Use:

```bash
PYTHONPATH=external/PopperPad/src python3 -m popperpad \
  --pad internal/popperpad/zenoenergy doctor
```
