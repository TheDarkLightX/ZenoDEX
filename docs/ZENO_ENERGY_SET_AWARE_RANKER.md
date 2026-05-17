# ZenoEnergy Set-Aware Ranker

Date: 2026-05-17

This note records the first concrete extension after the ZenoEnergy v0 baseline:
a permutation-invariant set feature block for UPBA v2 candidate ranking.

The baseline ranker uses a fixed 96-dimensional aggregate feature vector. That
is intentionally simple and auditable, but it compresses the intent set into
min/max/mean summaries. The set-aware extension keeps the aggregate block and
adds deterministic Deep-Sets-style moments over intent/fill pairs.

```text
set-aware features =
  aggregate UPBA features
  ++ permutation-invariant moments over sorted intent/fill pairs
```

The scorer remains advisory:

```text
model ranks candidates
deterministic verifier accepts or rejects candidates
```

## Files

- `src/energy/upba_v2_set_features.py`
  - `SET_FEATURE_NAMES`
  - `SET_AWARE_FEATURE_NAMES`
  - `extract_upba_v2_set_feature_record`
  - `extract_upba_v2_set_aware_feature_record`
- `tools/generate_upba_energy_dataset.py`
  - emits optional `set_features` and `set_aware_features`
- `tools/train_upba_energy.py`
  - supports `--feature-block set-aware`
- `tools/evaluate_upba_energy.py`
  - supports `--feature-block set-aware`
- `tools/inspect_upba_energy_model.py`
  - audits aggregate and set-aware linear models
- `tests/energy/test_upba_v2_set_features.py`
  - fixed-width schema checks
  - permutation invariance checks
  - advisory scoring checks
  - set-aware training smoke test

## Feature Shape

The set-aware model has:

```text
aggregate feature dim: 96
set feature dim:       51
combined feature dim:  147
linear parameters:     148
```

Set features include normalized moments for:

- intent amount and minimum output distribution;
- balance-to-amount and insufficient-balance indicators;
- fill fractions by direction;
- partial, zero, positive, and overfilled intents;
- per-intent surplus ratios;
- expected-output agreement;
- limit, balance, output, dust, zero-net-input, and fee indicators.

The feature block is deterministic and permutation-invariant over intent order
and candidate fill order. It does not include verifier labels, winner flags,
target energy, or valid-objective fields.

## Smoke Result

Command shape:

```bash
python3 tools/generate_upba_energy_dataset.py \
  --batches 6 \
  --candidates-per-batch 12 \
  --seed 20260519 \
  --output /tmp/zenoenergy-set-aware.jsonl

python3 tools/train_upba_energy.py \
  --dataset /tmp/zenoenergy-set-aware.jsonl \
  --output-model /tmp/zenoenergy-set-aware-model.json \
  --feature-block set-aware \
  --epochs 2 \
  --learning-rate 0.02 \
  --seed 20260519

python3 tools/evaluate_upba_energy.py \
  --dataset /tmp/zenoenergy-set-aware.jsonl \
  --model /tmp/zenoenergy-set-aware-model.json \
  --mode learned \
  --feature-block set-aware
```

Observed smoke metrics on 6 synthetic winner-bearing batches:

```text
top_1_recall:          0.8333
top_5_recall:          1.0000
top_10_recall:         1.0000
mean_verifier_calls:   1.3333
p95_verifier_calls:    3
p99_verifier_calls:    3
invalid_accept_count:  0
```

This is a wiring check, not a benchmark claim. The existing gap-weighted
aggregate model remains the stronger measured checkpoint until the set-aware
model is trained and evaluated on the full held-out corpus.

## Next Experiment

A first aggregate-vs-set-aware comparison is now recorded in
[ZenoEnergy Set-Aware Comparison](./ZENO_ENERGY_SET_AWARE_COMPARISON.md).
The run used 120 synthetic training batches and 80 held-out batches:

```text
aggregate learned top1:       0.9625
aggregate learned mean calls: 1.0375
set-aware learned top1:       0.9500
set-aware learned mean calls: 1.0625
invalid accepts:              0 in every mode
```

The result is negative knowledge for this exact linear set-aware candidate:
the extra moment features did not improve the aggregate ranker on this seed.
The aggregate gap-weighted checkpoint stays the measured default.

The acceptance criteria for future runs should stay unchanged:

```text
invalid_accept_count = 0
top_10_recall >= aggregate baseline
mean verifier calls <= aggregate baseline
fallback recovers exact winner when top-k fails
```

Next research moves should test cross-seed stability, nonlinear set-aware
scorers, and hard-case-focused objectives before promoting set-aware features.
