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

Derived PopperPad status:

```text
H_ZENOENERGY_SET_AWARE_COMPARE_SAFETY_20260517: supported
H_ZENOENERGY_SET_AWARE_LINEAR_STRICTLY_IMPROVES_AGGREGATE_20260517: falsified
doctor_ok: true
```

Use:

```bash
PYTHONPATH=external/PopperPad/src python3 -m popperpad \
  --pad internal/popperpad/zenoenergy doctor
```
