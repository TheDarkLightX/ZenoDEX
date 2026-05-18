# AutoTraderEnergy Hard V1 Receipt

```text
profile: hard synthetic
train_seed: 20260522
holdout_seed: 20260523
model: data/upba_energy/autotrader_energy_hard_linear_hand_seed20260522.json
train_rows: 40000
dataset_rows: 16000
contexts: 1000
model_feature_dim: 35
model_parameter_count: 36
training_backend: linear_pairwise_hinge
init: hand
epochs: 6
learning_rate: 0.001
```

| mode | top1 | top3 | top5 | mean guard calls | p95 | p99 | invalid accepts | invalid top1 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 0.068 | 0.187 | 0.318 | 8.550 | 16 | 16 | 0 | 0.632 |
| hand | 0.418 | 0.834 | 0.975 | 2.160 | 5 | 6 | 0 | 0.000 |
| learned | 0.595 | 0.929 | 0.990 | 1.698 | 4 | 5 | 0 | 0.000 |
| hybrid | 0.595 | 0.929 | 0.990 | 1.698 | 4 | 5 | 0 | 0.000 |

The scorer is advisory. Deterministic AutoTrader policy guards remain the authority for trade acceptance.

The hard synthetic profile adds multiple valid candidate actions per context,
valid high-cost decoys, and invalid high-edge near misses. This produces a
nontrivial ordering task: the learned scorer reduces mean guard calls from
2.160 for hand energy to 1.698, while invalid accepted candidates remain zero.
