# AutoTraderEnergy v0 Receipt

```text
train_contexts: 500
train_rows: 5000
holdout_contexts: 250
dataset_rows: 2500
holdout_rows: 2500
model_feature_dim: 35
model_parameter_count: 36
model: data/upba_energy/autotrader_energy_linear_hand_tiny_step_seed20260518.json
train_seed: 20260518
holdout_seed: 20260519
```

| mode | top1 | top3 | top5 | mean guard calls | p95 | p99 | invalid accepts | invalid top1 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 0.080 | 0.248 | 0.496 | 5.628 | 10 | 10 | 0 | 0.864 |
| hand | 0.992 | 1.000 | 1.000 | 1.012 | 1 | 1 | 0 | 0.000 |
| learned | 0.992 | 1.000 | 1.000 | 1.012 | 1 | 1 | 0 | 0.000 |
| hybrid | 0.992 | 1.000 | 1.000 | 1.012 | 1 | 1 | 0 | 0.000 |

The scorer is advisory. Deterministic AutoTrader policy guards remain the authority for trade acceptance.

## Interpretation

The ZenoEnergy pattern transfers cleanly to AutoTrader candidate-action ranking.
On this bounded synthetic holdout, the tiny 36-parameter learned scorer matches
the deterministic hand energy and sharply improves over random ordering:

```text
random mean guard calls: 5.628
learned mean guard calls: 1.012
invalid_accept_count: 0
```

The model ranks candidate actions only. The deterministic guard verifier still
decides whether a candidate action may be submitted.

## Negative Knowledge

A zero-initialized linear scorer trained on the same synthetic setup beat random
ordering but trailed the hand energy baseline:

```text
zero_init learned top1: 0.932
zero_init learned mean guard calls: 1.072
zero_init invalid_top1_rate: 0.032
hand energy top1: 0.992
hand energy mean guard calls: 1.012
```

A larger hand-initialized update also trailed hand energy. The promoted v0
checkpoint uses hand initialization with a tiny learning step, which preserves
the hand baseline rather than improving it. The current conclusion is that
AutoTrader's deterministic guard structure is already easy for a hand energy to
rank on this synthetic distribution. The next useful experiment needs harder
candidate sets, real shadow observations, or action-value labels that create
room for learning beyond guard-shaped rules.

## Safety Boundary

```text
energy_rank(candidate) -> advisory_order
policy_guard(candidate) -> accept_or_reject
```

The scorer cannot authorize a trade. It can only place a candidate earlier in
the guard-check order.
