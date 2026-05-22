# ZenoEnergy Quality Selection

schema: `zenodex/energy/upba_v2_quality_selection_report/v1`
winner_bearing_train_batches: 9916
excluded_no_winner_train_batches: 84

| train batches | raw mean calls | quality mean calls | raw top-1 | quality top-1 | quality better? | invalid accepts |
| ---: | ---: | ---: | ---: | ---: | --- | ---: |
| 100 | 1.0439 | 1.0620 | 0.9662 | 0.9445 | no | 0 |
| 250 | 1.0610 | 1.0388 | 0.9496 | 0.9662 | yes | 0 |
| 500 | 1.0343 | 1.0282 | 0.9758 | 0.9763 | yes | 0 |
| 1000 | 1.0303 | 1.0247 | 0.9773 | 0.9783 | yes | 0 |
| 2500 | 1.0247 | 1.0217 | 0.9808 | 0.9793 | yes | 0 |
| 5000 | 1.0177 | 1.0177 | 0.9829 | 0.9823 | no | 0 |

## Current Gap-Weighted Baseline

top_1_recall: 0.9834
top_10_recall: 1.0000
mean_verifier_calls: 1.0166
p99_verifier_calls: 2

## Interpretation

Quality-selected winner-bearing synthetic batches improve mean calls over raw winner-bearing samples at the medium budgets in this probe.

Very small hard-only quality budgets can overfocus on rare current-model misses; quality selection is useful as a coverage lane, not as proof that hard examples alone dominate raw training.
