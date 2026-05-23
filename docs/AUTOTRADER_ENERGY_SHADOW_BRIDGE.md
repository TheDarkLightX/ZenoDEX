# AutoTraderEnergy Shadow Bridge Receipt

source: built-in-zenograph-baseline
synthetic_train_contexts: 1500
candidates_per_context: 16
train_seed: 20260528
shadow_contexts: 4
shadow_rows: 20
valid_count: 12
invalid_count: 8
invalid_accept_count_total: 0
policy_guards_authoritative: true
scorer_authorizes_trade: false

| mode | mean guard calls | objective guard calls | exact top-1 | objective top-1 | top-5 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 3.250 | 2.000 | 0.250 | 0.500 | 1.000 | 0 |
| hand | 2.000 | 1.000 | 0.000 | 1.000 | 1.000 | 0 |
| learned | 2.000 | 1.000 | 0.000 | 1.000 | 1.000 | 0 |

Interpretation: the learned scorer ties hand energy on exact hash-selected
winner position, but reaches an objective-equivalent argmax candidate first
on every context. This records a quotient/equivalence issue in the shadow
metric: exact top-1 can be zero when the benchmark has tied valid maxima.

The built-in shadow bridge is a deterministic fixture derived from accepted ZenoGraph store exports. It is useful for schema and boundary replay, but it is not live production distribution evidence.
