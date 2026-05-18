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

| mode | mean guard calls | top-1 recall | top-5 recall | invalid accepts |
| --- | ---: | ---: | ---: | ---: |
| random | 3.250 | 0.250 | 1.000 | 0 |
| hand | 2.000 | 0.000 | 1.000 | 0 |
| learned | 2.000 | 0.000 | 1.000 | 0 |

Interpretation: the learned scorer ties hand energy on this fixture. Both
reduce mean guard calls versus random ordering, but neither puts the exact
shadow winner first. This records boundary replay and a concrete
distribution-transfer gap for later model work.

The built-in shadow bridge is a deterministic fixture derived from accepted ZenoGraph store exports. It is useful for schema and boundary replay, but it is not live production distribution evidence.
