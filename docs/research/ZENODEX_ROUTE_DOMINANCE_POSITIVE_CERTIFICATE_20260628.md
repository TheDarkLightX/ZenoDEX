# ZenoDEX Route Dominance Positive Certificate - 2026-06-28

## Executive Result

A bounded exact-out route-label domain admits a best-only dominance frontier when a host verifier proves every pruned route is dominated under the integer route key and Tau certifies the resulting proof-surface flags.

Research certificate only. Tau has no settlement, quote, routing, oracle, liquidation, or state-root authority.

- Tau spec: `src/tau_specs/recommended/route_dominance_frontier_envelope_v1.tau`
- Positive cases: `5`
- Route labels covered: `169`
- Kept frontier labels: `5`
- Pruned labels with dominators: `164`
- Frontier compression: `169:5`
- Mutation invalid accepts: `0`
- Prior forged-flag admits retained as negative knowledge: `2`

## Positive Certificates

| case | labels | kept | pruned | selected route | amount in | Tau accepts |
| --- | ---: | ---: | ---: | --- | ---: | --- |
| `positive_best_only_amount_out_8` | `11` | `1` | `10` | `twohop:p_ac>p_cb` | `14` | `True` |
| `positive_best_only_amount_out_16` | `19` | `1` | `18` | `twohop:p_ac>p_cb` | `26` | `True` |
| `positive_best_only_amount_out_24` | `27` | `1` | `26` | `twohop:p_ac>p_cb` | `38` | `True` |
| `positive_best_only_amount_out_42` | `45` | `1` | `44` | `twohop:p_ac>p_cb` | `67` | `True` |
| `positive_best_only_amount_out_64` | `67` | `1` | `66` | `twohop:p_ac>p_cb` | `102` | `True` |

## Negative Controls

| case | ok | o4 | o5 |
| --- | --- | ---: | ---: |
| `drop_dominator_reject` | `True` | `0` | `0` |
| `drop_projection_cover_reject` | `True` | `0` | `0` |
| `drop_quote_replay_reject` | `True` | `0` | `0` |
| `drop_rounding_bound_reject` | `True` | `0` | `0` |
| `drop_no_authority_reject` | `True` | `0` | `0` |
| `inactive_safe` | `True` | `0` | `1` |

The prior refuter remains attached: forged all-true Tau flags admit two bad route packets, while host-computed flags have zero false admits.

## Non-Claims

- This is a bounded direct, two-hop, and two-way split exact-out route-label certificate, not an all-route theorem.
- The positive certificate still depends on host-computed flags; untrusted declared Tau flags are unsafe, as shown by the prior refuter.
- The artifact compresses the positive certificate frontier; it does not claim to reduce route-label generation cost.
- Tau does not compute route quotes, dominance, projection cover, settlement, or runtime route selection.

## Replay

```bash
python3 tools/zenodex_route_dominance_positive_certificate_20260628.py
```
