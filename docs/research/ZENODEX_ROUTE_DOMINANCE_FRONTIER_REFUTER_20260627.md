# ZenoDEX Route Dominance Frontier Refuter - 2026-06-27

## Executive Result

This artifact checks the route-dominance Tau envelope against host-computed direct, two-hop, and parallel-split exact-out route labels.
Cases: `3`. Forged declared Tau admits: `2`. Computed-flag false admits: `0`. Overall: `ok=True`.

Result: Tau is a useful compact envelope only when its flags are produced by a host route-label verifier. Forged all-true flags can admit bad route packets.

## Cases

| case | host ok | Tau with declared flags | Tau with computed flags | failed host flags |
| --- | --- | --- | --- | --- |
| `valid_best_only_dominates` | `True` | `True` | `True` | none |
| `forged_pruned_winner_without_dominator` | `False` | `True` | `False` | `i4` |
| `forged_projection_cover_gap` | `False` | `True` | `False` | `i6` |

## Best Route Evidence

- `valid_best_only_dominates`: selected `twohop:p_ac>p_cb` amount_in `67`, full best `twohop:p_ac>p_cb` amount_in `67`.
- `forged_pruned_winner_without_dominator`: selected `twohop:p_ac_fee_heavy>p_cb` amount_in `88`, full best `twohop:p_ac>p_cb` amount_in `67`.
- `forged_projection_cover_gap`: selected `twohop:p_ac>p_cb` amount_in `67`, full best `twohop:p_ac>p_cb` amount_in `67`.

## Non-Claims

- This is a bounded direct/two-hop/parallel-split route-label refuter, not an exhaustive all-route theorem.
- Tau checks declared proof-surface flags; host verification must compute those flags from route labels.
- The artifact does not authorize settlement and does not replace route quote replay.

## Replay

```bash
python3 tools/zenodex_route_dominance_frontier_refuter_20260627.py
```
