# ZenoDEX AB Reserve-State Child-Frontier Tau Certificate - 2026-06-29

## Executive Result

`ab_reserve_state_child_frontier_certificate_v1` admits the reserve-state child-frontier research bundle only when the n=7 host evidence, bounded n=8 sample, transition projection, observed-summary bridge, Lean contract markers, deterministic replay, negative controls, scoped non-claims, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `strict_zero_min_scope_ok` = `1`
- `n7_child_frontier_ok` = `1`
- `n8_sample_child_frontier_ok` = `1`
- `transition_projection_ok` = `1`
- `observed_summary_bridge_ok` = `1`
- `lean_afterstep_contract_ok` = `1`
- `deterministic_replay_ok` = `1`
- `negative_controls_ok` = `1`
- `scope_nonclaims_bound` = `1`
- `no_authority_effect` = `1`
- `frontier_nonvacuous` = `1`
- `n8_sample_bounded` = `1`

## Source Reports

| report | ok | schema |
| --- | --- | --- |
| `n7_child_frontier` | `True` | `zenodex.ab_reserve_state_child_frontier_generation_report.v1` |
| `n8_child_frontier_sample` | `True` | `zenodex.ab_reserve_state_child_frontier_n8_sample_report.v1` |
| `transition_projection` | `True` | `zenodex.ab_reserve_state_transition_projection_report.v1` |
| `reserve_state_quotient_n7` | `True` | `zenodex.ab_strict_zero_min_reserve_state_quotient_certificate_report.v1` |
| `reserve_state_quotient_n8_sample` | `True` | `zenodex.ab_strict_zero_min_reserve_state_quotient_n8_sample_report.v1` |

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `child_frontier_certificate_pass` | `True` | `1` |
| `missing_n7_child_frontier_reject` | `True` | `0` |
| `missing_n8_sample_reject` | `True` | `0` |
| `missing_transition_projection_reject` | `True` | `0` |
| `missing_observed_summary_bridge_reject` | `True` | `0` |
| `missing_lean_contract_reject` | `True` | `0` |
| `missing_negative_controls_reject` | `True` | `0` |
| `missing_scope_nonclaims_reject` | `True` | `0` |
| `missing_bounded_n8_scope_reject` | `True` | `0` |
| `authority_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not claim exhaustive n=8 coverage.
- This certificate does not define canonical tie order.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/zenodex_ab_reserve_state_child_frontier_tau_certificate_20260629.py
```
