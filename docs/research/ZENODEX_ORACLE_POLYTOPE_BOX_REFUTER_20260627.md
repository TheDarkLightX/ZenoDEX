# Zeno Oracle Polytope Box Refuter - 2026-06-27

## Executive Result

This artifact refutes the broad claim that the one-field oracle intervals can be promoted directly to a Cartesian product box.
Counterexamples found: `3` from `5` deterministic probes.

The one-field intervals are not a Cartesian product feasibility polytope. A coupled interval certificate must include cross-field inequalities or an exact verifier for the intended multi-field region.

Authority boundary: the pointwise verifier remains authoritative; this tool records negative knowledge for the research frontier.

## Probes

| probe | inside one-field intervals | verifier accepted | errors |
| --- | --- | --- | --- |
| `baseline_sample_accepts` | `True` | `True` | none |
| `attack_margin_cartesian_counterexample` | `True` | `False` | `attack_cost_floor_below_required_margin` |
| `reporter_reward_cartesian_counterexample` | `True` | `False` | `reporter_reward_budget_exceeded` |
| `slash_coverage_cartesian_counterexample` | `True` | `False` | `slash_deterrence_below_required_margin` |
| `all_lower_bounds_control` | `True` | `True` | none |

## Non-Claims

- This refuter does not invalidate the one-field interval compiler.
- This refuter does not construct the maximal coupled feasible region.
- This refuter does not estimate MEV, challenge probability, or oracle truth.

## Replay

```bash
python3 tools/zenodex_oracle_polytope_box_refuter_20260627.py
```
