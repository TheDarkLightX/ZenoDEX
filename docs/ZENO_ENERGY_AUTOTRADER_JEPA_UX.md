# ZenoEnergy AutoTrader JEPA UX

```text
ok: true
decision: research_only_future_aware_autotrader_ux
contexts: 96
future_weight: 0.1
later_policy_failure_auc: 0.814429
future_failure_tension_delta_mean: 0.500729
slippage_stress_correlation: 0.613327
budget_stress_correlation: 0.559229
drawdown_stress_correlation: 0.555595
safer_counterfactual_reduction_rate: 1.000000
suggested_control_best_reduction_rate: 1.000000
blocked_status_match_rate: 1.000000
future_warning_match_rate: 1.000000
mean_guard_calls: 1.062500
top_1_recall: 0.937500
top_5_recall: 1.000000
invalid_accept_count: 0
balanced_future_tension: 0.910303
fragile_future_tension: 4.764275
```

The UX layer presents advisory risk and explanation cards. It does not authorize execution; deterministic policy guards remain authoritative.

## UX Checks

| check | status |
| --- | --- |
| future tension predicts later policy failures | pass |
| future tension predicts drawdown, slippage, and budget stress | pass |
| safer counterfactual controls lower future tension | pass |
| suggested controls lower future tension | pass |
| UX warnings match deterministic guard outcomes | pass |
| ranking remains a guardrail, top-5 recall at least 0.99 | pass |
| future tension differentiates fragile from balanced | pass |
| no invalid accepts | pass |
| UX explains blocked state and controls | pass |
| model and UX cannot authorize trade | pass |
| research inputs are linked | pass |
| JEPA path is small and dependency-light | pass |

## Negative Knowledge

- Future-tension UX is a warning and proposal-shaping feature, not execution authority.
- JEPA-over-hand ordering is weaker than learned AutoTraderEnergy; use learned ranking as the ordering guardrail.
- Synthetic UX receipts do not prove live AutoTrader profitability.
- Production use still needs source-manifested real shadow replay and wallet-level policy gates.
