# Zeno Oracle Coupled Inequality Certificate - 2026-06-27

## Executive Result

This artifact replaces the refuted Cartesian-box interpretation with a coupled inequality certificate that mirrors the pointwise oracle economic-security verifier.
Rules checked: `8`. Replay cases: `5`. Overall status: `ok=True`.

Authority boundary: the certificate is advisory evidence; the pointwise verifier remains authoritative.

## Rules

| rule | verifier error | expression |
| --- | --- | --- |
| `notional_covers_extractable` | `extractable_value_exceeds_notional` | `max_extractable_value_e8 <= notional_value_e8` |
| `cheat_gain_covers_extractable` | `expected_cheat_gain_exceeds_extractable_value` | `expected_cheat_gain_e8 <= max_extractable_value_e8` |
| `attack_cost_margin` | `attack_cost_floor_below_required_margin` | `attack_cost_floor_e8 * 10000 >= max_extractable_value_e8 * (10000 + required_attack_margin_bps)` |
| `reporter_reward_floor` | `reporter_reward_below_honest_cost_plus_risk` | `reporter_reward_per_report_e8 >= honest_reporter_cost_e8 + honest_reporter_risk_premium_e8` |
| `reporter_reward_budget` | `reporter_reward_budget_exceeded` | `reporter_reward_per_report_e8 * reporter_count <= reporter_reward_budget_e8` |
| `slash_deterrence` | `slash_deterrence_below_required_margin` | `(reporter_bond_required_e8 * slash_fraction_bps) // 10000 >= ceil(expected_cheat_gain_e8 * (10000 + deterrence_margin_bps) / 10000)` |
| `dispute_reward_budget` | `dispute_reward_budget_exceeded` | `dispute_reward_e8 <= dispute_budget_e8` |
| `fee_share_budget` | `fee_shares_exceed_fee_paid` | `reporter_fee_share_e8 + treasury_fee_share_e8 + burn_fee_share_e8 <= fee_paid_e8` |

## Replay Cases

| case | certificate ok | verifier ok | failed rules |
| --- | --- | --- | --- |
| `sample_accepts` | `True` | `True` | none |
| `attack_margin_counterexample_now_rejected` | `False` | `False` | `attack_cost_floor_below_required_margin` |
| `reporter_reward_counterexample_now_rejected` | `False` | `False` | `reporter_reward_budget_exceeded` |
| `slash_counterexample_now_rejected` | `False` | `False` | `slash_deterrence_below_required_margin` |
| `fee_share_budget_rejects` | `False` | `False` | `fee_shares_exceed_fee_paid` |

## Non-Claims

- The certificate mirrors the current pointwise economic-security verifier; it does not estimate MEV or market truth.
- The certificate does not authorize oracle updates.
- The certificate is a coupled inequality checker, not a maximal polytope enumerator.

## Replay

```bash
python3 tools/zenodex_oracle_coupled_inequality_certificate_20260627.py
```
