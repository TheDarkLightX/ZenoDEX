# Zeno Oracle Polytope Compiler - 2026-06-27

## Executive Result

This artifact turns the pointwise oracle economic-security verifier into exact one-field integer feasibility intervals.
Each interval is checked at the lower wall, upper wall, just below, and just above against `verify_economic_security_envelope`.

Overall status: `ok=True`.

Authority boundary: the compiler emits advisory interval evidence and Tau-facing facts. The pointwise verifier remains authoritative.

## Intervals

| field | lower | upper | reason |
| --- | ---: | ---: | --- |
| `notional_value_e8` | `50000000000` | `1000000000000000000000000000000` | notional must cover max_extractable_value_e8 |
| `max_extractable_value_e8` | `50000000000` | `62500000000` | max extractable must cover expected cheat gain and stay below the attack-cost wall |
| `attack_cost_floor_e8` | `60000000000` | `1000000000000000000000000000000` | attack cost floor must exceed max_extractable_value_e8 plus required margin |
| `required_attack_margin_bps` | `0` | `5000` | attack margin cannot exceed what the fixed attack_cost_floor_e8 supports |
| `reporter_reward_per_report_e8` | `25000000` | `40000000` | per-report reward must cover honest cost plus risk and fit the reward budget |
| `reporter_reward_budget_e8` | `90000000` | `1000000000000000000000000000000` | reward budget must cover reward_per_report times reporter_count |
| `reporter_count` | `1` | `4` | reporter count must fit the fixed reward budget |
| `expected_cheat_gain_e8` | `0` | `50000000000` | expected cheat gain must fit both max_extractable_value_e8 and slash deterrence |
| `reporter_bond_required_e8` | `120000000000` | `1000000000000000000000000000000` | bond times slash fraction must cover expected cheat gain plus deterrence margin |
| `slash_fraction_bps` | `2400` | `10000` | slash fraction must make the fixed bond cover expected cheat gain plus margin |
| `deterrence_margin_bps` | `0` | `15000` | deterrence margin cannot exceed what the fixed slash amount supports |
| `dispute_reward_e8` | `0` | `20000000` | dispute reward must not exceed dispute budget |
| `dispute_budget_e8` | `10000000` | `1000000000000000000000000000000` | dispute budget must cover dispute reward |
| `fee_paid_e8` | `100000000` | `1000000000000000000000000000000` | fee paid must cover reporter, treasury, and burn fee shares |
| `reporter_fee_share_e8` | `0` | `30000000` | reporter fee share must fit the fixed fee budget |
| `treasury_fee_share_e8` | `0` | `40000000` | treasury fee share must fit the fixed fee budget |
| `burn_fee_share_e8` | `0` | `30000000` | burn fee share must fit the fixed fee budget |

## Boundary Replay

- Boundary samples: `68/68` matched the pointwise verifier expectation.
- Samples include accepted walls and rejected just-outside values for every interval.

## Tau Envelope Facts

- `oracle_param_update_requested`: `True`
- `interval_nonempty`: `True`
- `honest_challenge_profitable_interval_ok`: `True`
- `frivolous_dispute_deterrence_interval_ok`: `True`
- `slash_covers_cheat_gain_interval_ok`: `True`
- `point_verifier_parity_ok`: `True`
- `all_boundary_walls_checked`: `True`
- `mev_assumption_declared`: `True`
- `probability_assumption_declared`: `True`
- `no_oracle_update_authority`: `True`
- `fail_closed_default_ok`: `True`

## Non-Claims

- The compiler does not estimate MEV, challenge probability, or market truth.
- The compiler does not authorize oracle updates.
- Intervals are exact for one varied field at a time with other fields fixed to the base envelope.

## Replay

```bash
python3 tools/zenodex_oracle_polytope_compiler_20260627.py
```
