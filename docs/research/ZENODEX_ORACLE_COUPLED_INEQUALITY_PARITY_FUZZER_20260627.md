# Zeno Oracle Coupled Inequality Parity Fuzzer - 2026-06-27

## Executive Result

This bounded deterministic fuzzer compares the coupled inequality certificate against the pointwise oracle economic-security verifier.
Cases: `594`. Accepted: `11`. Rejected: `583`. Mismatches: `0`. Overall: `ok=True`.

Authority boundary: the fuzzer is evidence for certificate/verifier parity; it does not authorize oracle updates.

## Case Families

| family | cases | accepted | rejected | mismatches |
| --- | ---: | ---: | ---: | ---: |
| `baseline` | `1` | `1` | `0` | `0` |
| `metadata_domain` | `5` | `0` | `5` | `0` |
| `random_economic` | `512` | `0` | `512` | `0` |
| `single_field_domain` | `76` | `10` | `66` | `0` |

## Error Coverage

- `action_kind_must_be_token`
- `attack_cost_floor_below_required_margin`
- `attack_cost_floor_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `burn_fee_share_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `consumer_module_must_be_token`
- `deterrence_margin_bps_must_be_int_between_0_and_1000000`
- `dispute_budget_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `dispute_reward_budget_exceeded`
- `dispute_reward_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `economic_security_schema_mismatch`
- `expected_cheat_gain_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `expected_cheat_gain_exceeds_extractable_value`
- `extractable_value_exceeds_notional`
- `fee_paid_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `fee_shares_exceed_fee_paid`
- `honest_reporter_cost_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `honest_reporter_risk_premium_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `max_extractable_value_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `notional_value_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `query_id_must_be_sha256`
- `reporter_bond_required_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `reporter_count_must_be_int_between_1_and_1024`
- `reporter_fee_share_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `reporter_reward_below_honest_cost_plus_risk`
- `reporter_reward_budget_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `reporter_reward_budget_exceeded`
- `reporter_reward_per_report_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `required_attack_margin_bps_must_be_int_between_0_and_1000000`
- `slash_deterrence_below_required_margin`
- `slash_fraction_bps_must_be_int_between_0_and_10000`
- `treasury_fee_share_e8_must_be_int_between_0_and_1000000000000000000000000000000`
- `unknown_economic_security_field:hidden_mint`

## Non-Claims

- The fuzzer is bounded and deterministic; it is not exhaustive over the full integer domain.
- The pointwise verifier remains authoritative.
- The fuzzer checks parity of accept/reject and reject-reason sets, not oracle truth.

## Replay

```bash
python3 tools/zenodex_oracle_coupled_inequality_parity_fuzzer_20260627.py --seed 20260627 --random-cases 512
```
