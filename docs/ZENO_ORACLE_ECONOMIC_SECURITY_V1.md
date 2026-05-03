# Zeno Oracle Economic Security V1

Status: first public local verifier format for Oracle economic security
envelopes.

This document describes the narrow economic envelope currently accepted by:

```text
python3 tools/zenodex_oracle_economic_security.py verify <envelope>
```

The structural Oracle verifiers answer whether receipts, policies, profiles,
and adapter bindings are well-formed. This envelope answers a different
question: whether the declared economic assumptions have enough margin for a
critical query/action pair.

## Envelope Shape

```json
{
  "schema": "zenodex.oracle.economic_security_envelope.v1",
  "query_id": "sha256:...",
  "consumer_module": "zenodex.perps",
  "action_kind": "settle_epoch",
  "notional_value_e8": 1000000000000,
  "max_extractable_value_e8": 50000000000,
  "attack_cost_floor_e8": 75000000000,
  "required_attack_margin_bps": 2000,
  "reporter_count": 3,
  "reporter_reward_budget_e8": 120000000,
  "reporter_reward_per_report_e8": 30000000,
  "honest_reporter_cost_e8": 20000000,
  "honest_reporter_risk_premium_e8": 5000000,
  "reporter_bond_required_e8": 250000000000,
  "slash_fraction_bps": 5000,
  "expected_cheat_gain_e8": 50000000000,
  "deterrence_margin_bps": 2000,
  "dispute_reward_e8": 10000000,
  "dispute_budget_e8": 20000000,
  "fee_paid_e8": 100000000,
  "reporter_fee_share_e8": 30000000,
  "treasury_fee_share_e8": 40000000,
  "burn_fee_share_e8": 30000000
}
```

All amounts are non-negative integer `e8` units. Basis-point fields are
integers. `slash_fraction_bps` is capped at `10000`; margin fields may exceed
`10000` to express large safety multiples.

## Economic Laws

The attack-cost law is:

```text
required_attack_cost_e8 :=
  ceil(max_extractable_value_e8 * (10000 + required_attack_margin_bps) / 10000)

attack_cost_floor_e8 >= required_attack_cost_e8
```

Plain English: the declared minimum cost to manipulate the oracle must exceed
the declared maximum extractable value by the required margin.

The honest-reward law is:

```text
required_reward_per_report_e8 :=
  honest_reporter_cost_e8 + honest_reporter_risk_premium_e8

reporter_reward_per_report_e8 >= required_reward_per_report_e8
reporter_reward_per_report_e8 * reporter_count <= reporter_reward_budget_e8
```

Plain English: honest reporting must be paid enough to cover declared cost and
risk premium, and total reporter rewards must fit inside the declared reward
budget.

The slash-deterrence law is:

```text
slash_amount_e8 :=
  floor(reporter_bond_required_e8 * slash_fraction_bps / 10000)

required_deterrence_slash_e8 :=
  ceil(expected_cheat_gain_e8 * (10000 + deterrence_margin_bps) / 10000)

slash_amount_e8 >= required_deterrence_slash_e8
```

Plain English: under the declared bond and slash fraction, the slashable amount
must exceed the declared cheating gain by the deterrence margin.

The budget laws are:

```text
max_extractable_value_e8 <= notional_value_e8
expected_cheat_gain_e8 <= max_extractable_value_e8
dispute_reward_e8 <= dispute_budget_e8
reporter_fee_share_e8 + treasury_fee_share_e8 + burn_fee_share_e8 <= fee_paid_e8
```

Plain English: the envelope cannot claim more extractable value than notional,
cannot claim cheating gain above extractable value, cannot pay dispute rewards
above dispute budget, and cannot split more fees than were paid.

## Result Shape

Verification returns computed values as well as the accept/reject status:

```json
{
  "schema": "zenodex.oracle.economic_security_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "required_attack_cost_e8": 60000000000,
  "required_reporter_reward_per_report_e8": 25000000,
  "total_reporter_reward_e8": 90000000,
  "slash_amount_e8": 125000000000,
  "required_deterrence_slash_e8": 60000000000,
  "fee_spend_total_e8": 100000000,
  "errors": []
}
```

## Replay Commands

Generate and verify a minimal accepted envelope:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_economic_security.py sample --output "$tmp/economics.json"
python3 tools/zenodex_oracle_economic_security.py verify "$tmp/economics.json"
rm -rf "$tmp"
```

Run deterministic economic chaos replay:

```bash
python3 tools/zenodex_oracle_economic_security_chaos.py
```

The current economic chaos lane covers `14` named attack-cost, reward, budget,
slash, fee, schema, hidden-field, and type-confusion disaster shapes. Details
are tracked in [ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- the attack-cost estimate is correct;
- token price will appreciate;
- reporters are honest;
- market prices are true;
- a production Oracle network is live.

The claim is narrower: if the declared numbers are accepted, they satisfy the
integer budget and margin laws above.
