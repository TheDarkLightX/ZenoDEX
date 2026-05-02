# Zeno Oracle Token Budget V1

Status: first public local verifier format for Oracle token budget transitions.

Zeno Oracle requires a token in the MVP because permissionless reporters and
challengers need explicit compensation and slash exposure. The safety rule is
that the token surface must be budget-backed before it is incentive-rich.

The current local verifier is:

```text
python3 tools/zenodex_oracle_budget.py verify <transition>
```

## Budget Transition Shape

```json
{
  "schema": "zenodex.oracle.budget_transition.v1",
  "query_budget_remaining": 1000,
  "query_reward_paid": 250,
  "reporter_bond_available": 2000,
  "reporter_slash_paid": 100,
  "dispute_bond_available": 500,
  "dispute_slash_paid": 50,
  "fee_paid": 300,
  "reporter_fee_share": 120,
  "treasury_fee_share": 90,
  "burn_fee_share": 90
}
```

Allowed fields are exactly:

- `schema`
- `query_budget_remaining`
- `query_reward_paid`
- `reporter_bond_available`
- `reporter_slash_paid`
- `dispute_bond_available`
- `dispute_slash_paid`
- `fee_paid`
- `reporter_fee_share`
- `treasury_fee_share`
- `burn_fee_share`

All numeric fields must be non-negative integers. Unknown fields reject. Local
files above `250_000` bytes are treated as `inconclusive` before JSON parsing.

## Safety Laws

```text
query_reward_paid <= query_budget_remaining
reporter_slash_paid <= reporter_bond_available
dispute_slash_paid <= dispute_bond_available
reporter_fee_share + treasury_fee_share + burn_fee_share <= fee_paid
```

Plain English: a reward cannot exceed the query budget, a slash payout cannot
exceed the relevant bond, and the fee split cannot spend more than the fee that
was paid.

## Result Shape

```json
{
  "schema": "zenodex.oracle.budget_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "query_reward_paid": 250,
  "reporter_slash_paid": 100,
  "dispute_slash_paid": 50,
  "fee_paid": 300,
  "fee_spend_total": 300,
  "errors": [],
  "not_claimed": [
    "does_not_claim_token_price_appreciation",
    "does_not_claim_reporter_honesty",
    "does_not_claim_production_oracle_token_live"
  ]
}
```

Statuses:

| Status | Meaning |
| --- | --- |
| `accepted` | The local transition satisfies the V1 budget laws. |
| `rejected` | The transition parsed, but at least one budget law failed. |
| `inconclusive` | The verifier could not load or parse the transition safely. |

## Replay Commands

Generate and verify a sample transition:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_budget.py sample --output "$tmp/budget.json"
python3 tools/zenodex_oracle_budget.py verify "$tmp/budget.json"
rm -rf "$tmp"
```

## Non-Claims

This verifier does not claim:

- the Oracle token will appreciate;
- reporters are honest;
- a live reporter network exists;
- the final tokenomics are complete;
- all future fee, rebate, bond, dispute, or governance flows are covered.

The claim is narrower: this first budget shell rejects token transitions that
try to spend more than the explicit budget, bond, or fee envelope.
