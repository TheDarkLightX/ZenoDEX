# ZenoDEX Yield-like Funding Shapes V1

This note replaces a blanket passive-yield ban with a typed funding taxonomy.
The core rule is positive: earned, source-verified, source-bounded,
non-guaranteed, non-profit-share, non-future-entrant flows can enter payout
math. Passive, guaranteed, profit-share, future-entrant, or discretionary
managerial-yield flows remain rejected.

## Legal-facing Posture

This is a mathematical and engineering note, not legal advice. Counsel still
needs to review every live source, interface, disclosure, jurisdiction, and
marketing claim.

The current regulatory signals support a narrower distinction than
`yield = bad`. SEC 2026-30 says the SEC clarified federal-securities treatment
for airdrops, protocol mining, protocol staking, wrapping, and token taxonomy:

<https://www.sec.gov/newsroom/press-releases/2026-30-sec-clarifies-application-federal-securities-laws-crypto-assets>

The SEC protocol-staking statement describes validators as earning protocol
rewards and transaction-fee shares for validation services:

<https://www.sec.gov/newsroom/speeches-statements/statement-certain-protocol-staking-activities-052925>

The SEC liquid-staking statement is useful for pass-through receipt design, but
only where the activity stays administrative or ministerial and no provider
guarantees or sets rewards:

<https://www.sec.gov/newsroom/speeches-statements/corpfin-certain-liquid-staking-activities-080525>

The CLARITY Act remains market-structure direction unless enacted and
implemented. Treat it as design context, not a live blanket safe harbor.

## Whitelist

```text
AllowedYieldLike :=
  protocol_service_reward
  OR protocol_fee_rebate
  OR liquidity_service_fee
  OR protocol_staking_security_reward
  OR verified_work_bounty
  OR treasury_operating_revenue
  OR liquid_staking_pass_through
  OR deflationary_burn_source
```

The proof surface is:

```text
AllowedSource(source) :=
  kind_allowed
  AND source_verified
  AND source_bounded
  AND no_guaranteed_return
  AND no_profit_share
  AND no_future_entrant
  AND disclosure_met
  AND (requires_work(kind) -> earned_by_service)
  AND (kind = liquid_staking_pass_through -> ministerial_only)
```

## Rejected Shapes

```text
ForbiddenPassiveYield :=
  hold_to_earn
  OR guaranteed_APY
  OR profit_share_right
  OR future_entrant_inflow
  OR discretionary_managerial_yield
```

These are rejected independently by kind and by safety flags:

```text
no_guaranteed_return = false -> not admitted
no_profit_share = false -> not admitted
no_future_entrant = false -> not admitted
```

## Payout Formula

Let:

```text
A_t = allocable budget after reserves and insurance
```

For each payout:

```text
payout_i,t <= min(
  verified_value_i,t,
  source_cap_i,t,
  treasury_cap_i,t,
  sybil_cap_i,t,
  scope_cap_i,t,
  allocable_cap_i,t
)

allocable_cap_i,t <= A_t
```

The global gate is:

```text
positive payout
  -> source kind is allowed
  -> source is bounded
  -> no guaranteed return
  -> no profit share
  -> no future entrant dependency
  -> reserve target is met
  -> payout <= realized surplus
```

## Shape Formulas

### Protocol service reward

```text
reward_i,t + penalties_i,t <= base_reward_i,t + fee_share_i,t
```

Use for validators, oracle reporters, bridge sentinels, proof verifiers, or
keepers that perform measurable protocol service and can be penalized.

### Fee rebate

```text
rebate_i,t <= fees_paid_i,t
```

This is a cost rebate, not a profit claim.

### Liquidity service fee

```text
sum(lp_payouts_t) <= realized_trade_fees_t
```

LP payments must come from realized trade fees and disclosed inventory risk.

### Verified work bounty

```text
work_payout_i,t <= min(verified_value_i,t, scope_cap_i,t, sybil_cap_i,t, A_t)
```

Use for humans and agents only after proof, scope, anti-sybil, and value review.

### Treasury operating revenue

```text
ops_budget_t <= treasury_net_operating_income_t
```

Token holders should not receive a claim on treasury revenue as a profit share.

### Liquid-staking pass-through receipt

```text
receipt_claim_t + provider_fees_t + slashing_losses_t
  <= underlying_assets_t + accrued_protocol_rewards_t
```

The provider must remain ministerial and cannot guarantee or set the reward.

### Deflationary burn

```text
burn_t <= allocable_budget_t
```

Do not market burn as guaranteed price appreciation.

## Replay

The public Lean theorem surface is:

```text
lean-mathlib/Proofs/ZenoDEXYieldLikeFundingSafety.lean
```

Replay:

```bash
cd lean-mathlib && lake env lean Proofs/ZenoDEXYieldLikeFundingSafety.lean
pytest -q tests/formal/test_lean_zenodex_yield_like_funding_safety.py
```
