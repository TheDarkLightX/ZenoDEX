---
title: FIRE_REVENUE_SURFACE_ATLAS
type: note
permalink: autonomous-tau-dex-review/docs/fire-revenue-surface-atlas
---

# FIRE Revenue Surface Atlas

This document answers the concrete tokenomics question: where does protocol
revenue actually come from?

The answer should not be "staking." Staking is an allocation and commitment
surface. Revenue comes from fee surfaces where the protocol creates measurable
execution, protection, automation, liquidity, or verification value.

## Revenue Surface Law

For normal user-facing surfaces:

```text
UserFee <= MeasuredUserValue
```

In plain English: the user should not pay more than the value the surface
creates. If the surface cannot measure value, its bps rate should be tiny,
bundled, or turned off.

For protocol surplus surfaces:

```text
ProtocolRevenue <= CapturableProtocolSurplus
```

In plain English: market-maker bots, arbitrage recapture, and solver auctions
can fund the protocol without charging the user directly, but only to the
extent the surplus is real and receipt-backed.

For staking rewards:

```text
StakeRewards <= RevenueBackedRewardBudget + ExplicitSubsidy
```

In plain English: staking distributes funded budget. It is not itself a revenue
source.

## Concrete Fee Surfaces

| Surface | Who pays | Fee basis | Why it can be worth paying |
| --- | --- | --- | --- |
| Swap protocol rake | swap user | bps of notional | baseline use of the DEX |
| Route surplus capture | swap user | bps of measured output improvement | user keeps part of a better route |
| Exact-out savings capture | swap user | bps of saved input | same output costs less than baseline |
| COW/batch solver surplus | solver/user surplus | bps of measured batch surplus | solver improves settlement quality |
| MEV/protection receipt | swap user/integrator | low bps of protected notional or surplus | stale/replay/MEV risk is reduced |
| Automation orders | user | bps of executed notional or saved manual cost | DCA, TWAP, limit, recurring execution |
| Pro certificate/API | integrator | bps of routed volume or surplus | wallets/apps need audit-grade evidence |
| Integrator routing | wallet/app/user | bps of routed volume or surplus | distribution and UX improve flow |
| Treasury market-maker bot | market surplus | bps of bot profit | protocol earns from providing liquidity |
| Arbitrage recapture auction | arbitrageur/solver | bps of auctioned surplus | leakage becomes treasury revenue |
| LP loss-cover premium | protection buyer | bps premium | protocol sells bounded protection |
| Early-exit penalty | broken commitment | capped penalty | protects commitment schedules |

Early-exit penalties are intentionally last. They are not healthy primary
revenue. The v190 oracle rejects policies that depend materially on penalty
revenue.

## Revenue To Deflation

```text
NetRevenue
  = GrossRevenue
  - solver_rewards
  - claims_cost
  - operating_cost
```

In plain English: only net revenue can safely fund burns, treasury, security,
liquidity support, rebates, and lock rewards.

```text
BurnBudget > SubsidyEmissions -> TotalSupply decreases
```

In plain English: lockups reduce liquid float, but only burn greater than
emission reduces total supply.

## Staking User Experience

The first staking product should be a revenue-backed commitment vault:

1. User chooses amount and lock duration.
2. The vault mints non-transferable commitment shares.
3. Protocol revenue funds a reward pool.
4. The reward pool is allocated pro-rata by commitment shares.
5. Rewards are never guaranteed and never exceed funded budget.
6. Early exit is allowed only under a capped, predeclared penalty.

The UI should show:

- current funded reward pool,
- total active commitment shares,
- user's share of active shares,
- maturity date,
- early-exit penalty,
- whether rewards are fee-funded or subsidy-funded.

## v190 Bounded Oracle

The executable cycle is:

```text
experiments/math_object_innovation_v190/
```

It searches a bounded bps grid over concrete fee surfaces and rejects:

- zero-fee policies that cannot fund the protocol,
- extractive notional fees that make user net value negative,
- wash-rebate farms,
- passive-subsidy staking,
- penalty-dependent revenue.

The corresponding Lean algebra packet is:

```text
lean-mathlib/Proofs/RevenueSurfaceSafety.lean
```

That proof covers the small algebraic skeleton. The executable oracle covers
bounded parameter search. Production deployment would still need runtime
receipts for measured value, surplus, wash score, and fee attribution.

Current v190 replay:

```text
candidate_policy_count = 155527
survivor_count = 5510
model_audit.total_model_invariant_failures = 0
mutation_receipt.detected_count = 5 / 5
```

Best bounded survivor:

```text
policy = grid_090937_max_burn_guarded
net_protocol_revenue = 5322
burn_budget = 4257
deflation_margin = 4257
penalty_dependency_bps = 0
```

Launch-shaped survivor:

```text
policy = fee_surface_launch
net_protocol_revenue = 2258
burn_budget = 1016
total_user_net_value = 3669
```

In plain English: there are revenue-generating fee surfaces that survive the
bounded model without leaning on penalty revenue or passive emissions. The next
question is calibration against real quote/action corpora.

The mutation receipt deliberately corrupts the model in five ways and confirms
the audit layer detects each corruption. That does not prove the economics are
complete; it does prove the accounting audit is sensitive to known-bad bug
classes.
