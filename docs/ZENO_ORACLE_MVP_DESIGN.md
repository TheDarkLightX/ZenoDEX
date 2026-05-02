# Zeno Oracle MVP Design

Status: public design snapshot, not a live production oracle.

Zeno Oracle is the planned oracle extension for ZenoDEX-critical reads. Its
purpose is not to publish a naked price and ask consumers to trust it. Its
purpose is to publish a value together with the receipts needed to decide
whether that value is safe enough for a specific use such as settlement,
liquidation, minting, trigger execution, or guarded routing.

The public MVP target is permissionless-human reporting. An internal devnet may
start with allowlisted reporters, but that is not the full market MVP.

```text
CriticalOracleUse -> AcceptedReadReceipt
AcceptedReadReceipt :=
  QuerySpecBound
  and AggregateBound
  and ConsumerPolicyBound
  and FreshEnough
  and DisputeClear
  and UncertaintyAccepted
```

Plain English: ZenoDEX should never consume a raw oracle value in a critical
state transition. It should consume only a receipt that binds the query
semantics, aggregate value, consumer policy, freshness window, dispute status,
and uncertainty checks.

## MVP Components

1. Query registry

Defines canonical query semantics: asset pair, unit, scale, source policy,
reporter policy, aggregation policy, freshness policy, movement policy, dispute
policy, token policy, and query ID.

2. Reporter registry

Tracks reporter identity, signing key, active status, bond state, weight, and
operator grouping. Public reporting requires token-backed registration and bond
receipts.

3. Signed report lane

Accepts reports only when schema, canonical hash, reporter signature, query
binding, source timing, value type, and reporter sequence checks pass.

4. Aggregate receipt lane

Builds deterministic aggregates from accepted reports. The first concrete MVP
kernel is an odd-cardinality median, with `median_3` as the first small,
auditable target.

5. Read receipt lane

Turns an aggregate into a consumer-specific accepted read. This is where
freshness, evidence class, dispute status, price movement, uncertainty, and
attack-cost constraints are checked.

6. Critical consumer action lane

Binds the accepted read to the specific downstream action. A perps settlement,
liquidation, zUSD mint, or trigger execution cannot borrow a receipt from a
different action, query, value hash, epoch, or policy.

7. Token incentive lane

Permissionless reporting needs on-protocol incentives. The MVP token surface
includes reporter bonds, query reward budgets, reporter rewards, dispute bonds,
slash receipts, and treasury/burn fee splits.

## Evidence Classes

Zeno Oracle should label oracle data by evidence class rather than pretending
all values are equally safe.

| Class | Meaning | Critical Use |
| --- | --- | --- |
| `O0` | raw unchecked report | never |
| `O1` | accepted report | never |
| `O2` | delayed/dev final report | devnet only |
| `O3` | robust aggregate with reporter/source policy receipts | yes |
| `O4` | proof-backed provenance or computation | future |
| `O5` | cross-checked independent mechanisms | future |

Critical ZenoDEX consumers should default to `O3` or higher. `O2` is useful for
engineering previews, UI display, and dry runs, but it should not authorize
production settlement, liquidation, minting, or trigger execution.

## Uncertainty Math

For the first `median_3` price model, let the accepted reporter prices be:

```text
p0, p1, p2 > 0
m := median(p0, p1, p2)
confidence_e8 := max(|p0 - m|, |p1 - m|, |p2 - m|)
deviation_bps := ceil(confidence_e8 * 10000 / m)
```

Plain English: the aggregate is the median. The confidence radius is the
largest included-report distance from that median. The deviation bps converts
that radius into basis points, so consumers can set explicit risk limits.

A critical read is high-uncertainty when any required bound fails:

```text
HighUncertainty :=
  m <= 0
  or confidence_e8 * 10000 > max_confidence_bps * m
  or confidence_e8 * 10000 > max_deviation_bps * m
  or attack_cost_floor_e8 <= max_extractable_value_e8
```

This makes uncertainty consumer-specific. A value can be acceptable for a chart
and still too uncertain for liquidation.

## Token Incentive Contract

The oracle token is part of the public MVP, not an optional decoration, because
permissionless humans need a reason to report, monitor, dispute, and accept
slash risk.

The minimum rule is budget safety:

```text
RewardPaid <= VerifiedQueryBudgetRemaining
SlashPaid <= VerifiedBondAvailable
FeeSplitTotal <= FeePaid
```

Plain English: rewards, slashes, burns, and treasury shares must come from
explicit verified balances. The Oracle should not mint trust by promising
unbounded rewards.

## Disaster States The MVP Is Designed To Block

- raw signed report feeds a critical action;
- wrong query ID is consumed;
- semantic aliasing changes query meaning;
- stale or future report is accepted;
- zero or malformed price is consumed;
- reporter sequence replay is accepted;
- signature verifies over the wrong payload;
- unauthorized or under-bonded reporter is accepted;
- source evidence is borrowed across reports;
- aggregate is accepted without quorum;
- aggregate value is borrowed from another report set;
- open or unresolved dispute feeds a critical read;
- weak evidence label is treated as stronger evidence;
- confidence or deviation is erased before critical use;
- attack-cost check is omitted for a critical consumer;
- consumer action swaps root-membership witness roles;
- reward payout borrows evidence from another context;
- reward budget overdrafts;
- bond withdrawal under-bonds an active reporter;
- slash settlement exceeds or misbinds bond state.

## What Is Not Claimed Yet

This document is a design snapshot. It does not claim that:

- a public Zeno Oracle network is live;
- the oracle token economics are finalized;
- subjective disputes are fully solved;
- every source is honest or independent;
- median price equals true market price;
- every future consumer action is already integrated.

The production milestone is a public replay gate that recomputes accepted reads
and critical-action receipts from a clean checkout, plus a reporter binary that
ordinary users can run.
