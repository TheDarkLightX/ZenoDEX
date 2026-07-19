# Zeno Oracle MVP Design

Status: public design snapshot, not a live production oracle.

Zeno Oracle is the planned oracle extension for ZenoDEX-critical reads. Its
purpose is not to publish a naked price and ask consumers to trust it. Its
purpose is to publish a value together with the receipts needed to decide
whether that value is safe enough for a specific use such as settlement,
liquidation, minting, trigger execution, or guarded routing.

The public MVP target is permissionless-human reporting. An internal devnet may
start with allowlisted reporters, but that is not the full market MVP.

The first concrete public receipt format is
[ZENO_ORACLE_RECEIPT_FORMAT_V1.md](ZENO_ORACLE_RECEIPT_FORMAT_V1.md).
The first concrete public token budget format is
[ZENO_ORACLE_TOKEN_BUDGET_V1.md](ZENO_ORACLE_TOKEN_BUDGET_V1.md).
The first concrete public reporter lifecycle format is
[ZENO_ORACLE_REPORTER_LIFECYCLE_V1.md](ZENO_ORACLE_REPORTER_LIFECYCLE_V1.md).
The first concrete public signed-report format is
[ZENO_ORACLE_SIGNED_REPORT_V1.md](ZENO_ORACLE_SIGNED_REPORT_V1.md).
The first concrete public report-admission bridge format is
[ZENO_ORACLE_REPORT_ADMISSION_V1.md](ZENO_ORACLE_REPORT_ADMISSION_V1.md).
The first concrete public aggregate format is
[ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md](ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md).
The first concrete public aggregate-from-admission format is
[ZENO_ORACLE_ADMITTED_MEDIAN3_V1.md](ZENO_ORACLE_ADMITTED_MEDIAN3_V1.md).
The first concrete public aggregate-to-read bridge format is
[ZENO_ORACLE_AGGREGATE_READ_V1.md](ZENO_ORACLE_AGGREGATE_READ_V1.md).
The first concrete public aggregate-to-action adapter bridge format is
[ZENO_ORACLE_AGGREGATE_ADAPTER_V1.md](ZENO_ORACLE_AGGREGATE_ADAPTER_V1.md).
The first concrete public source-diversity format is
[ZENO_ORACLE_SOURCE_DIVERSITY_V1.md](ZENO_ORACLE_SOURCE_DIVERSITY_V1.md).
The first concrete public query-policy format is
[ZENO_ORACLE_QUERY_POLICY_V1.md](ZENO_ORACLE_QUERY_POLICY_V1.md).
The first concrete public adapter format is
[ZENO_ORACLE_ADAPTER_V1.md](ZENO_ORACLE_ADAPTER_V1.md).
The first concrete public consumer-profile catalog is
[ZENO_ORACLE_CONSUMER_PROFILES_V1.md](ZENO_ORACLE_CONSUMER_PROFILES_V1.md).
The first concrete public economic security envelope is
[ZENO_ORACLE_ECONOMIC_SECURITY_V1.md](ZENO_ORACLE_ECONOMIC_SECURITY_V1.md).
The first concrete public feed-registry format is
[ZENO_ORACLE_FEED_REGISTRY_V1.md](ZENO_ORACLE_FEED_REGISTRY_V1.md).
The first concrete public CLI wrapper is
[ZENO_ORACLE_CLI_V1.md](ZENO_ORACLE_CLI_V1.md).

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
policy, source-diversity policy, token policy, and query ID.

The first local feed-registry shell makes that query layer executable: it
accepts feed definitions only when the query spec, source-diversity receipt,
aggregate policy, freshness/deviation limits, evidence floor, and content
hashes all agree.

2. Reporter registry

Tracks reporter identity, signing key, active status, bond state, weight, and
operator grouping. Public reporting requires token-backed registration and bond
receipts.

3. Signed report lane

Accepts reports only when schema, canonical hash, reporter signature, query
binding, source timing, value type, and reporter sequence checks pass. The
current shell verifies BLS signatures and a reporter-local previous-report
chain before reports are eligible for aggregation.

4. Report admission lane

Bridges signed reports to reporter lifecycle and source-diversity receipts. A
report can be admitted only when the signed payload, lifecycle submit event,
and declared source policy bind to the same reporter, query, report ID, source,
payload hash, and freshness window.

5. Aggregate receipt lane

Builds deterministic aggregates from accepted reports. The first concrete MVP
kernel is an odd-cardinality median, with `median_3` as the first small,
auditable target. The current `median_3` shell embeds a source-diversity
receipt so source IDs are tied to operator, venue, data-family, transport, and
jurisdiction classifications.

The admitted-median3 shell tightens this lane by requiring each aggregate input
to be an accepted report-admission bundle. It then recomputes the median,
confidence radius, deviation bps, and observed epoch from exactly one admitted
report per admission.

6. Read receipt lane

Turns an aggregate into a consumer-specific accepted read. This is where
freshness, evidence class, dispute status, price movement, uncertainty, and
attack-cost constraints are checked.

The aggregate-read bridge now binds the admitted aggregate value, confidence
radius, deviation bps, observed epoch, report count, and admission count into
the read `value_hash` consumed by the generic receipt bundle.

7. Critical consumer action lane

Binds the accepted read to the specific downstream action. A perps settlement,
liquidation, zUSD mint, or trigger execution cannot borrow a receipt from a
different action, query, value hash, epoch, or policy.

The aggregate-adapter bridge now checks the complete local path from admitted
aggregate to aggregate-derived read bundle to concrete action/profile binding.
Perps `settle_epoch` paths and guarded routing quote APIs have runtime hooks.
When configured to require an Oracle bridge, isolated,
2-party clearinghouse, and 3-party transfer clearinghouse settlement reject
missing, unverified, rejected, wrong-query, wrong-profile, wrong-action, or
wrong-runtime-action-ID aggregate-adapter bridges before state changes. The
exact-in and exact-out
guarded routing quote APIs apply it to `zenodex.routing / guarded_quote`,
including the route request, route policy, routing reference-price query,
official routing profile, and pool snapshot hash. The deleted unsigned zUSD API
provides no release evidence; production zUSD mint and liquidation remain
blocked until the monetary bridge has an equivalent committed lifecycle.

8. Token incentive lane

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
- feed registry admits duplicate or hash-forged feed definitions;
- feed registry accepts a base/quote alias or unsupported aggregate policy;
- stale or future report is accepted;
- zero or malformed price is consumed;
- reporter sequence replay is accepted;
- signature verifies over the wrong payload;
- signed report sequence skips or points at the wrong predecessor;
- lifecycle submit event does not match the signed report;
- signed source is outside the declared source-diversity receipt;
- aggregate uses reports that did not pass report admission;
- duplicate admission/report/reporter/source is aggregated;
- accepted read value hash does not match the admitted aggregate;
- concrete action/profile binding does not match the aggregate-derived read;
- unauthorized or under-bonded reporter is accepted;
- source evidence is borrowed across reports;
- three source strings collapse to one operator, venue, data family,
  transport, or jurisdiction bucket;
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
- declared source classifications are externally audited;
- median price equals true market price;
- every future consumer action is already integrated.

The production milestone is a public replay gate that recomputes accepted reads
and critical-action receipts from a clean checkout, plus a reporter binary that
ordinary users can run.
