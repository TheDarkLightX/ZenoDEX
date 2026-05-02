# Zeno Oracle MVP Status

Status: public branch summary for the local Oracle MVP shell.

This page summarizes what exists now on the public Zeno Oracle MVP branch. It
is a status page, not a production launch claim.

## Implemented Local Surfaces

| Surface | Artifact | Replay |
| --- | --- | --- |
| Critical read receipt verifier | `tools/zenodex_oracle.py` | `python3 tools/zenodex_oracle.py verify <bundle>` |
| Receipt chaos replay | `tools/zenodex_oracle_chaos.py` | `python3 tools/zenodex_oracle_chaos.py` |
| Token budget verifier | `tools/zenodex_oracle_budget.py` | `python3 tools/zenodex_oracle_budget.py verify <transition>` |
| Token budget chaos replay | `tools/zenodex_oracle_budget_chaos.py` | `python3 tools/zenodex_oracle_budget_chaos.py` |
| Reporter lifecycle verifier | `tools/zenodex_oracle_reporter_lifecycle.py` | `python3 tools/zenodex_oracle_reporter_lifecycle.py verify <trace>` |
| Reporter lifecycle chaos replay | `tools/zenodex_oracle_reporter_lifecycle_chaos.py` | `python3 tools/zenodex_oracle_reporter_lifecycle_chaos.py` |
| Median3 aggregate verifier | `tools/zenodex_oracle_median3.py` | `python3 tools/zenodex_oracle_median3.py verify <aggregate>` |
| Median3 aggregate chaos replay | `tools/zenodex_oracle_median3_chaos.py` | `python3 tools/zenodex_oracle_median3_chaos.py` |
| Source diversity verifier | `tools/zenodex_oracle_source_diversity.py` | `python3 tools/zenodex_oracle_source_diversity.py verify <receipt>` |
| Source diversity chaos replay | `tools/zenodex_oracle_source_diversity_chaos.py` | `python3 tools/zenodex_oracle_source_diversity_chaos.py` |
| Query-policy verifier | `tools/zenodex_oracle_query_policy.py` | `python3 tools/zenodex_oracle_query_policy.py verify <trace>` |
| Query-policy chaos replay | `tools/zenodex_oracle_query_policy_chaos.py` | `python3 tools/zenodex_oracle_query_policy_chaos.py` |
| ZenoDEX adapter verifier | `tools/zenodex_oracle_adapter.py` | `python3 tools/zenodex_oracle_adapter.py verify --action <action> --bundle <bundle>` |
| ZenoDEX adapter chaos replay | `tools/zenodex_oracle_adapter_chaos.py` | `python3 tools/zenodex_oracle_adapter_chaos.py` |
| Consumer profile catalog verifier | `tools/zenodex_oracle_consumer_profiles.py` | `python3 tools/zenodex_oracle_consumer_profiles.py verify <catalog>` |
| Consumer profile catalog chaos replay | `tools/zenodex_oracle_consumer_profiles_chaos.py` | `python3 tools/zenodex_oracle_consumer_profiles_chaos.py` |
| Economic security verifier | `tools/zenodex_oracle_economic_security.py` | `python3 tools/zenodex_oracle_economic_security.py verify <envelope>` |
| Economic security chaos replay | `tools/zenodex_oracle_economic_security_chaos.py` | `python3 tools/zenodex_oracle_economic_security_chaos.py` |

## Current Replay Counts

```text
receipt_chaos_case_count = 28
receipt_chaos_rejected_count = 28
receipt_chaos_failed_count = 0

budget_chaos_case_count = 12
budget_chaos_rejected_count = 12
budget_chaos_failed_count = 0

reporter_lifecycle_chaos_case_count = 20
reporter_lifecycle_chaos_rejected_count = 20
reporter_lifecycle_chaos_failed_count = 0

median3_chaos_case_count = 21
median3_chaos_rejected_count = 21
median3_chaos_failed_count = 0

source_diversity_chaos_case_count = 16
source_diversity_chaos_rejected_count = 16
source_diversity_chaos_failed_count = 0

query_policy_chaos_case_count = 19
query_policy_chaos_rejected_count = 19
query_policy_chaos_failed_count = 0

adapter_chaos_case_count = 27
adapter_chaos_rejected_count = 27
adapter_chaos_failed_count = 0

consumer_profile_catalog_chaos_case_count = 14
consumer_profile_catalog_chaos_rejected_count = 14
consumer_profile_catalog_chaos_failed_count = 0

economic_security_chaos_case_count = 14
economic_security_chaos_rejected_count = 14
economic_security_chaos_failed_count = 0

total_oracle_chaos_case_count = 171
total_oracle_chaos_rejected_count = 171
total_oracle_chaos_failed_count = 0
```

Plain English: the local receipt verifier rejects all currently named
dangerous receipt mutations, and the local token budget verifier rejects all
currently named overspend, hidden-field, and type-confusion mutations. The
local reporter lifecycle verifier rejects all currently named unsafe reporter
sequence mutations. The local median3 aggregate verifier rejects all currently
named miscomputed aggregate, stale/future report, query mismatch, duplicate
source/reporter, source-diversity binding, forged-hash, schema, and hidden-field
mutations. The local source-diversity verifier rejects all currently named
source-set hash, duplicate-source, operator, venue, data-family, transport,
jurisdiction, hidden-field, schema, type-confusion, and malformed-source
mutations. The local query-policy verifier rejects all currently named silent
downgrade, stale policy binding, schema drift, wrong-query, wrong-supersedes,
version-skip, hash-forgery, and hidden-field mutations. The local adapter
verifier rejects all currently named receipt-borrowing, action/bundle mismatch,
weak action policy, consumer-profile mismatch, profile weakening, non-critical
action, hidden-field, schema, missing-field, and type-confusion mutations.
The local consumer profile catalog verifier rejects all currently named missing
profile, duplicate profile, forged hash, unsupported profile, wrong query, weak
evidence, loose freshness, non-critical profile, hidden-field, schema, and
type-confusion mutations.
The local economic security verifier rejects all currently named underpriced
attack, underpaid reporter, reward-budget overspend, weak slash-deterrence,
dispute-budget overspend, fee overspend, hidden-field, schema, and type-confusion
mutations.

## Current Test Command

```bash
pytest -q \
  tests/test_zenodex_oracle.py \
  tests/test_zenodex_oracle_chaos.py \
  tests/test_zenodex_oracle_budget.py \
  tests/test_zenodex_oracle_budget_chaos.py \
  tests/test_zenodex_oracle_reporter_lifecycle.py \
  tests/test_zenodex_oracle_reporter_lifecycle_chaos.py \
  tests/test_zenodex_oracle_median3.py \
  tests/test_zenodex_oracle_median3_chaos.py \
  tests/test_zenodex_oracle_source_diversity.py \
  tests/test_zenodex_oracle_source_diversity_chaos.py \
  tests/test_zenodex_oracle_query_policy.py \
  tests/test_zenodex_oracle_query_policy_chaos.py \
  tests/test_zenodex_oracle_adapter.py \
  tests/test_zenodex_oracle_adapter_chaos.py \
  tests/test_zenodex_oracle_consumer_profiles.py \
  tests/test_zenodex_oracle_consumer_profiles_chaos.py \
  tests/test_zenodex_oracle_economic_security.py \
  tests/test_zenodex_oracle_economic_security_chaos.py
```

Current result on this branch:

```text
171 passed
```

## Public Contract Documents

- [ZENO_ORACLE_MVP_DESIGN.md](ZENO_ORACLE_MVP_DESIGN.md)
- [ZENO_ORACLE_RECEIPT_FORMAT_V1.md](ZENO_ORACLE_RECEIPT_FORMAT_V1.md)
- [ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md](ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md)
- [ZENO_ORACLE_SOURCE_DIVERSITY_V1.md](ZENO_ORACLE_SOURCE_DIVERSITY_V1.md)
- [ZENO_ORACLE_QUERY_POLICY_V1.md](ZENO_ORACLE_QUERY_POLICY_V1.md)
- [ZENO_ORACLE_ADAPTER_V1.md](ZENO_ORACLE_ADAPTER_V1.md)
- [ZENO_ORACLE_CONSUMER_PROFILES_V1.md](ZENO_ORACLE_CONSUMER_PROFILES_V1.md)
- [ZENO_ORACLE_ECONOMIC_SECURITY_V1.md](ZENO_ORACLE_ECONOMIC_SECURITY_V1.md)
- [ZENO_ORACLE_TOKEN_BUDGET_V1.md](ZENO_ORACLE_TOKEN_BUDGET_V1.md)
- [ZENO_ORACLE_REPORTER_LIFECYCLE_V1.md](ZENO_ORACLE_REPORTER_LIFECYCLE_V1.md)
- [ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md)
- [ZENO_ORACLE_PRODUCTION_GATES.md](ZENO_ORACLE_PRODUCTION_GATES.md)

## What Is Stronger Now

The Oracle MVP shell has several important fail-closed properties already:

```text
CriticalOracleUse -> AcceptedReadReceipt
ReceiptAccepted -> ContentHashMatches and ConsumerActionBound
Median3Accepted -> ExactMedian and SourceDiversityAccepted and DeviationWithinPolicy
SourceDiversityAccepted -> DistinctOperatorsVenuesFamiliesTransportsJurisdictions
QueryPolicyAccepted -> NoSilentDowngrade and CriticalConsumersBindLatestPolicy
OracleUseOK(action, bundle, profile) ->
  ActionFactsMatchAcceptedBundle and ActionPolicyNoWeakerThanProfile
ConsumerProfileCatalogAccepted -> CriticalProfilesPresent and NoProfileWeakening
EconomicEnvelopeAccepted -> AttackCostMargin and BudgetSafety and SlashDeterrence
BudgetAccepted -> Spend <= ExplicitEnvelope
ReporterLifecycleAccepted -> ActiveReportersAreBonded and SlashesRequireDisputes
```

Plain English: critical consumers must use accepted receipts, receipt IDs must
commit to their content and bind the downstream action, median3 aggregates must
compute the stated median/confidence/deviation from exactly three reports, and
the report source IDs must match an accepted source-diversity receipt. That
receipt checks declared operator, venue, data-family, transport, and
jurisdiction diversity before the aggregate can pass. Query-policy revisions
must not silently weaken critical freshness, evidence, deviation, quorum, or
schema requirements. Token movements must fit inside explicit budgets, bonds,
or fees. Reporter traces must keep report submission, disputes, slashing, exit,
and withdrawal in the safe order.
The adapter then checks a downstream action against the accepted bundle facts so
critical actions cannot borrow receipts from a different module, action, query,
value, epoch, read receipt, or consumer-action receipt. When a consumer profile
is supplied, the adapter also rejects self-declared action policies that are
weaker than the module/action/query profile. The consumer profile catalog pins
the first critical perps, zUSD, routing, and trigger profiles so those modules
cannot invent weaker profile requirements without a catalog version change.
The economic envelope then checks the declared attack-cost, honest-reward,
slash-deterrence, dispute-budget, and fee-split numbers against integer margin
and budget laws.

## Still Not Claimed

This branch does not claim:

- a live Zeno Oracle network exists;
- reporter registration, submission, rewards, disputes, or slashing are live;
- a production Oracle token exists;
- reporter sources are honest;
- declared source classifications prove real-world independence;
- oracle values are true market prices;
- ZenoDEX perps, zUSD, routing, or trigger execution are already runtime-wired
  to this Oracle verifier;
- the receipt or budget formats are final.

## Next Production Work

1. Wire the adapter predicate into concrete ZenoDEX consumers such as perps,
   zUSD, routing, and trigger execution.
2. Add higher-redundancy aggregate policies after `median_3` and source
   diversity are stable.
3. Add executable reporter CLI flows once the reporter and dispute objects are
   stable.
