# Zeno Oracle MVP Status

Status: public branch summary for the local Oracle MVP shell.

This page summarizes what exists now on the public Zeno Oracle MVP branch. It
is a status page, not a production launch claim.

## Implemented Local Surfaces

| Surface | Artifact | Replay |
| --- | --- | --- |
| Unified local CLI wrapper | `tools/zenodex_oracle_cli.py` | `python3 tools/zenodex_oracle_cli.py doctor` |
| Packaged executable launcher | `bin/zenodex-oracle` | `bin/zenodex-oracle doctor` |
| Local MVP dry-run flow | `tools/zenodex_oracle_cli.py dry-run` | `bin/zenodex-oracle dry-run --workdir /tmp/zeno-oracle-dry-run` |
| Local devnet alpha service | `tools/zenodex_oracle_devnet_service.py` | `bin/zenodex-oracle serve --store /tmp/zeno-oracle-devnet` |
| Local devnet replay | `tools/zenodex_oracle_devnet_service.py replay` | `bin/zenodex-oracle replay --store /tmp/zeno-oracle-devnet` |
| MVP completion audit | `tools/zenodex_oracle_mvp_completion_audit.py` | `python3 tools/zenodex_oracle_mvp_completion_audit.py` |
| Release-candidate package builder | `scripts/package_zeno_oracle_rc.sh` | `bash scripts/package_zeno_oracle_rc.sh` |
| Critical read receipt verifier | `tools/zenodex_oracle.py` | `python3 tools/zenodex_oracle.py verify <bundle>` |
| Receipt chaos replay | `tools/zenodex_oracle_chaos.py` | `python3 tools/zenodex_oracle_chaos.py` |
| Token budget verifier | `tools/zenodex_oracle_budget.py` | `python3 tools/zenodex_oracle_budget.py verify <transition>` |
| Token budget chaos replay | `tools/zenodex_oracle_budget_chaos.py` | `python3 tools/zenodex_oracle_budget_chaos.py` |
| Reporter lifecycle verifier | `tools/zenodex_oracle_reporter_lifecycle.py` | `python3 tools/zenodex_oracle_reporter_lifecycle.py verify <trace>` |
| Reporter lifecycle chaos replay | `tools/zenodex_oracle_reporter_lifecycle_chaos.py` | `python3 tools/zenodex_oracle_reporter_lifecycle_chaos.py` |
| Signed report verifier | `tools/zenodex_oracle_signed_report.py` | `python3 tools/zenodex_oracle_signed_report.py verify <submission>` |
| Signed report chaos replay | `tools/zenodex_oracle_signed_report_chaos.py` | `python3 tools/zenodex_oracle_signed_report_chaos.py` |
| Report admission verifier | `tools/zenodex_oracle_report_admission.py` | `python3 tools/zenodex_oracle_report_admission.py verify <admission>` |
| Report admission chaos replay | `tools/zenodex_oracle_report_admission_chaos.py` | `python3 tools/zenodex_oracle_report_admission_chaos.py` |
| Median3 aggregate verifier | `tools/zenodex_oracle_median3.py` | `python3 tools/zenodex_oracle_median3.py verify <aggregate>` |
| Median3 aggregate chaos replay | `tools/zenodex_oracle_median3_chaos.py` | `python3 tools/zenodex_oracle_median3_chaos.py` |
| Admitted median3 verifier | `tools/zenodex_oracle_admitted_median3.py` | `python3 tools/zenodex_oracle_admitted_median3.py verify <aggregate>` |
| Admitted median3 chaos replay | `tools/zenodex_oracle_admitted_median3_chaos.py` | `python3 tools/zenodex_oracle_admitted_median3_chaos.py` |
| Aggregate-read bridge verifier | `tools/zenodex_oracle_aggregate_read.py` | `python3 tools/zenodex_oracle_aggregate_read.py verify <bridge>` |
| Aggregate-read bridge chaos replay | `tools/zenodex_oracle_aggregate_read_chaos.py` | `python3 tools/zenodex_oracle_aggregate_read_chaos.py` |
| Aggregate-adapter bridge verifier | `tools/zenodex_oracle_aggregate_adapter.py` | `python3 tools/zenodex_oracle_aggregate_adapter.py verify <bridge>` |
| Aggregate-adapter bridge chaos replay | `tools/zenodex_oracle_aggregate_adapter_chaos.py` | `python3 tools/zenodex_oracle_aggregate_adapter_chaos.py` |
| Feed registry verifier | `tools/zenodex_oracle_feed_registry.py` | `python3 tools/zenodex_oracle_feed_registry.py verify <registry>` |
| Feed registry chaos replay | `tools/zenodex_oracle_feed_registry_chaos.py` | `python3 tools/zenodex_oracle_feed_registry_chaos.py` |
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

signed_report_chaos_case_count = 18
signed_report_chaos_rejected_count = 18
signed_report_chaos_failed_count = 0

report_admission_chaos_case_count = 18
report_admission_chaos_rejected_count = 18
report_admission_chaos_failed_count = 0

median3_chaos_case_count = 21
median3_chaos_rejected_count = 21
median3_chaos_failed_count = 0

admitted_median3_chaos_case_count = 18
admitted_median3_chaos_rejected_count = 18
admitted_median3_chaos_failed_count = 0

aggregate_read_chaos_case_count = 16
aggregate_read_chaos_rejected_count = 16
aggregate_read_chaos_failed_count = 0

aggregate_adapter_chaos_case_count = 16
aggregate_adapter_chaos_rejected_count = 16
aggregate_adapter_chaos_failed_count = 0

feed_registry_chaos_case_count = 26
feed_registry_chaos_rejected_count = 26
feed_registry_chaos_failed_count = 0

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

total_oracle_chaos_case_count = 283
total_oracle_chaos_rejected_count = 283
total_oracle_chaos_failed_count = 0
```

Plain English: the local receipt verifier rejects all currently named
dangerous receipt mutations, and the local token budget verifier rejects all
currently named overspend, hidden-field, and type-confusion mutations. The
local reporter lifecycle verifier rejects all currently named unsafe reporter
sequence mutations. The local signed-report verifier rejects all currently
named payload, signature, report-ID, sequence, previous-link, duplicate,
hidden-field, schema, key-format, type-confusion, and malformed-report
mutations. The local report-admission verifier rejects all currently named
signed/lifecycle/source bridge mismatches, missing or extra lifecycle submit
events, source-policy mismatches, stale/future admission, hidden-field, schema,
type-confusion, and malformed-subreceipt mutations. The local median3 aggregate
verifier rejects all currently named miscomputed aggregate, stale/future report,
query mismatch, duplicate source/reporter, source-diversity binding,
forged-hash, schema, and hidden-field mutations. The local admitted-median3
verifier rejects all currently named aggregate-from-admission hash, median,
confidence, deviation, observed-epoch, admission-count, admission-rejection,
duplicate-admission, duplicate-reporter, duplicate-source, query mismatch,
freshness-window mismatch, multi-report admission, deviation-policy,
hidden-field, and schema mutations. The local aggregate-read bridge verifier
rejects all currently named admitted-aggregate rejection, receipt-bundle
rejection, query mismatch, value-hash mismatch, observed-epoch mismatch, expiry
mismatch, freshness-window mismatch, missing-subobject, evidence-weakening,
hidden-field, schema, and type-confusion mutations. The local aggregate-adapter
bridge verifier rejects all currently named aggregate-read rejection, action
query/value/action/read/consumer-receipt mismatch, profile hash/mismatch,
freshness weakening, non-critical action, missing-subobject, hidden-field, and
schema mutations. The local feed-registry verifier rejects all currently named
registry/feed/query/policy/source hash forgery, duplicate feed/query,
base-quote aliasing, weak quorum/freshness/evidence/deviation, unsupported
schema, source-query mismatch, source-correlation, future/inactive feed,
hidden-field, schema, and type-confusion mutations. The local source-diversity
verifier rejects all currently named source-set hash, duplicate-source,
operator, venue, data-family, transport, jurisdiction, hidden-field, schema,
type-confusion, and malformed-source mutations. The local query-policy verifier
rejects all currently named silent downgrade, stale policy binding, schema
drift, wrong-query, wrong-supersedes, version-skip, hash-forgery, and
hidden-field mutations. The local adapter
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
bash scripts/check_zeno_oracle_mvp.sh
```

Current result on this branch:

```text
doctor_ok = true
chaos_all_case_count = 283
chaos_all_rejected_count = 283
chaos_all_failed_count = 0
271 passed
```

The CI workflow `.github/workflows/zeno-oracle-mvp.yml` runs the same command
on pull requests and pushes to `main` or `docs/zeno-oracle-mvp-design`, then
builds and uploads the `zeno-oracle-mvp-rc1` package artifact.

## Public Contract Documents

- [ZENO_ORACLE_MVP_DESIGN.md](ZENO_ORACLE_MVP_DESIGN.md)
- [ZENO_ORACLE_CLI_V1.md](ZENO_ORACLE_CLI_V1.md)
- [ZENO_ORACLE_RECEIPT_FORMAT_V1.md](ZENO_ORACLE_RECEIPT_FORMAT_V1.md)
- [ZENO_ORACLE_SIGNED_REPORT_V1.md](ZENO_ORACLE_SIGNED_REPORT_V1.md)
- [ZENO_ORACLE_REPORT_ADMISSION_V1.md](ZENO_ORACLE_REPORT_ADMISSION_V1.md)
- [ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md](ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md)
- [ZENO_ORACLE_ADMITTED_MEDIAN3_V1.md](ZENO_ORACLE_ADMITTED_MEDIAN3_V1.md)
- [ZENO_ORACLE_AGGREGATE_READ_V1.md](ZENO_ORACLE_AGGREGATE_READ_V1.md)
- [ZENO_ORACLE_AGGREGATE_ADAPTER_V1.md](ZENO_ORACLE_AGGREGATE_ADAPTER_V1.md)
- [ZENO_ORACLE_RUNTIME_BRIDGE_V1.md](ZENO_ORACLE_RUNTIME_BRIDGE_V1.md)
- [ZENO_ORACLE_FEED_REGISTRY_V1.md](ZENO_ORACLE_FEED_REGISTRY_V1.md)
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
OracleCLIReady -> LocalSamplesAndVerifiersDiscoverable
CriticalOracleUse -> AcceptedReadReceipt
ReceiptAccepted -> ContentHashMatches and ConsumerActionBound
SignedReportAccepted -> PayloadHashMatches and SignatureValid and SequenceChainValid
ReportAdmissionAccepted -> SignedReportAccepted and LifecycleSubmitMatches and SourcePolicyMatches
Median3Accepted -> ExactMedian and SourceDiversityAccepted and DeviationWithinPolicy
AdmittedMedian3Accepted -> ReportAdmissionAccepted and ExactMedian and DeviationWithinPolicy
AggregateReadAccepted -> AdmittedMedian3Accepted and ReceiptBundleAccepted and ValueHashMatchesAggregate
AggregateAdapterAccepted -> AggregateReadAccepted and AdapterAccepted(action, bundle, profile)
FeedRegistryAccepted -> QuerySpecHashMatches and SourceDiversityAccepted and AggregatePolicyHashMatches
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
commit to their content and bind the downstream action. The local CLI wrapper
now exposes one entry point for discovering verifier surfaces, emitting sample
feed/report artifacts, verifying those artifacts, registering accepted feed
registries into a local store, submitting accepted signed reports into a local
store, and replaying chaos lanes.
Median3 aggregates must
commit to their content and bind the downstream action, signed reporter
submissions must verify the BLS signature over the exact payload and preserve a
contiguous previous-report chain. The report-admission bridge then requires the
signed report, lifecycle submit event, and source-diversity policy to describe
the same reporter, report, query, source, payload hash, and freshness window.
Plain median3 aggregates must compute the stated median/confidence/deviation
from exactly three reports, and the report source IDs must match an accepted
source-diversity receipt. The admitted-median3 bridge tightens this by requiring
each aggregate input to be an accepted report-admission bundle before median
computation. The aggregate-read bridge then requires the accepted read/action
bundle's query, value hash, observed epoch, expiry, and freshness window to be
derived from the admitted aggregate. The aggregate-adapter bridge then checks
the concrete action/profile binding against that exact aggregate-derived
bundle. That receipt checks declared operator, venue, data-family, transport,
and jurisdiction diversity before the aggregate can pass.
The feed registry now checks feed creation/registration objects before they can
be treated as admissible query definitions, and it pins query semantics, source
diversity, admitted-median3 aggregation, signed-report inputs, freshness,
deviation, evidence, and uniqueness in content-addressed objects.
Query-policy revisions must not silently weaken critical freshness, evidence,
deviation, quorum, or schema requirements. Token movements must fit inside
explicit budgets, bonds, or fees. Reporter traces must keep report submission,
disputes, slashing, exit, and withdrawal in the safe order.
The adapter then checks a downstream action against the accepted bundle facts so
critical actions cannot borrow receipts from a different module, action, query,
value, epoch, read receipt, or consumer-action receipt. When a consumer profile
is supplied, the adapter also rejects self-declared action policies that are
weaker than the module/action/query profile. The consumer profile catalog pins
the first critical perps, zUSD, routing, and trigger profiles so those modules
cannot invent weaker profile requirements without a catalog version change.
The first runtime hooks are wired into perps settlement and guarded routing
quote APIs. Isolated, 2-party clearinghouse, and 3-party
transfer clearinghouse
`settle_epoch` can require `oracle_adapter_bridge`, verify it before settlement
state changes, and reject bridges that are missing, unchecked, rejected, bound
to any action other than `zenodex.perps / settle_epoch`, bound to a different
Oracle query, bound to a weaker or unrelated consumer profile, or bound to a
different market/epoch/price snapshot runtime action ID. The exact-in and
exact-out guarded routing quote APIs can
require the same bridge for `zenodex.routing / guarded_quote`, bound to the
route request, route policy, official routing profile, routing reference-price
query, and pool snapshot hash.
The economic envelope then checks the declared attack-cost, honest-reward,
slash-deterrence, dispute-budget, and fee-split numbers against integer margin
and budget laws.

## Devnet Alpha Layer

The devnet alpha adds local HTTP transport and a replayable store around the
accepted MVP verifier objects. It supports reporter key registration, feed
registry registration, signed report submission, admitted median3 aggregate
production, accepted read APIs, ZenoDEX aggregate-adapter bridge APIs, economic
event receipts, and replay from `events.jsonl`.

```text
HTTP artifact accepted -> existing verifier accepted -> artifact persisted -> event receipt appended
```

That keeps the network-facing path aligned with the local verifier shell. A
read returned by `/reads/latest` or `/adapter/latest` is an accepted verifier
artifact, not an unchecked service-side assertion.

Details are in [ZENO_ORACLE_DEVNET_ALPHA.md](ZENO_ORACLE_DEVNET_ALPHA.md).

## Still Not Claimed

This branch does not claim:

- a production Zeno Oracle network exists;
- a platform-native binary installer exists;
- feed governance or on-chain feed registration is live;
- reporter registration, submission, rewards, disputes, or slashing are live
  beyond the local devnet receipt service;
- a production Oracle token exists;
- reporter sources are honest;
- declared source classifications prove real-world independence;
- oracle values are true market prices;
- every ZenoDEX routing endpoint, production zUSD, liquidation, or trigger action is already
  runtime-wired to this Oracle verifier;
- the receipt or budget formats are final.

## Next Production Work

1. Replace the devnet integrity signature with production code signing.
2. Implement the blocked production zUSD mint/liquidation Oracle lifecycle in
   the monetary bridge, and extend coverage to additional routing endpoints.
3. Add higher-redundancy aggregate policies after `median_3` and source
   diversity are stable.
4. Add production reporter CLI flows, public testnet deployment config, and
   external monitoring once the reporter and dispute objects are stable.
