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
| Query-policy verifier | `tools/zenodex_oracle_query_policy.py` | `python3 tools/zenodex_oracle_query_policy.py verify <trace>` |
| Query-policy chaos replay | `tools/zenodex_oracle_query_policy_chaos.py` | `python3 tools/zenodex_oracle_query_policy_chaos.py` |
| ZenoDEX adapter verifier | `tools/zenodex_oracle_adapter.py` | `python3 tools/zenodex_oracle_adapter.py verify --action <action> --bundle <bundle>` |
| ZenoDEX adapter chaos replay | `tools/zenodex_oracle_adapter_chaos.py` | `python3 tools/zenodex_oracle_adapter_chaos.py` |

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

median3_chaos_case_count = 18
median3_chaos_rejected_count = 18
median3_chaos_failed_count = 0

query_policy_chaos_case_count = 19
query_policy_chaos_rejected_count = 19
query_policy_chaos_failed_count = 0

adapter_chaos_case_count = 27
adapter_chaos_rejected_count = 27
adapter_chaos_failed_count = 0
```

Plain English: the local receipt verifier rejects all currently named
dangerous receipt mutations, and the local token budget verifier rejects all
currently named overspend, hidden-field, and type-confusion mutations. The
local reporter lifecycle verifier rejects all currently named unsafe reporter
sequence mutations. The local median3 aggregate verifier rejects all currently
named miscomputed aggregate, stale/future report, query mismatch, duplicate
source/reporter, forged-hash, schema, and hidden-field mutations. The local
query-policy verifier rejects all currently named silent downgrade, stale
policy binding, schema drift, wrong-query, wrong-supersedes, version-skip,
hash-forgery, and hidden-field mutations. The local adapter verifier rejects all
currently named receipt-borrowing, action/bundle mismatch, weak action policy,
consumer-profile mismatch, profile weakening, non-critical action,
hidden-field, schema, missing-field, and type-confusion mutations.

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
  tests/test_zenodex_oracle_query_policy.py \
  tests/test_zenodex_oracle_query_policy_chaos.py \
  tests/test_zenodex_oracle_adapter.py \
  tests/test_zenodex_oracle_adapter_chaos.py
```

Current result on this branch:

```text
117 passed
```

## Public Contract Documents

- [ZENO_ORACLE_MVP_DESIGN.md](ZENO_ORACLE_MVP_DESIGN.md)
- [ZENO_ORACLE_RECEIPT_FORMAT_V1.md](ZENO_ORACLE_RECEIPT_FORMAT_V1.md)
- [ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md](ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md)
- [ZENO_ORACLE_QUERY_POLICY_V1.md](ZENO_ORACLE_QUERY_POLICY_V1.md)
- [ZENO_ORACLE_ADAPTER_V1.md](ZENO_ORACLE_ADAPTER_V1.md)
- [ZENO_ORACLE_TOKEN_BUDGET_V1.md](ZENO_ORACLE_TOKEN_BUDGET_V1.md)
- [ZENO_ORACLE_REPORTER_LIFECYCLE_V1.md](ZENO_ORACLE_REPORTER_LIFECYCLE_V1.md)
- [ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md)
- [ZENO_ORACLE_PRODUCTION_GATES.md](ZENO_ORACLE_PRODUCTION_GATES.md)

## What Is Stronger Now

The Oracle MVP shell has several important fail-closed properties already:

```text
CriticalOracleUse -> AcceptedReadReceipt
ReceiptAccepted -> ContentHashMatches and ConsumerActionBound
Median3Accepted -> ExactMedian and DistinctSources and DeviationWithinPolicy
QueryPolicyAccepted -> NoSilentDowngrade and CriticalConsumersBindLatestPolicy
OracleUseOK(action, bundle, profile) ->
  ActionFactsMatchAcceptedBundle and ActionPolicyNoWeakerThanProfile
BudgetAccepted -> Spend <= ExplicitEnvelope
ReporterLifecycleAccepted -> ActiveReportersAreBonded and SlashesRequireDisputes
```

Plain English: critical consumers must use accepted receipts, receipt IDs must
commit to their content and bind the downstream action, median3 aggregates must
compute the stated median/confidence/deviation from exactly three distinct
reports, and query-policy revisions must not silently weaken critical
freshness, evidence, deviation, quorum, or schema requirements. Token movements
must fit inside explicit budgets, bonds, or fees. Reporter traces must keep
report submission, disputes, slashing, exit, and withdrawal in the safe order.
The adapter then checks a downstream action against the accepted bundle facts so
critical actions cannot borrow receipts from a different module, action, query,
value, epoch, read receipt, or consumer-action receipt. When a consumer profile
is supplied, the adapter also rejects self-declared action policies that are
weaker than the module/action/query profile.

## Still Not Claimed

This branch does not claim:

- a live Zeno Oracle network exists;
- reporter registration, submission, rewards, disputes, or slashing are live;
- a production Oracle token exists;
- reporter sources are honest;
- oracle values are true market prices;
- ZenoDEX perps, zUSD, routing, or trigger execution are already runtime-wired
  to this Oracle verifier;
- the receipt or budget formats are final.

## Next Production Work

1. Wire the adapter predicate into concrete ZenoDEX consumers such as perps,
   zUSD, routing, and trigger execution.
2. Add higher-redundancy aggregate policies after `median_3` is stable.
3. Add executable reporter CLI flows once the reporter and dispute objects are
   stable.
