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

## Current Replay Counts

```text
receipt_chaos_case_count = 28
receipt_chaos_rejected_count = 28
receipt_chaos_failed_count = 0

budget_chaos_case_count = 12
budget_chaos_rejected_count = 12
budget_chaos_failed_count = 0
```

Plain English: the local receipt verifier rejects all currently named
dangerous receipt mutations, and the local token budget verifier rejects all
currently named overspend, hidden-field, and type-confusion mutations.

## Current Test Command

```bash
pytest -q \
  tests/test_zenodex_oracle.py \
  tests/test_zenodex_oracle_chaos.py \
  tests/test_zenodex_oracle_budget.py \
  tests/test_zenodex_oracle_budget_chaos.py
```

Current result on this branch:

```text
37 passed
```

## Public Contract Documents

- [ZENO_ORACLE_MVP_DESIGN.md](ZENO_ORACLE_MVP_DESIGN.md)
- [ZENO_ORACLE_RECEIPT_FORMAT_V1.md](ZENO_ORACLE_RECEIPT_FORMAT_V1.md)
- [ZENO_ORACLE_TOKEN_BUDGET_V1.md](ZENO_ORACLE_TOKEN_BUDGET_V1.md)
- [ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md)
- [ZENO_ORACLE_PRODUCTION_GATES.md](ZENO_ORACLE_PRODUCTION_GATES.md)

## What Is Stronger Now

The Oracle MVP shell has three important fail-closed properties already:

```text
CriticalOracleUse -> AcceptedReadReceipt
ReceiptAccepted -> ContentHashMatches and ConsumerActionBound
BudgetAccepted -> Spend <= ExplicitEnvelope
```

Plain English: critical consumers must use accepted receipts, receipt IDs must
commit to their content and bind the downstream action, and token movements
must fit inside explicit budgets, bonds, or fees.

## Still Not Claimed

This branch does not claim:

- a live Zeno Oracle network exists;
- reporter registration, submission, rewards, disputes, or slashing are live;
- a production Oracle token exists;
- reporter sources are honest;
- oracle values are true market prices;
- ZenoDEX perps, zUSD, routing, or trigger execution are already wired to this
  Oracle verifier;
- the receipt or budget formats are final.

## Next Production Work

1. Add reporter lifecycle objects: register, bond, report, dispute, slash,
   withdraw.
2. Add aggregate/source receipts for `median_3` and later higher-redundancy
   policies.
3. Add query-policy versioning so consumers cannot silently downgrade freshness,
   evidence, or uncertainty requirements after binding.
4. Add a ZenoDEX adapter predicate:

   ```text
   OracleUseOK(action, receipt_bundle) -> bool
   ```

5. Add executable reporter CLI flows once the reporter and dispute objects are
   stable.
