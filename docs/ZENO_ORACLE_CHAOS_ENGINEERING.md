# Zeno Oracle Chaos Engineering

Status: public chaos-test plan and first replay lane.

Chaos engineering is useful for Zeno Oracle when it is treated as a bounded
receipt-mutation discipline, not as random breakage. A valid receipt bundle is
the baseline. Each chaos case changes one semantic axis and expects the verifier
to fail closed.

## Target Shape

```text
ValidBundle + DangerousPerturbation -> RejectedBundle
```

Plain English: if a mutation weakens evidence, freshness, dispute status,
query binding, value binding, dependency closure, or bypass policy, the local
verifier should reject the bundle instead of letting the unsafe state reach a
critical ZenoDEX action.

## First Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_chaos.py
```

The replay starts with one accepted `O3` critical-read bundle, then applies
deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `weak_o2_evidence_used_for_critical_action` | weak evidence feeds a critical action |
| `stale_read_used_for_critical_action` | stale data remains consumable |
| `open_dispute_used_for_critical_action` | disputed aggregate feeds a critical action |
| `high_uncertainty_erased_before_action` | uncertainty failure is stripped before use |
| `consumer_action_borrows_other_query` | action consumes a read for another query |
| `consumer_action_borrows_other_value` | action consumes a value hash from another bundle |
| `consumer_action_drops_read_dependency` | dependency closure is broken |
| `emergency_oracle_bypass_flag_set` | bypass flag survives critical-action verification |
| `terminal_points_to_missing_read` | terminal read pointer is absent from the bundle |
| `action_depends_on_missing_receipt` | dependency graph references missing evidence |
| `duplicate_receipt_id_shadows_terminal` | duplicate IDs create ambiguous evidence |
| `stray_receipt_hides_unreachable_evidence` | unrelated evidence is present but not in terminal closure |
| `unsupported_receipt_type_in_terminal_closure` | unknown receipt type enters the replay closure |
| `dependency_consumed_before_it_appears` | bundle is not in dependency-before-consumer order |
| `read_receipt_depends_on_itself` | receipt graph contains a self-cycle |
| `read_receipt_status_downgraded_after_terminal_binding` | terminal read is no longer accepted |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 16,
  "rejected_case_count": 16,
  "failed_case_count": 0
}
```

## What This Improves

This lane gives ZenoDEX a cheap regression check for the most important oracle
weird-machine pattern:

```text
receipt looks reachable
but one semantic binding is wrong
```

It is stronger than ordinary malformed-input testing because each mutant starts
from a valid bundle and changes one field that a real attacker would want to
weaken while preserving as much surrounding structure as possible.

## What It Does Not Prove

This is not a universal proof of Oracle safety. It is a bounded replay receipt
for named disaster shapes. New consumers, new evidence classes, larger
aggregate families, live network submission, reporter economics, and dispute
governance need their own chaos lanes.

## Next Chaos Lanes

1. Reporter lifecycle: registration, bond, report, dispute, slash, withdrawal.
2. Query-policy update lifecycle: no downgrade after critical consumers bind.
3. Aggregation lifecycle: reporter-set drift, source-family drift, root drift.
4. Token budget lifecycle: fee split, reward payout, budget transition, slash.
5. ZenoDEX adapter lifecycle: accepted read to perps/zUSD/trigger execution.
