# Zeno Oracle Chaos Engineering

Status: public chaos-test plan and first replay lane.

Chaos engineering is useful for Zeno Oracle when it is treated as a bounded
receipt- and budget-mutation discipline, not as random breakage. A valid
receipt bundle or budget transition is the baseline. Each chaos case changes
one semantic axis and expects the verifier to fail closed.

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
| `consumer_action_replays_expired_read` | action executes after the read expires |
| `consumer_action_precedes_read_observation` | action claims a read before it was observed |
| `consumer_action_erases_consumer_identity` | action removes the downstream consumer binding |
| `terminal_points_to_missing_read` | terminal read pointer is absent from the bundle |
| `action_depends_on_missing_receipt` | dependency graph references missing evidence |
| `duplicate_receipt_id_shadows_terminal` | duplicate IDs create ambiguous evidence |
| `stray_receipt_hides_unreachable_evidence` | unrelated evidence is present but not in terminal closure |
| `unsupported_receipt_type_in_terminal_closure` | unknown receipt type enters the replay closure |
| `dependency_consumed_before_it_appears` | bundle is not in dependency-before-consumer order |
| `read_receipt_depends_on_itself` | receipt graph contains a self-cycle |
| `read_receipt_depends_on_action_receipt` | read depends on the action it should precede |
| `action_depends_on_extra_reachable_read` | action imports extra reachable read evidence |
| `action_duplicates_read_dependency` | action duplicates dependency edges |
| `terminal_aliases_read_as_action` | terminal read ID is reused as action ID |
| `receipt_id_forged_without_body_match` | receipt ID does not match its canonical body hash |
| `read_receipt_status_downgraded_after_terminal_binding` | terminal read is no longer accepted |
| `unknown_top_level_field_survives` | bundle carries undeclared top-level authority |
| `unknown_terminal_field_survives` | terminal binding carries undeclared action data |
| `unknown_read_receipt_field_survives` | read receipt carries unchecked source/debug data |
| `unknown_action_receipt_field_survives` | action receipt carries unchecked bypass-like data |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 28,
  "rejected_case_count": 28,
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

## Token Budget Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_budget_chaos.py
```

The replay starts with one accepted budget transition, then applies
deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `query_reward_exceeds_remaining_budget` | reporter reward exceeds query budget |
| `query_reward_from_zero_budget` | reward is paid from an empty query budget |
| `reporter_slash_exceeds_available_bond` | reporter slash payout exceeds bond |
| `dispute_slash_exceeds_available_bond` | dispute slash payout exceeds dispute bond |
| `fee_split_spends_more_than_fee` | fee split spends more than paid fees |
| `fee_split_spends_from_zero_fee` | fee share is paid from an empty fee envelope |
| `hidden_mint_field_survives` | hidden mint-like field is accepted |
| `negative_reward_amount_survives` | negative reward amount enters accounting |
| `boolean_burn_share_survives` | boolean value is accepted as an amount |
| `missing_fee_share_survives` | required fee share is omitted |
| `wrong_schema_survives` | budget schema downgrade is accepted |
| `string_budget_amount_survives` | string amount is accepted as a budget |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.budget_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 12,
  "rejected_case_count": 12,
  "failed_case_count": 0
}
```

This lane checks the token surface behind the Oracle MVP:

```text
ValidBudgetTransition + DangerousPerturbation -> RejectedTransition
```

Plain English: if a mutation creates a reward, slash, burn, treasury, or fee
share that exceeds the explicit budget/bond/fee envelope, the local verifier
rejects it.

## Reporter Lifecycle Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_reporter_lifecycle_chaos.py
```

The replay starts with one accepted reporter lifecycle trace, then applies
deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `duplicate_reporter_registration` | reporter registers twice |
| `bond_deposit_before_registration` | bond appears before reporter registration |
| `report_before_registration` | report is submitted by inactive reporter |
| `report_under_required_bond` | report is submitted below required bond |
| `duplicate_report_id_survives` | same report ID is submitted twice |
| `dispute_for_unknown_report` | dispute targets unknown report |
| `zero_dispute_bond_survives` | dispute opens with no challenger bond |
| `slash_without_open_dispute` | slash executes without open dispute |
| `slash_exceeds_reporter_bond` | slash exceeds available reporter bond |
| `double_slash_same_dispute` | same dispute slashes twice |
| `resolve_unknown_dispute` | resolver closes unknown dispute |
| `unregister_with_open_dispute` | reporter exits with open dispute |
| `withdraw_while_active` | reporter withdraws while active |
| `withdraw_with_open_dispute` | reporter withdraws while dispute is open |
| `withdraw_exceeds_bond` | withdrawal exceeds remaining bond |
| `event_epoch_regression` | lifecycle epochs move backward |
| `hidden_event_field_survives` | hidden event authority field is accepted |
| `unknown_event_type_survives` | unsupported event type is accepted |
| `boolean_bond_amount_survives` | boolean is accepted as amount |
| `too_many_events_survive` | trace exceeds event-count budget |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.reporter_lifecycle_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 20,
  "rejected_case_count": 20,
  "failed_case_count": 0
}
```

This lane checks the permissionless reporter sequence:

```text
ValidReporterLifecycle + DangerousPerturbation -> RejectedLifecycle
```

Plain English: if a mutation lets a reporter skip registration, report
under-bonded, slash outside an open dispute, or withdraw unsafely, the local
verifier rejects it.

## Median3 Aggregate Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_median3_chaos.py
```

The replay starts with one accepted `median_3` aggregate, then applies
deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `aggregate_value_not_median` | aggregate value is not the median of included reports |
| `aggregate_confidence_mismatch` | confidence radius is understated or miscomputed |
| `aggregate_deviation_mismatch` | deviation bps is understated or miscomputed |
| `aggregate_observed_epoch_mismatch` | aggregate observation epoch does not match report epochs |
| `report_query_id_mismatch` | report for a different query enters the aggregate |
| `stale_report_survives` | stale report remains aggregatable |
| `future_report_survives` | future-dated report remains aggregatable |
| `duplicate_reporter_survives` | one reporter counts as multiple reporters |
| `duplicate_source_survives` | one source counts as multiple independent sources |
| `too_few_reports_survive` | aggregate is accepted below the median_3 quorum |
| `too_many_reports_survive` | extra reports enter an exactly-three policy |
| `forged_report_id_survives` | report ID does not match report body |
| `forged_aggregate_id_survives` | aggregate ID does not match aggregate body |
| `deviation_policy_exceeded` | high-deviation aggregate passes policy |
| `nonpositive_report_value_survives` | zero price enters aggregation |
| `hidden_report_field_survives` | report carries unchecked authority/debug data |
| `hidden_aggregate_field_survives` | aggregate carries unchecked authority/debug data |
| `wrong_schema_survives` | aggregate schema downgrade is accepted |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.median3_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 18,
  "rejected_case_count": 18,
  "failed_case_count": 0
}
```

This lane checks the first aggregate policy:

```text
ValidMedian3Aggregate + DangerousPerturbation -> RejectedAggregate
```

Plain English: if a mutation changes the median, confidence, deviation, source
set, query binding, freshness, or content hash, the local verifier rejects the
aggregate before it can become an accepted read.

## Query-Policy Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_query_policy_chaos.py
```

The replay starts with one accepted query-policy trace, then applies
deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `staleness_downgrade_survives` | later policy allows older reports |
| `deviation_downgrade_survives` | later policy allows wider price dispersion |
| `evidence_floor_downgrade_survives` | later policy lowers required evidence class |
| `source_quorum_downgrade_survives` | later policy lowers source quorum |
| `reporter_quorum_downgrade_survives` | later policy lowers reporter quorum |
| `aggregation_schema_drift_survives` | later policy swaps aggregate schema |
| `read_schema_drift_survives` | later policy swaps read-receipt schema |
| `policy_content_hash_forgery_survives` | policy ID no longer matches policy body |
| `policy_query_mismatch_survives` | policy for another query enters the trace |
| `wrong_supersedes_survives` | policy update does not supersede active policy |
| `version_skip_survives` | policy version jumps or skips |
| `unknown_policy_binding_survives` | consumer binds an unknown policy ID |
| `nonlatest_policy_binding_survives` | consumer binds an older policy after a newer one exists |
| `noncritical_binding_survives` | critical policy shell accepts non-critical binding |
| `action_before_binding_survives` | action claims policy before binding event |
| `hidden_policy_field_survives` | policy carries unchecked authority/debug data |
| `hidden_event_field_survives` | event carries unchecked authority/debug data |
| `event_epoch_regression_survives` | policy lifecycle epochs move backward |
| `wrong_schema_survives` | query-policy schema downgrade is accepted |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.query_policy_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 19,
  "rejected_case_count": 19,
  "failed_case_count": 0
}
```

This lane checks query-policy versioning:

```text
ValidQueryPolicyTrace + DangerousPerturbation -> RejectedTrace
```

Plain English: if a mutation weakens the policy envelope or binds a consumer to
the wrong policy, the local verifier rejects the trace before a critical action
can treat the weaker policy as authority.

## Adapter Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_adapter_chaos.py
```

The replay starts with one accepted action/bundle pair, then applies
deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `unaccepted_bundle_survives` | downstream action accepts a rejected Oracle bundle |
| `consumer_module_mismatch_survives` | receipt is borrowed across consumer modules |
| `action_kind_mismatch_survives` | receipt is borrowed across action kinds |
| `action_id_mismatch_survives` | receipt is borrowed across action IDs |
| `action_epoch_mismatch_survives` | receipt is borrowed across action epochs |
| `query_mismatch_survives` | action asks one query but consumes another |
| `value_mismatch_survives` | action consumes another value hash |
| `read_receipt_id_mismatch_survives` | action names a different read receipt |
| `consumer_action_receipt_id_mismatch_survives` | action names a different consumer-action receipt |
| `evidence_below_action_floor_survives` | bundle evidence is below action requirement |
| `freshness_window_exceeds_action_limit_survives` | bundle freshness window is looser than action limit |
| `noncritical_action_descriptor_survives` | non-critical action descriptor is treated as critical |
| `weak_required_evidence_floor_survives` | action declares a weak evidence floor |
| `hidden_action_field_survives` | action carries unchecked authority/debug data |
| `wrong_action_schema_survives` | action schema downgrade is accepted |
| `missing_action_id_survives` | action omits the downstream action ID |
| `boolean_action_epoch_survives` | boolean is accepted as action epoch |
| `profile_content_hash_forgery_survives` | profile ID no longer matches profile body |
| `profile_consumer_module_mismatch_survives` | profile for another consumer module is accepted |
| `profile_action_kind_mismatch_survives` | profile for another action kind is accepted |
| `profile_query_mismatch_survives` | profile for another query is accepted |
| `action_evidence_floor_below_profile_survives` | action evidence floor is weaker than profile |
| `action_freshness_window_exceeds_profile_survives` | action freshness window is looser than profile |
| `noncritical_profile_survives` | non-critical profile is accepted for critical adapter use |
| `hidden_profile_field_survives` | profile carries unchecked authority/debug data |
| `weak_profile_evidence_floor_survives` | profile declares weak evidence for critical use |
| `wrong_profile_schema_survives` | profile schema downgrade is accepted |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.adapter_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 27,
  "rejected_case_count": 27,
  "failed_case_count": 0
}
```

This lane checks the first adapter boundary:

```text
ValidActionBundlePair + DangerousPerturbation -> RejectedOracleUse
```

Plain English: if a mutation lets a critical action borrow a receipt from the
wrong bundle, action, query, value, epoch, evidence floor, or freshness policy,
or lets a consumer profile silently weaken the action policy, the local adapter
rejects the attempted Oracle use.

## Consumer Profile Catalog Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_consumer_profiles_chaos.py
```

The replay starts with one accepted critical consumer profile catalog, then
applies deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `missing_required_profile_survives` | a critical consumer profile is omitted |
| `duplicate_profile_key_survives` | one module/action profile appears twice |
| `duplicate_profile_id_survives` | two profiles share one content ID |
| `profile_hash_forgery_survives` | profile ID no longer matches profile body |
| `unsupported_profile_key_survives` | unsupported consumer/action enters the catalog |
| `wrong_query_survives` | profile points at the wrong query |
| `weak_evidence_floor_survives` | profile lowers evidence below the required floor |
| `loose_freshness_survives` | profile loosens freshness beyond the required cap |
| `noncritical_profile_survives` | non-critical profile enters critical catalog |
| `hidden_profile_field_survives` | profile carries unchecked authority/debug data |
| `wrong_catalog_schema_survives` | catalog schema downgrade is accepted |
| `wrong_profile_schema_survives` | profile schema downgrade is accepted |
| `boolean_freshness_survives` | boolean is accepted as freshness window |
| `hidden_catalog_field_survives` | catalog carries unchecked authority/debug data |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.consumer_profile_catalog_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 14,
  "rejected_case_count": 14,
  "failed_case_count": 0
}
```

This lane checks the first concrete ZenoDEX consumer profile catalog:

```text
ValidConsumerProfileCatalog + DangerousPerturbation -> RejectedCatalog
```

Plain English: if a mutation removes, duplicates, weakens, misbinds, or hides
authority in a critical consumer profile, the local verifier rejects the catalog.

## Economic Security Replay Lane

Run:

```bash
python3 tools/zenodex_oracle_economic_security_chaos.py
```

The replay starts with one accepted economic security envelope, then applies
deterministic single-axis mutations:

| Chaos Case | Disaster Shape |
| --- | --- |
| `extractable_above_notional_survives` | extractable value exceeds protected notional |
| `attack_cost_below_margin_survives` | attack cost is below extractable value plus margin |
| `reward_below_honest_cost_survives` | reporter reward does not cover honest cost and risk |
| `reporter_reward_budget_overspend_survives` | total reporter reward exceeds budget |
| `cheat_gain_above_extractable_survives` | declared cheating gain exceeds extractable value |
| `weak_slash_deterrence_survives` | slashable bond is below cheating gain plus margin |
| `dispute_reward_budget_overspend_survives` | dispute reward exceeds dispute budget |
| `fee_split_overspend_survives` | fee shares spend more than paid fees |
| `hidden_mint_field_survives` | hidden mint-like field is accepted |
| `boolean_attack_cost_survives` | boolean is accepted as amount |
| `wrong_schema_survives` | economic envelope schema downgrade is accepted |
| `zero_reporter_count_survives` | zero reporters are accepted |
| `slash_fraction_over_100_percent_survives` | slash fraction above 100% is accepted |
| `negative_fee_share_survives` | negative fee share enters accounting |

The receipt reports:

```json
{
  "schema": "zenodex.oracle.economic_security_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 14,
  "rejected_case_count": 14,
  "failed_case_count": 0
}
```

This lane checks the first economic envelope:

```text
ValidEconomicEnvelope + DangerousPerturbation -> RejectedEnvelope
```

Plain English: if a mutation underprices manipulation, underpays honest
reporters, weakens slash deterrence, or overspends a budget, the local verifier
rejects the envelope.

## Next Chaos Lanes

1. Higher-redundancy aggregation lifecycle: reporter-set drift, source-family
   drift, root drift.
2. Runtime adapter hooks: concrete perps/zUSD/routing/trigger calls must reject
   raw oracle values and wrong-profile receipt reuse.
