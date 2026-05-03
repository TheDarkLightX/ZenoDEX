# Zeno Disaster-State Minimization Goal

Status: proposed next assurance goal for ZenoOracle and ZenoDEX as a whole.

## Goal

Maximally minimize reachable disaster states across ZenoOracle and ZenoDEX by
turning every critical safety claim into a named, replayable, fail-closed
obligation.

The target shape is:

```text
CriticalAction or OracleEvent or EconomicTransfer
  -> typed policy
  -> verifier gate
  -> replayable receipt
  -> bounded disaster-state search
  -> promoted guarantee or explicit backlog item
```

No disaster-state class should be counted as prevented unless it has a public
or reproducible evidence path: proof, verifier, fuzz replay, chaos replay, SMT
check, Lean theorem, ESSO receipt, or documented out-of-scope assumption.

## Acceptance Criteria

1. Every critical ZenoDEX consumer action is mapped to a required verifier
   profile and accepted Oracle adapter bridge.
2. Every ZenoOracle devnet action is included in a stateful action-sequence
   harness.
3. Live Oracle service state and replayed Oracle state agree for all accepted
   bounded traces in the harness.
4. Crash-consistency cases are covered: partial event writes, missing artifact
   files, reordered events, duplicate event ids, duplicate event sequences, and
   tampered artifacts.
5. Resource-budget disaster states are mapped and capped: request bodies,
   verifier file sizes, scan loops, JSON-RPC response reads, replay logs,
   reporter counts, feed counts, aggregate candidate counts, and routing search
   bounds.
6. Perps settlement has a direct invariant requiring a usable oracle snapshot
   before settlement can rely on oracle-bounded prices.
7. Oracle economics has a bounded model for reward, slash, dispute, treasury,
   and burn flows, with no accepted transition exceeding explicit budget.
8. The public disaster-state coverage table separates:
   - guaranteed unreachable under current checks;
   - bounded-no-counterexample evidence;
   - backlog/search inventory;
   - external assumptions;
   - out-of-scope production risks.
9. CI runs the promoted disaster-state harnesses.
10. The README links to the coverage table and avoids claiming immunity beyond
    the proved or replayed evidence.

## First Disaster Classes

The first campaign should cover these named classes:

```text
accepted_read_without_accepted_aggregate
adapter_bridge_without_matching_read
receipt_borrowed_across_consumer_action
replay_state_differs_from_live_state
missing_artifact_survives_replay
tampered_artifact_survives_replay
duplicate_event_changes_balance_or_reward
revoked_or_unregistered_reporter_admitted
policy_downgrade_changes_existing_query_semantics
high_uncertainty_price_used_by_critical_action
oracle_settlement_without_usable_snapshot
resource_bound_controlled_by_external_input
reward_exceeds_verified_budget
slash_exceeds_bond
fee_split_exceeds_fee_paid
critical_action_without_consumer_profile
```

## Evidence Standard

The standard for promotion is:

```text
NamedDisasterState
  and deterministic reproduction/search harness
  and fail-closed verifier or proof
  and CI replay
  -> promoted coverage claim
```

If any part is missing, the item remains backlog or bounded evidence, not a
guaranteed-unreachable state.

## Practical Next Step

Start with the ZenoOracle stateful HTTP/replay harness because it is the newest
multi-step surface and already has deterministic devnet APIs. Then lift the
same method into the ZenoDEX critical-action map.

## Current ZenoOracle Devnet Slice

The first promoted devnet slice is implemented by:

```bash
python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text
```

Current expected receipt:

```text
selected_disaster_state_count = 17
unreachable_count = 17
failed_count = 0
inconclusive_count = 0
```

The harness covers accepted-read/adapter preconditions, unregistered reporter
admission, high-uncertainty aggregate rejection, policy downgrade rejection,
receipt borrowing, missing consumer profiles, replay/live-state agreement,
missing and tampered artifacts, duplicate and reordered events, partial event
writes, and budget overspend cases for rewards, slashes, and fee splits.

This is bounded evidence for the local devnet verifier shell. It is not a claim
that the production oracle network exists, that reporters are honest, or that
the broader ZenoDEX/ZenoOracle disaster-state map is exhausted.
