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

## Current Critical-Action Map Slice

The first runtime-wiring map is implemented by:

```bash
python3 tools/check_zeno_oracle_critical_action_map.py
```

Current expected receipt:

```text
catalog_profile_count = 7
runtime_wired_count = 7
design_only_backlog_count = 0
status = accepted
```

The current runtime-wired profiles are perps `settle_epoch`, perps
`liquidate_account`, zUSD `mint`, zUSD `liquidate_vault`, routing
`guarded_quote`, critical settlement `critical_settlement`, and trigger
`execute_trigger`. The first-shell profile catalog
has no design-only backlog entries in this checkout.

Details are in
[ZENO_ORACLE_CRITICAL_ACTION_MAP.md](ZENO_ORACLE_CRITICAL_ACTION_MAP.md).

## Current Named Disaster Class Corpus

The first public named-class corpus is implemented by:

```bash
python3 tools/zeno_oracle_disaster_class_corpus.py --format text
```

Current expected receipt:

```text
named_disaster_class_count = 9
closed_class_count = 9
failed_class_count = 0
status = accepted
```

The corpus binds the named source-cartel, dispute-griefing, registry-drift,
settlement-execution total drift, verifier-spoofing, O5 independence-spoofing,
proof-timeout, replay-integrity, and cross-module split-brain families to
public checker outcomes. This is
bounded first-shell evidence. It does not claim exhaustive production oracle
safety, live on-chain governance, reporter honesty, or a live proof network.

## Current Compositional Disaster Regression Projection

The private compositional disaster campaigns are represented publicly by a
sanitized regression manifest and checker:

```bash
python3 tools/check_zeno_oracle_compositional_disaster_regressions.py --format text
```

Current expected receipt:

```text
status = accepted
campaign_count = 2
private_candidate_witness_count = 7
accepted_public_regression_count = 7
deferred_projection_count = 0
```

The public projection records two 100-iteration campaign summaries and promotes
only branch-local replayable regressions: duplicate DEX nonce replay, stale
quote-receipt pool snapshots, signed perps expected-nonce mismatch without
nonce consumption, and strategy policy bundle rejection below the O3 live
floor, confidential live-admission request replay, route candidate-set hash
drift, and missing quote-receipt hashes. All seven selected private witness
projections now have public branch-local replay.

Private campaign artifacts are provenance. The public assurance value is the
tracked manifest, checker, and replayable tests.

## Current Production-Disaster Frontier

The production-candidate frontier catalog is implemented by:

```bash
python3 tools/check_zeno_oracle_disaster_frontier.py --format text
```

Current expected receipt:

```text
status = accepted
frontier_family_count = 29
closed_family_count = 24
blocked_or_backlog_count = 5
new_obligation_family_count = 0
```

The frontier gate cross-checks the devnet disaster harness, named
disaster-class corpus, and obligation-antichain manifest. It rejects silent
coverage drift: a family must have public replay evidence, or it must remain an
explicit blocker/backlog item.

The frontier-to-antichain projection gate is:

```bash
python3 tools/check_zeno_oracle_frontier_obligation_projection.py --format text
```

Current expected receipt:

```text
status = accepted
frontier_family_count = 29
projected_family_count = 29
new_obligation_family_count = 0
error_count = 0
```

This gate rejects frontier drift before a family can silently escape the
obligation quotient.

Cross-domain finality is now represented as a manifest obligation atom and has
a local receipt-bundle gate:

```bash
python3 tools/check_zeno_oracle_cross_domain_finality_gate.py --format text
```

That gate validates that a source finality checkpoint receipt and target
adapter-acceptance receipt bind to the same accepted read, query/value hash,
policy, adapter contract, finality root, confirmation floor, and reorg-depth
limit. `--require-live` intentionally rejects until those receipts are replayed
against live chain state and public soak evidence exists.

The current open frontier families are usable perps oracle snapshots,
cross-domain finality, live escrow payout safety, live governance timelock
execution, and public reporter soak/operator independence. `--require-closed`
intentionally rejects while those families remain open.

The live escrow payout family now has local economics receipt replay through:

```bash
python3 tools/check_zeno_oracle_live_economics_policy.py --format text
```

That gate checks governance approval/execution, escrow funding against the
replay-derived floor, and settlement execution totals against the reporter
economics replay. `--require-live` intentionally rejects until the receipts are
verified against live chain state.

The usable perps oracle snapshot family now has bounded replay evidence through
`tools/check_zeno_oracle_perps_snapshot_gate.py`. That gate checks snapshot
roundtrip preservation for isolated perps settlement runtime facts, adapter
execution after restore, liquidation action-ID binding after restore,
clearinghouse 2p/3p settlement action-ID binding after restore, clearinghouse
2p/3p adapter execution after restore, and fail-closed rejection of malformed
oracle and clearinghouse snapshot state. It does not claim a general perps
snapshot theorem or live runtime policy.

The governance-timelock family now has local feed-governance
approval/execution receipt replay through
`tools/check_zeno_oracle_production_network_config.py`. The receipt gate checks
proposal ID binding, feed query binding, timelock floor, and execution time.
It still rejects `--require-live` until the same receipts are verified on-chain.

The public reporter-soak family now has local observation replay through:

```bash
python3 tools/check_zeno_oracle_reporter_soak_gate.py --format text
```

That gate validates reporter count, distinct operator count, operator-share
limits, per-reporter soak epochs, success/dispute-rate thresholds, and
source-diversity acceptance. `--require-live` intentionally rejects until the
observations are verified against public telemetry and operator independence is
externally attested.
