# Disaster State Coverage

This document records the current bounded disaster-state search coverage for
this checkout.

## Current Receipt

As of 2026-04-25, the current positive disaster-search receipt closes `21`
named disaster-state families:

```text
selected_axis_count = 21
unreachable_count = 21
failed_count = 0
inconclusive_count = 0
timeout_s = 240
```

An axis is a scenario family, not one concrete state. Each family is backed by
one or more replay commands that exercise concrete inputs, action sequences,
boundary cases, proof artifacts, certificates, or runtime wrappers.

The broader exploratory plan now names `125` candidate what-if axes. Running
that full plan in this public checkout produced:

```text
selected_axis_count = 125
unreachable_count = 21
failed_count = 96
inconclusive_count = 8
timeout_s = 240
```

That broader result is useful search inventory, but it is not a safety claim.
The closed claim is only the `21` green axes listed below. The remaining `104`
axes stay in backlog until their replay commands are refreshed, their skipped
lanes are split out, or their checks are promoted into Lean, ESSO, Tau, TLA, or
another replayable certificate lane.

## Evidence Discipline

The disaster-state lane follows the repository's public correct-by-construction
posture:

- functional-core changes are accepted only with a clear evidence lane
- skips and timeouts are not counted as unreachable states
- stale or missing harnesses are backlog, not proof
- stateful witness coverage is about attack-shaped semantic states being
  constructed and rejected, not just lines of code being executed

The internal agent/operator notes are not part of this public assurance claim.
This document publishes the replayable result and the limits of that result.

## Replay

Run the closed receipt:

```bash
python3 tools/run_stateful_disaster_search_expansion_plan.py \
  --timeout-s 240 \
  --axis-id epoch_split_brain \
  --axis-id identity_registry_drift \
  --axis-id canonicalization_equivocation \
  --axis-id serialization_width_aliasing \
  --axis-id repair_after_tamper \
  --axis-id external_state_drift \
  --axis-id atomicity_partial_side_effect \
  --axis-id restart_replay_persistence \
  --axis-id dependency_outage_fail_closed \
  --axis-id reciprocal_netting_pair_forgery \
  --axis-id tau_gate_policy_aliasing \
  --axis-id confidential_receipt_attestation_drift \
  --axis-id batch_clearing_fragmentation_ordering \
  --axis-id operations_parser_canonical_envelope \
  --axis-id dex_engine_sequence_anomaly_surface \
  --axis-id dex_core_ref_parity_drift \
  --axis-id boundary_concolic_wrapper_consistency \
  --axis-id exact_out_prefilter_winner_repair_boundary \
  --axis-id quote_receipt_transport_intent_boundary \
  --axis-id tau_runner_subprocess_transport_boundary \
  --axis-id dex_settlement_recovery_proof_unit_boundary \
  --output internal/stateful_disaster_search_expansion_receipt.closed.json \
  --format text
```

Run the full exploratory plan:

```bash
python3 tools/run_stateful_disaster_search_expansion_plan.py \
  --timeout-s 240 \
  --output internal/stateful_disaster_search_expansion_receipt.full.json \
  --format text
```

The `internal/` receipt path is intentionally local and git-ignored. The public
source of the axis definitions is `tools/stateful_scenario_bridge.py`.

## Closed Axes

The current green receipt closes these `21` disaster-state families:

1. `epoch_split_brain`
2. `identity_registry_drift`
3. `canonicalization_equivocation`
4. `serialization_width_aliasing`
5. `repair_after_tamper`
6. `external_state_drift`
7. `atomicity_partial_side_effect`
8. `restart_replay_persistence`
9. `dependency_outage_fail_closed`
10. `reciprocal_netting_pair_forgery`
11. `tau_gate_policy_aliasing`
12. `confidential_receipt_attestation_drift`
13. `batch_clearing_fragmentation_ordering`
14. `operations_parser_canonical_envelope`
15. `dex_engine_sequence_anomaly_surface`
16. `dex_core_ref_parity_drift`
17. `boundary_concolic_wrapper_consistency`
18. `exact_out_prefilter_winner_repair_boundary`
19. `quote_receipt_transport_intent_boundary`
20. `tau_runner_subprocess_transport_boundary`
21. `dex_settlement_recovery_proof_unit_boundary`

## Security Hardening Included

This coverage update is paired with scoped hardening for the live security
findings that are reachable in this checkout:

- perps settlement now requires a usable oracle snapshot before `settle_epoch`
- proof-mining reward-pool drift is synchronized from chain balances instead
  of killing unrelated transactions, while underfunded claims still reject
- malformed proof-mining claim bodies reject without crashing `apply_app_tx`
- `COW_NETTED` settlement fills require exact reciprocal pair evidence
- Tau state-proof binding rejects `state_proof.present` unless the committed
  state hash and app hash agree
- JSON-RPC signer-registry responses are bounded before decoding
- aligned Tau settlement profiles reject full-width intent-order projections
  that would only pass after low-bit truncation
- DEX API resource-budget caps from `origin/main` remain part of the current
  public checkout

## Residual Backlog

The full exploratory plan still contains `104` axes that are not part of the
closed guarantee:

- `8` axes are inconclusive because their replay commands contain skipped lanes
  or external-tool-dependent proof checks.
- `96` axes are not promoted because this public checkout lacks the referenced
  stale artifacts or because their current commands fail.

Those axes are useful prompts for future hardening. They should not be counted
as prevented disaster states until they have clean receipts with no failures,
skips, or timeouts.

## Interpretation

The current assurance improvement is real but bounded. The repo now has a
replayable 21-family disaster-state receipt plus a larger 125-axis search map.
The map makes the next search frontier explicit; the receipt is the part that
can be treated as current evidence.
