# Disaster State Coverage

This document records the current bounded disaster-state search coverage for
this checkout.

## Current Receipt

As of 2026-04-25, the current positive disaster-search receipt closes `29`
named disaster-state families:

```text
selected_axis_count = 29
unreachable_count = 29
failed_count = 0
inconclusive_count = 0
timeout_s = 240
```

An axis is a scenario family, not one concrete state. Each family is backed by
one or more replay commands that exercise concrete inputs, action sequences,
boundary cases, proof artifacts, certificates, or runtime wrappers.

The broader exploratory plan now names `125` candidate what-if axes. That
broader map is useful search inventory, but it is not a safety claim. The
closed claim is only the `29` green axes listed below. The remaining `96` axes
stay in backlog until their replay commands are refreshed, their skipped lanes
are split out, or their checks are promoted into Lean, ESSO, Tau, TLA, or
another replayable certificate lane.

## Proof Layer Added For Future Promotion

The current branch adds three reusable Lean theorem schemas that strengthen the
way future axes can be promoted from search inventory into replayable guarantees:

- `Proofs.AMMIntegerRuntimeBridge`: integer-runtime CPMM receipts imply
  no-overdelivery, nondecreasing fee-adjusted `k`, and route rounding envelopes.
- `Proofs.DisasterAntichainBasis`: if every minimal forbidden trace in a basis
  is rejected, and every bad trace contains one of those basis traces, then the
  whole bad family is rejected.
- `Proofs.ForbiddenTraceMinor`: if every bad trace embeds a forbidden motif and
  rejection or guard blocking lifts through that embedding, then the whole bad
  trace family is rejected.
- `Proofs.NoFreeResourceTraceLedger`: if every accepted event carries a safe
  resource delta and the safe cone is closed under trace composition, then an
  accepted trace cannot create a protected resource outside that cone; Nat
  budget lemmas also reject claims above total or prefix budget.
- `Proofs.ZenoDEXDisasterSchemaInstantiations`: small proof adapters for
  ZenoDEX-shaped resource budgets and forbidden motifs, including API scan
  budgets, proof-mining rewards, bounty payouts, proof work, stale settlement,
  missing-oracle settlement, unpaired COW fills, and API overscan.
- `Proofs.CertificateGluing`: locally accepted certificates that glue into one
  compatible global section exclude cross-surface disaster states.

These proofs do not change the closed count from `29` to `125`. They provide
the reusable math needed to turn more axes into concrete claims once each axis
has a matching instantiation and replay receipt.

Receipt:

- `lean-mathlib/proof_receipts/aristotle_runtime_disaster_gluing_2026-04-28.md`
- `lean-mathlib/proof_receipts/forbidden_trace_minor_2026-04-28.md`
- `lean-mathlib/proof_receipts/no_free_resource_trace_ledger_2026-04-28.md`
- `lean-mathlib/proof_receipts/zenodex_disaster_schema_instantiations_2026-04-28.md`

The static proof-schema map is checked by:

```bash
python3 tools/check_disaster_proof_schema_map.py
```

Current output:

```text
axis_count: 29
schema_count: 7
amm_integer_runtime_bridge: 1
certificate_gluing: 13
disaster_antichain_basis: 8
disaster_trace_lifting: 11
forbidden_trace_minor: 15
no_free_resource_trace_ledger: 6
zenodex_disaster_schema_instantiations: 6
```

This map is not a proof that all 29 axes are now fully discharged in Lean. It is
a ratchet that keeps every closed replay axis attached to the theorem schema
that should discharge or strengthen it once the concrete runtime predicates are
instantiated.

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
  --axis-id resource_budget_abort \
  --axis-id repair_after_tamper \
  --axis-id external_state_drift \
  --axis-id atomicity_partial_side_effect \
  --axis-id restart_replay_persistence \
  --axis-id dependency_outage_fail_closed \
  --axis-id reciprocal_netting_pair_forgery \
  --axis-id bounded_advisory_search_envelope \
  --axis-id exact_out_candidate_domain_explosion \
  --axis-id tau_gate_policy_aliasing \
  --axis-id confidential_receipt_attestation_drift \
  --axis-id batch_clearing_fragmentation_ordering \
  --axis-id perp_funding_liquidation_oracle_window \
  --axis-id proof_mining_packet_envelope_replay \
  --axis-id tau_net_client_transport_boundary \
  --axis-id settlement_proof_recompute_gate \
  --axis-id operations_parser_canonical_envelope \
  --axis-id dex_engine_sequence_anomaly_surface \
  --axis-id dex_core_ref_parity_drift \
  --axis-id boundary_concolic_wrapper_consistency \
  --axis-id exact_out_prefilter_winner_repair_boundary \
  --axis-id perp_engine_integration_oracle_bootstrap_boundary \
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

## CI Ratchet

The closed 29-axis receipt is now pinned in
`.github/workflows/disaster-assurance-ratchet.yml`. The workflow runs
`tools/check_disaster_search_closed_receipt.py`, which executes only the closed
axis set and fails if any closed axis becomes failed, skipped, inconclusive, or
missing from the current search inventory.

The same workflow also runs `tools/check_formal_proof_hygiene.py` over critical
Lean proof artifacts, `tools/check_disaster_proof_schema_map.py` over the
closed-axis proof-schema map, and deployment-posture tests on the default
API/resource-safety boundary. That does not turn the bounded receipt into an
exhaustive proof, but it does make regression of the current claim visible on
every main-branch push and pull request.

## Closed Axes

The current green receipt closes these `29` disaster-state families:

1. `epoch_split_brain`
2. `identity_registry_drift`
3. `canonicalization_equivocation`
4. `serialization_width_aliasing`
5. `resource_budget_abort`
6. `repair_after_tamper`
7. `external_state_drift`
8. `atomicity_partial_side_effect`
9. `restart_replay_persistence`
10. `dependency_outage_fail_closed`
11. `reciprocal_netting_pair_forgery`
12. `bounded_advisory_search_envelope`
13. `exact_out_candidate_domain_explosion`
14. `tau_gate_policy_aliasing`
15. `confidential_receipt_attestation_drift`
16. `batch_clearing_fragmentation_ordering`
17. `perp_funding_liquidation_oracle_window`
18. `proof_mining_packet_envelope_replay`
19. `tau_net_client_transport_boundary`
20. `settlement_proof_recompute_gate`
21. `operations_parser_canonical_envelope`
22. `dex_engine_sequence_anomaly_surface`
23. `dex_core_ref_parity_drift`
24. `boundary_concolic_wrapper_consistency`
25. `exact_out_prefilter_winner_repair_boundary`
26. `perp_engine_integration_oracle_bootstrap_boundary`
27. `quote_receipt_transport_intent_boundary`
28. `tau_runner_subprocess_transport_boundary`
29. `dex_settlement_recovery_proof_unit_boundary`

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

The full exploratory plan still contains `96` axes that are not part of the
closed guarantee:

- Some axes still contain skipped external-tool lanes, such as Tau-binary,
  `blake3`, or ESSO-dependent checks.
- Some axes still point at stale or absent public-checkout artifacts.
- Some axes need stronger proof lanes before their bounded tests should be
  counted as prevented-state receipts.

Those axes are useful prompts for future hardening. They should not be counted
as prevented disaster states until they have clean receipts with no failures,
skips, or timeouts.

## Interpretation

The current assurance improvement is real but bounded. The repo now has a
replayable 29-family disaster-state receipt plus a larger 125-axis search map.
The map makes the next search frontier explicit; the receipt is the part that
can be treated as current evidence.
