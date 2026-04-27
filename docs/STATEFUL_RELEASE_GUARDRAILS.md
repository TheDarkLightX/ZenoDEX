# Stateful Release Guardrails

This note turns the current stateful weird-machine assurance results into a release checklist.

## Receipt basis

```text
ReleaseGuardrailBasis := DeepGateGreen ∧ WitnessedSurfaces=10 ∧ ReachedNoWitness=0
```

Plain English: the guardrails below are based on a clean deep lane, full dangerous-surface witness coverage, and no remaining reachability gaps.

Practical consequence: routing, settlement, quote-receipt, and attestation refactors should preserve these witnesses before release.

Current basis snapshot as of `2026-04-08`:
- deep gate: `108 passed, 1 warning in 1135.88s`
- witnessed surfaces: `10`
- reached-but-unwitnessed surfaces: `0`
- unique ranked witnesses: `18`
- hotspot count: `10`

## Release bar

```text
ReleaseOK -> DeepGateGreen ∧ TopWitnessesReplay ∧ CriticalSurfaceCoverageStable
```

Plain English: a release is acceptable only if the deep lane stays green, the top witness set still replays to the same reject families, and no critical surface loses witness coverage.

Practical consequence: these checks are release-blocking for the highest-value semantic boundaries.

## Critical witness set

1. `quote_receipt_route_canonicalization_candidate_set_hash_mismatch`
   - expected guard family: `route_canonicalization_guard`
2. `quote_receipt_certificate_amount_out_mismatch`
   - expected guard family: `route_certificate_binding_guard`
3. `dex_engine_settlement_stale_dead_tail`
   - expected guard family: `settlement_freshness_guard`
4. `quote_receipt_transport_repair_then_stale_snapshot`
   - expected guard family: `snapshot_freshness_guard`
5. `settlement_attestation_future_epoch`
   - expected guard family: `attestation_temporal_guard`

These must continue to replay to the same reject-family class before release.

## Hotspot ordering

```text
PriorityOrder := preserve_canonicalization > preserve_freshness > preserve_replay > preserve_transport
```

Plain English: canonicalization and freshness guards carry more safety load than lower-level envelope hygiene.

Practical consequence: do not weaken or de-prioritize the top canonicalization/freshness witnesses first.

Current hotspot order:
1. `quote_receipt_certificate_boundary`
2. `stale_settlement_boundary`
3. `stale_quote_receipt_boundary`
4. `settlement_attestation_policy_boundary`
5. `route_canonicalization_boundary`
6. `nonce_replay_guard`
7. `quote_receipt_pool_envelope_boundary`
8. `quote_receipt_transport_boundary`
9. `operations_signature_reuse_boundary`
10. `api_request_authorization_boundary`

## Guard families carrying the most safety load

```text
MainSafetyLoad := route_canonicalization_guard ∨ settlement_freshness_guard ∨ snapshot_freshness_guard ∨ attestation_temporal_guard
```

Plain English: the system currently relies most heavily on canonicalization, freshness, and attestation-time guards.

Practical consequence: any refactor touching these guard families should require explicit witness replay before merge.

High-priority guard families:
- `route_canonicalization_guard`
- `route_certificate_binding_guard`
- `settlement_freshness_guard`
- `snapshot_freshness_guard`
- `attestation_temporal_guard`
- `attestation_policy_guard`
- `attestation_packet_binding_guard`

## Scope limit

```text
ThisNote := operator_release_guardrail ∧ not_claim_of_formal_proof
```

Plain English: this is an operator-facing release discipline, not a formal proof artifact.

Practical consequence: it complements proofs, kernels, and formal contracts rather than replacing them.
