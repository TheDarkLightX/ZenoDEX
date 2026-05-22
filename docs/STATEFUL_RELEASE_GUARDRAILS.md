# Stateful Release Guardrails

This note turns the current stateful weird-machine assurance results into a release checklist.

## Receipt basis

```text
ReleaseGuardrailBasis := DeepGateGreen ∧ WitnessedSurfaces=10 ∧ ReachedNoWitness=0
```

Standard reading: the release guardrails are based on a clean deep stateful campaign, full dangerous-surface witness coverage, and no remaining reachability gaps.

Practical consequence: this note is only valid as long as the deep lane continues to produce the same class of receipts.

Current basis snapshot:
- deep gate: `109 passed, 1 warning in 683.63s (0:11:23)`
- witnessed surfaces: `10`
- reached but unwitnessed surfaces: `0`
- unique ranked witnesses: `18`
- hotspot count: `10`

## Release bar

```text
ReleaseOK -> DeepGateGreen ∧ TopWitnessesReplay ∧ CriticalSurfaceCoverageStable
```

Standard reading: a release is acceptable only if the deep gate stays green, the top witness set still replays to the same reject families, and no critical surface loses witness coverage.

Practical consequence: these checks should be treated as release-blocking for routing, settlement, quote-receipt, and attestation refactors.

## Critical witness set

The following witnesses are the strongest current guardrails and must remain replayable.

### 1. Route canonicalization drift against a repaired quote receipt

Witness ID:
- `quote_receipt_route_canonicalization_candidate_set_hash_mismatch`

Expected reject family:
- `route_canonicalization_guard`

Invariant:
```text
candidate_reorder ∧ receipt_rehash -> reject(candidate_set_hash mismatch)
```

Standard reading: if the route candidates are reordered and the receipt hash is repaired, the canonical route certificate must still fail.

Practical consequence: this blocks a high-value weird machine where an attacker tries to keep the receipt structurally valid while changing the winner relation.

### 2. Quote-body tamper followed by hash repair

Witness ID:
- `quote_receipt_certificate_amount_out_mismatch`

Expected reject family:
- `route_certificate_binding_guard`

Invariant:
```text
tamper_amount_out ∧ rehash -> reject(canonical_route_certificate_amount_out_mismatch)
```

Standard reading: changing the quoted amount and then repairing the transport hash must still break the route certificate.

Practical consequence: this blocks cosmetic repair of a maliciously edited quote body.

### 3. Stale settlement replay after valid state movement

Witness ID:
- `dex_engine_settlement_stale_dead_tail`

Expected reject family:
- `settlement_freshness_guard`

Invariant:
```text
settlement_for_old_state ∧ state_moved -> reject(settlement mismatch)
```

Standard reading: a settlement computed for an earlier state must fail once the state changes.

Practical consequence: this is one of the closest witnesses to actual value-transfer corruption, so it is release-critical.

### 4. Receipt transport repair followed by stale snapshot reuse

Witness ID:
- `quote_receipt_transport_repair_then_stale_snapshot`

Expected reject family:
- `snapshot_freshness_guard`

Invariant:
```text
drop_hash ∧ rehash ∧ snapshot_drift -> reject(pool_snapshot_mismatch)
```

Standard reading: repairing the receipt envelope is not enough; if the pool snapshot drifts afterward, the quote must still fail.

Practical consequence: this blocks repaired-but-stale quote reuse.

### 5. Future-dated settlement attestation

Witness ID:
- `settlement_attestation_future_epoch`

Expected reject family:
- `attestation_temporal_guard`

Invariant:
```text
signed_at_epoch > consumer_now_epoch -> reject
```

Standard reading: a future-dated attestation must not cross the settlement attestation boundary.

Practical consequence: this blocks temporal skew abuse in the attestation path.

## Hotspot ordering

```text
PriorityOrder := preserve_canonicalization > preserve_freshness > preserve_replay > preserve_transport
```

Standard reading: canonicalization and freshness guards carry more safety load than lower-level envelope hygiene.

Practical consequence: if CI budgets or review attention are constrained, do not weaken or de-prioritize the top canonicalization/freshness witnesses first.

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

Standard reading: the system currently relies most heavily on canonicalization, freshness, and attestation-time guards.

Practical consequence: any refactor touching these guard families should require explicit witness replay before merge.

High-priority guard families:
- `route_canonicalization_guard`
- `route_certificate_binding_guard`
- `settlement_freshness_guard`
- `snapshot_freshness_guard`
- `attestation_temporal_guard`
- `attestation_policy_guard`
- `attestation_packet_binding_guard`

## Failure interpretation rule

```text
CriticalWitnessRank ≠ ProvenLiveExploit
```

Standard reading: a critical-ranked witness is a high-value rejected bad state, not proof that the protocol previously accepted an exploit.

Practical consequence: public reporting should say these witnesses strengthen fail-closed assurance, not that they prove a past production exploit.

## Minimal release checklist

1. Run the deep acceptance TCB fuzz campaign.
2. Confirm the deep gate remains green.
3. Confirm all 10 dangerous surfaces remain `witnessed`.
4. Confirm `reached_no_witness = 0`.
5. Confirm the five critical witnesses above still replay to the same reject families.
6. Confirm the top hotspot ordering has not materially shifted without explanation.
7. If any top witness disappears or changes reject family, stop and investigate before release.

## Scope limit

```text
ThisNote := operator_release_guardrail ∧ not_claim_of_formal_proof
```

Standard reading: this note is an operator-facing release discipline, not a formal proof artifact.

Practical consequence: it complements, but does not replace, proofs, kernels, or formal contracts.
