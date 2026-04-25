# Stateful Disaster-State Witnesses

This note explains what the stateful weird-machine lane has actually demonstrated.

## Core distinction

A dangerous state is witnessed when the campaign can construct it and the
implementation rejects it with a replayable receipt. That means the state exists
in the search space and is currently blocked.

A witnessed reject state is not, by itself, proof that the same state was
previously accepted in production. These witnesses support fail-closed
assurance claims, not retrospective exploit claims.

## Current snapshot

As of `2026-04-08`, the deep stateful lane reports:
- deep gate: `108 passed, 1 warning in 1135.88s`
- dangerous surfaces: `10/10 witnessed`
- reached-but-unwitnessed surfaces: `0`
- unique ranked witnesses: `18`
- hotspot count: `10`

The surface count is a coverage index, not a claim that the state space has only
ten possible bad states. A surface groups a family of related failures, such as
stale settlement replay or route-certificate drift. The witness count records
the minimized replayable examples currently retained for those families.

The useful interpretation is:

```text
WitnessFamilyCovered(F) := exists witness W such that W reaches F and replay rejects W
```

For each selected high-risk family in this release lane, there is at least one
replayable witness that reaches the family and is rejected by the implementation.
That materially improves assurance because a future change can be checked
against concrete attack-shaped states instead of only against line coverage.

## What “witness coverage” means

Code coverage asks whether code ran. Witness coverage asks whether dangerous
semantic states were actually generated, rejected, and stored as reusable
receipts. If branch coverage stayed high but one of these witnesses disappeared,
that would still be a serious regression.

## Highest-value witness families

### 1. Route/certificate canonicalization drift
- witness: `quote_receipt_route_canonicalization_candidate_set_hash_mismatch`
- reject family: `route_canonicalization_guard`
- meaning: candidate reordering plus receipt repair still cannot survive canonical route binding

### 2. Quote-body tamper followed by hash repair
- witness: `quote_receipt_certificate_amount_out_mismatch`
- reject family: `route_certificate_binding_guard`
- meaning: changing the quote body and repairing the hash still breaks the route certificate

### 3. Stale settlement replay
- witness: `dex_engine_settlement_stale_dead_tail`
- reject family: `settlement_freshness_guard`
- meaning: a settlement for an old execution state cannot be replayed after state movement

### 4. Repaired receipt reused after pool drift
- witness: `quote_receipt_transport_repair_then_stale_snapshot`
- reject family: `snapshot_freshness_guard`
- meaning: fixing the transport envelope is not enough once the quoted pool snapshot drifts

### 5. Future-dated settlement attestation
- witness: `settlement_attestation_future_epoch`
- reject family: `attestation_temporal_guard`
- meaning: settlement attestations are rejected if they are dated in the future relative to the consumer epoch

## Hotspot interpretation

The current weird-machine pressure is concentrated on canonicalization and
freshness semantics, not on shallow transport parsing. The most important
guards to preserve are route canonicalization, route-certificate binding,
settlement freshness, snapshot freshness, and attestation-time guards.

## Public reporting guidance

The strongest honest public claim is:
- ZenoDEX has replayable minimized witnesses for 10 dangerous stateful protocol surfaces.
- The deep lane demonstrates fail-closed handling for routing/canonicalization drift, stale quote reuse, stale settlement reuse, replay, attestation policy/time drift, duplicate signatures, and unauthorized envelopes.
- Previously reached-but-unwitnessed surfaces in this stateful lane have been removed.

The claim to avoid is:
- "we found and fixed 10 live exploitable bugs"

That stronger claim would require separate evidence that these states were previously admitted rather than currently rejected.
