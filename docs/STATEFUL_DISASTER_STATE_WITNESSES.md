---
title: STATEFUL_DISASTER_STATE_WITNESSES
type: note
permalink: autonomous-tau-dex-review/docs/stateful-disaster-state-witnesses
---

# Stateful Disaster-State Witnesses

## Scope

This note summarizes the stateful weird-machine assurance lane for ZenoDEX.
It is intentionally conservative about what is being claimed.

```text
WitnessedRejectState(D) := campaign_reaches(D) ∧ system_rejects(D)
```

Standard reading: a disaster state `D` is *witnessed* when the stateful campaign can produce it and the system rejects it with a replayable receipt.

Practical consequence: the witness proves a dangerous state exists in the search space and is blocked by the current implementation.

```text
RemovedBlindSpot(S) := previously_reached_without_witness(S) -> now_reached_with_witness(S)
```

Standard reading: an assurance blind spot is removed when a surface that was previously reached but not captured as a first-class witness is now backed by a replayable minimized witness.

Practical consequence: this strengthens regression defense and public assurance posture.

## What This Note Does Not Claim

This note does **not** claim that each witness corresponds to a previously exploitable production bug.
Most witnesses here are fail-closed receipts: they show that a dangerous state is constructed and rejected.
That is valuable, but it is different from proving the system used to accept that state.

```text
WitnessedRejectState(D) ≠ PreviouslyAcceptedBug(D)
```

Standard reading: witnessing and rejecting a dangerous state does not, by itself, prove that the same state was previously accepted.

Practical consequence: public reporting should say "witnessed and rejected" unless there is separate evidence that a bad state used to pass.

## Current State

The deep stateful acceptance lane now covers nine declared dangerous surfaces.
All nine are backed by replayable minimized witnesses.

Current lane status:
- deep stateful gate: `91 passed, 1 warning`
- stateful dangerous surfaces: `9/9 witnessed`
- reached-but-unwitnessed surfaces: `0`
- atlas status: `complete`
- curated stateful tooling typecheck: `20 source files`, green

## Witness Families

### 1. Unauthorized request envelopes
- Witness ID: `api_request_unauthorized`
- Representative outcome: `handled:401:unauthorized`
- Bad state: an unauthorized API request attempts to cross the admission boundary.
- Current behavior: rejected before runtime admission.
- Why it matters: blocks unauthenticated request weird machines at the outer boundary.

### 2. Duplicate signature binding
- Witness ID: `operations_duplicate_signature`
- Representative outcome: `signature provided twice (envelope + field)`
- Bad state: a signed operation carries duplicated or ambiguous signature material.
- Current behavior: parse/validation failure.
- Why it matters: blocks ambiguous signature-binding and signature-reuse interpretation bugs.

### 3. Cross-batch nonce replay
- Witness IDs: `nonce_cross_batch_replay`, `dex_engine_replay_dead_tail`
- Representative outcome: `reject:step=1:nonce sequence invalid`
- Bad state: a previously consumed nonce sequence is replayed in a later batch.
- Current behavior: rejected by the nonce/replay boundary.
- Why it matters: blocks double-execution and replay-style state machines.

```text
ConsumedNonceSequence ∧ ReplayAttempt -> reject
```

Standard reading: once a nonce sequence has been consumed, replaying it is rejected.

Practical consequence: the protocol does not silently re-accept already-consumed intent sequences.

### 4. Missing receipt hash at the transport boundary
- Witness ID: `quote_receipt_missing_hash`
- Representative outcome: `reject:missing_receipt_hash`
- Bad state: a quote receipt body travels without its required transport hash.
- Current behavior: rejected at transport verification.
- Why it matters: blocks detached-body and envelope-binding failures.

### 5. Stale quote receipt reuse after pool drift
- Witness ID: `dex_engine_quote_receipt_stale_dead_tail`
- Representative outcome: `pool_snapshot_mismatch`
- Bad state: a quote receipt generated against one pool snapshot is replayed after the pool state changes.
- Current behavior: rejected as a stale receipt.
- Why it matters: blocks stale-quote execution and quote/body mismatch reuse.

```text
QuoteReceiptBoundToSnapshot ∧ PoolStateChanged -> reject
```

Standard reading: if the pool snapshot changes after a quote receipt is issued, replaying that receipt is rejected.

Practical consequence: stale price surfaces do not silently cross into execution.

### 6. Stale provided settlement replay
- Witness ID: `dex_engine_settlement_stale_dead_tail`
- Representative outcome: `reject:step=1:settlement mismatch`
- Bad state: a settlement prepared for an old execution state is replayed after the execution surface changes.
- Current behavior: rejected during settlement verification.
- Why it matters: blocks stale settlement application and reserve/balance corruption paths.

```text
SettlementComputedOnOldState ∧ StateChanged -> reject
```

Standard reading: a settlement computed against an old state cannot be applied after the state changes.

Practical consequence: stale settlement packets do not survive state drift.

### 7. Route-certificate candidate-set tampering
- Witness ID: `route_certificate_candidate_set_hash_mismatch`
- Representative outcome: `reject:step=1:candidate_set_hash mismatch`
- Bad state: a route certificate is replayed against a changed candidate set.
- Current behavior: rejected because the certified candidate set no longer matches.
- Why it matters: blocks route substitution and candidate-set injection attacks.

```text
CertificateBuiltForCandidates(C) ∧ ReplayOn(C') ∧ C' != C -> reject
```

Standard reading: a certificate built for one candidate set cannot be replayed on a different candidate set.

Practical consequence: route certificates stay bound to the candidate universe they were issued for.

### 8. Route canonicalization drift
- Witness ID: `route_canonicalization_candidate_set_hash_mismatch`
- Representative outcome: `reject:step=1:candidate_set_hash mismatch`
- Bad state: canonical winner selection is asked to survive a changed candidate set.
- Current behavior: rejected instead of silently reinterpreting the certificate.
- Why it matters: protects canonical winner binding and tie-break stability.

### 9. Settlement attestation tampering and policy drift
- Witness ID: `settlement_attestation_signature_invalid`
- Representative outcome: `reject:step=1:settlement spot price attestation signature invalid`
- Other witnessed reject states in the same family:
  - attestation in the future
  - stale attestation
  - packet-hash mismatch
  - source allowlist drift
- Bad state: an attestation is tampered with, stale, future-dated, or no longer permitted by source policy.
- Current behavior: rejected before settlement admission.
- Why it matters: blocks forged or policy-invalid settlement price attestations.

## What Was Fixed In The Assurance Stack

The main engineering improvements were:
- adding a fast default policy-mode attestation explorer so the attestation boundary is exercised in the deep lane by default
- promoting route-certificate and attestation-policy surfaces from reached-only to witnessed
- eliminating the remaining `reached_no_witness` surfaces in the dangerous-surface manifest
- adding a curated typechecked boundary for the stateful assurance tooling

## Reproduction Commands

Deep stateful lane:

```bash
bash tools/run_acceptance_tcb_fuzz_gate_deep.sh
```

Full stateful campaign receipt:

```bash
python3 tools/acceptance_tcb_fuzz_campaign.py --format json --gate-lane deep --run-id local-stateful-receipt
```

The command above writes local artifacts under the local campaign artifact directory including:
- minimized witness receipts
- stateful introspection
- weird-machine atlas

Those artifacts are intended as local replay receipts, not as committed public repo state.

## Public Reporting Guidance

The strongest honest public claim is:
- ZenoDEX now has replayable minimized witnesses for nine dangerous stateful protocol surfaces.
- The deep stateful lane demonstrates fail-closed handling for replay, stale quote receipts, stale settlements, route-certificate tampering, attestation tampering, duplicate signatures, and unauthorized envelopes.
- Previously reached-but-unwitnessed surfaces in this lane have been removed.

The claim to avoid is:
- "we found nine previously exploitable critical bugs"

That stronger claim would require separate evidence that these states were previously admitted rather than currently rejected.