# ZRPF Spot V7 Single Atomic Authority Join V1

Status: code-ready implementation plan; authority activation remains unavailable.

Date: 2026-07-15

## Decision

The current tree must not expose an authority-bearing Spot V7 commit yet.
Several prerequisite types either permanently report their authority property as
false or intentionally expose no production mint. Constructing an authority
capability from them would convert an explicit non-claim into settlement power.

The existing V6 operational store already supplies the reusable atomic database
mechanics. In one `BEGIN IMMEDIATE` transaction it persists:

- economic cell transitions and the economic post-state root;
- economic action, authorization, grant-spend, and consumed-object uniqueness;
- exact proof, journal, runtime, DA, finality, and replay identities;
- operational-policy provenance;
- retained finality-checker request, response, executable, and manifest bytes;
- application and operational cursors;
- complete-history validation before commit.

The production work is therefore a versioned authenticated-prerequisite seam
and a V7 schema that admits only that seam. The existing economic store remains
the implementation base.

## Verified blockers in the current source

### B1. Semantic proof authority has no Spot V7 store capability

`PinnedRecursiveStarkVerifier` can mint a private authenticated recursive-root
value and commit replay indexes to its own store. The Spot V7 settlement store
does not consume that value. Its candidate path still uses
`_seal_test_only_spot_v7_settlement_v1` while persisting proof identities.

Required closure: one private Spot-specific proof projection derived from the
single successful RISC0 verification. It must bind the exact V7 receipt,
journal, program ID, profile ID, program-manifest root, source-child claim,
settlement plan, action/nullifier roots, cell-transition root, pre-state root,
and post-state root.

### B2. The live Firecracker runtime exposes no authority mint

`_zrpf_spot_v7_firecracker_authority.py` deliberately raises
`SpotV7FirecrackerAuthorityUnavailableV1`. The candidate-bound Linux runner
also reports runtime, release, settlement, and production authority as false.

Required closure: a private runtime result minted only by the completed
privileged Jailer lifecycle after descriptor-stable artifact capture, governed
release selection, exact request/output validation, cgroup membership and
teardown, exclusive network namespace validation, and exact V7 payload binding.

### B3. DA response-time provenance remains false

`_GovernedSpotV7DataAvailabilityPrerequisiteV2` authenticates exact content,
sampled evidence, signed policy, and beacon provenance. Its
`response_timing_provenance_verified` property remains false because the
response epoch is not yet proven by finalized inclusion evidence.

Required closure: a versioned private DA capability that binds the exact sampled
response batch to a finalized ledger body and proves:

```text
checked_epoch <= finalized_inclusion_epoch <= response_deadline_epoch
```

Provider independence, continuous availability, and future public availability
remain separate policy claims unless their own governed profile requires and
authenticates them.

### B4. Release currentness is an authority-neutral observation

The authenticated release-state Store V3 and current-release execution binding
establish canonical local history. The current binding explicitly leaves
`currentness_at_settlement_established` false. The external highest-observed
watermark is also authority-neutral.

Required closure: release selection, revocation, and settlement currentness must
share one serializable commit domain, or one externally finalized monotonic
release head must be authenticated at the same checkpoint consumed by the
settlement. A checked value from a separate database cannot establish currentness
after that database is unlocked.

### B5. The finality checker identity is not release-governed at consumption

The checkpoint finality adapter cryptographically authenticates the ZenoLedger
quorum and the V6 store retains an exact manifest-pinned checker invocation.
`release_governed_checkpoint_finality_checker_identity_verified` remains false.

Required closure: the current, nonrevoked release manifest must commit the exact
checker authority manifest and executable digest, and the atomic transaction
must compare those identities with the retained invocation.

## Target trust progression

```text
untrusted V7 receipt bytes
  -> one governed verifier execution
  -> _AuthenticatedSpotV7SemanticProofV1

privileged Jailer execution over the selected release
  -> _AuthenticatedLiveSpotV7FirecrackerExecutionV1

exact blob plus finalized sampled-response inclusion
  -> _AuthenticatedSpotV7DaTransitionV3

ZenoLedger quorum plus release-selected checker invocation
  -> _AuthenticatedSpotV7FinalityTransitionV4

signed release events plus externally monotonic checkpoint
  -> locked release-state row in the unified V7 store

all exact private values and one governed policy
  -> _SpotV7AuthorityCommitCapabilityV1
  -> one BEGIN IMMEDIATE transaction
  -> economic state, replay/nullifiers, evidence, and cursors
```

Raw bytes, mappings, report dictionaries, caller booleans, local test seals, and
authority-neutral observations must never satisfy one of these typed inputs.

## Minimal production types

Implement these types in narrow private modules. Every type must be final,
immutable, non-copyable, non-serializable, privately sealed, and reconstructed
from its authoritative source when durable history is replayed.

### `_AuthenticatedSpotV7SemanticProofV1`

Mint location: the exact successful Spot V7 receipt-verifier path.

Projection:

```text
application_id
chain_or_domain_id
epoch_id
verified_program_id
verified_profile_id
verified_program_manifest_root
receipt_sha256
journal_sha256
source_child_claim_binding
source_child_journal_sha256
settlement_effect_plan_commitment
economic_action_id
authorization_nullifier
authorization_grant_spend_nullifier
consumed_object_ids_root
cell_transitions_root
asset_effects_root
pre_state_root
post_state_root
exact_receipt_bytes
exact_journal_bytes
proof_verifier_authority_manifest_sha256
proof_verifier_executable_sha256
proof_verification_request_sha256
proof_verification_response_sha256
```

No public constructor. The Spot projection must be derived from the already
authenticated journal. The host must not supply the projected values again.

### `_AuthenticatedLiveSpotV7FirecrackerExecutionV1`

Mint location: the one-shot root-owned Linux supervisor after successful output
validation and complete teardown.

Projection:

```text
release_candidate_id
release_revision
runtime_manifest_sha256
artifact_set_root
kernel_sha256
rootfs_sha256
input_drive_sha256
firecracker_sha256
jailer_sha256
netns_helper_sha256
machine_config_sha256
authority_input_profile_sha256
request_sha256
output_sha256
execution_record_sha256
run_nonce
candidate_settlement_commitment
candidate_journal_sha256
candidate_receipt_sha256
cgroup_identity
network_namespace_identity
```

The capability may be minted only after `cgroup.events` reports `populated=0`
and the supervisor has validated the final output through stable descriptors.

### `_AuthenticatedSpotV7DaTransitionV3`

Mint location: a protocol-specific finalized-inclusion adapter over the existing
exact-content and sampled-retrievability capabilities.

Projection:

```text
policy_root
full_blob_certificate_root
data_root
blob_sha256
sampled_evidence_root
beacon_checkpoint_hash
checked_epoch
response_deadline_epoch
finalized_inclusion_epoch
finalized_inclusion_block_hash
finalized_inclusion_body_root
finalized_inclusion_proof_root
provider_set_root
exact_certificate_bytes
exact_sampled_evidence_bytes
exact_inclusion_evidence_bytes
```

V3 must derive the response epoch from the finalized inclusion record. It must
not trust a provider-signed, caller-declared response epoch by itself.

### `_AuthenticatedSpotV7FinalityTransitionV4`

Mint location: the existing ZenoLedger quorum adapter followed by the exact
release-governed checker cross-check.

Projection:

```text
policy_root
certificate_root
proof_journal_hash
post_state_root
prior_checkpoint_sequence
prior_checkpoint_hash
next_checkpoint_sequence
next_checkpoint_hash
finality_evidence_root
checker_authority_manifest_sha256
checker_executable_sha256
checker_request_sha256
checker_response_sha256
release_candidate_id
release_revision
```

### `_SpotV7AuthorityCommitCapabilityV1`

Mint location: a private binder in
`_zrpf_spot_v7_authority_commit_capability_v1.py`.

Inputs:

```text
_AuthenticatedSpotV7SemanticProofV1
_AuthenticatedLiveSpotV7FirecrackerExecutionV1
_GovernedSpotV7OperationalPolicyV3
_AuthenticatedSpotV7DaTransitionV3
_AuthenticatedSpotV7FinalityTransitionV4
_DurablyReverifiedSpotV7SettlementReplayV2
expected economic cursor
expected release-state cursor
```

The binder checks equality of every duplicated commitment. It carries no input
Boolean and exposes no authority property. Its sole consumer is the V7 store.

## Release-state atomicity choice

Use one SQLite database as the write authority after a governed cutover. This is
the smallest design that makes current release selection and settlement
currentness one transaction.

The V7 schema must contain the authenticated release-event log and current
release head used for settlement. The existing release Store V3 may be imported
only through a maintenance-mode cutover that:

1. obtains an externally finalized store-derived checkpoint;
2. validates the complete release history against that checkpoint;
3. inserts the history and current head into the empty V7 operational store;
4. records the source store identity, final imported revision, state root, and
   external anchor;
5. marks the old store retired before the V7 store accepts any settlement;
6. makes the V7 store the sole writer for later select and revoke events.

Do not use a read from the separate release Store V3 followed by an economic
commit. The release may be revoked between those operations.

## V7 schema delta

Create `_zrpf_spot_v7_atomic_settlement_schema_v7.py` by extending the exact V6
schema. Preserve all V6 uniqueness and history tables. Add these tables.

### `spot_v7_release_state_v7`

Singleton current head:

```text
database_revision
last_evaluation_epoch
release_state_root
current_candidate_id nullable
current_candidate_sha256 nullable
current_release_revision nullable
current_select_input_id nullable
current_revocation_record_id nullable
external_anchor_position
external_anchor_commitment
```

All integers use fixed-width big-endian blobs or existing bounded integer
conventions. Candidate fields are either all present or all absent. An active
candidate requires a null revocation ID.

### `spot_v7_release_events_v7`

Append-only selected and revoked signed envelopes, signer-set roots, quorum
evidence, exact canonical input bytes, event IDs, parent revision/root, result
revision/root, external anchor, and event kind. Event IDs and input IDs are
unique.

### `spot_v7_authoritative_proof_v7`

One row per settlement containing all proof projection digests, exact receipt
and journal bytes, verifier identity, request/response hashes, and the release
candidate/revision that selected the verifier.

### `spot_v7_authoritative_runtime_v7`

One row per settlement containing the live run nonce, exact request/output and
execution-record hashes, immutable artifact roots, cgroup/netns identities, and
selected release candidate/revision. Nonce and execution-record hash are unique.

### `spot_v7_authoritative_da_v7`

One row per settlement containing exact content and sampled roots plus finalized
response-inclusion position and proof. The sampled response and inclusion proof
identities are unique.

### `spot_v7_authoritative_finality_v7`

One row per settlement containing the quorum certificate, exact checker
invocation, release-selected checker identity, and exact prior/successor cursor.
The successor sequence/hash and request/response identities are unique.

### `spot_v7_authority_commit_v7`

One row per settlement containing a domain-separated `authority_prerequisite_root`
over the proof, runtime, release, policy, DA, finality, replay, and expected
cursor projections. Store the profile/version identifier used to derive it.

Do not store caller-provided `verified`, `settlement_authority`, or
`production_authority` values. The existence of a fully validated V7 row under
the exact schema is the scoped commit fact. Public production posture remains a
separate release-policy decision.

## Exact transaction algorithm

The public integration surface should be one method:

```python
store.commit_authoritative_spot_v7(
    expected_cursor=...,
    expected_release_cursor=...,
    capability=...,
)
```

The method performs bounded type and identity preflight, then:

```text
BEGIN IMMEDIATE

1. Validate exact V7 schema and complete prior economic, operational, release,
   proof, runtime, DA, finality, and replay history.

2. Reconstruct every projection from the sealed capability. Never accept a
   prebuilt packet or a mapping at this boundary.

3. Compare the expected economic cursor with `spot_v7_store_meta`.

4. Compare the expected release cursor with `spot_v7_release_state_v7`.

5. Require the selected release candidate and revision to equal the proof,
   runtime, policy, finality-checker, and execution-manifest bindings.

6. Require `current_revocation_record_id IS NULL` in the locked release row.

7. Require the release external anchor to be at least the governed minimum and
   to match the authenticated monotonic checkpoint carried by the capability.

8. Require candidate pre-state root = current economic state root.

9. Require proof post-state, finality post-state, runtime payload post-state,
   and candidate post-state to be byte-identical.

10. Require economic action, authorization nullifier, grant-spend nullifier,
    consumed objects, receipt, journal, source child, runtime nonce, DA sample,
    finality cursor, and prerequisite root to be globally unused.

11. Require finalized DA response inclusion within the governed response
    interval and bind the inclusion block to authenticated finality.

12. Persist the V6 economic candidate and operational rows.

13. Persist exact V7 proof, runtime, DA, finality, release, replay, and authority
    rows.

14. Apply typed cell transitions and asset effects.

15. Compare-and-swap the application checkpoint, economic cursor, release
    cursor observation, and any DA/retrievability cursor.

16. Validate the complete post-write histories and recompute every root.

17. Materialize the durable receipt from stored rows.

COMMIT
```

Any typed rejection rolls back and returns the exact pre-state. An ambiguous
commit acknowledgement returns `COMMIT_OUTCOME_UNKNOWN`; callers reconcile by
retrying the same authority-prerequisite root and settlement commitment.

## Invariant ownership

| Invariant | Owning layer |
| --- | --- |
| Receipt seal, image, profile, and journal | proof verifier |
| Exact settlement semantics and state transition | Spot V7 guest/journal |
| Runtime artifact and request/output execution | privileged Firecracker supervisor |
| Release selection and revocation signatures | release-event adapter |
| Release currentness at commit | locked V7 release-state row plus external anchor |
| Exact blob identity | full-blob verifier |
| Sample response validity | sampled retrievability verifier |
| Response inclusion timing | finalized-inclusion adapter |
| Application checkpoint finality | ZenoLedger quorum adapter |
| Checker identity | current release manifest plus exact invocation |
| Replay/nullifier uniqueness | V7 SQL unique constraints |
| State and cursor atomicity | one V7 SQLite transaction |
| Production enablement | separate governed release posture |

## Required implementation PR sequence

### PR A: Spot proof projection

Files:

```text
src/integration/_zrpf_spot_v7_authenticated_proof_v1.py
src/integration/recursive_stark_verifier_adapter.py
tests/integration/test_zrpf_spot_v7_authenticated_proof_v1.py
```

Acceptance:

- one receipt verification creates one private projection;
- every journal field mutation rejects;
- wrong image, profile, manifest, receipt kind, and child binding reject;
- raw facts, mappings, and test-only settlement seals reject;
- no settlement or production authority property is introduced.

### PR B: finalized DA response inclusion

Files:

```text
src/integration/zrpf_spot_v7_finalized_da_inclusion_v1.py
src/integration/zrpf_spot_v7_governed_da_prerequisite_v3.py
tests/integration/test_zrpf_spot_v7_finalized_da_inclusion_v1.py
tests/integration/test_zrpf_spot_v7_governed_da_prerequisite_v3.py
```

Acceptance:

- inclusion is proven under a finalized body root;
- response bytes and provider signature are the exact included object;
- early, late, wrong-body, wrong-policy, wrong-beacon, and replay cases reject;
- `response_timing_provenance_verified` is true only on the new private type.

### PR C: release cutover and unified history

Files:

```text
src/integration/_zrpf_spot_v7_release_state_schema_v7.py
src/integration/_zrpf_spot_v7_release_state_engine_v7.py
tools/zrpf_spot_v7_release_store_cutover_v1.py
tests/integration/test_zrpf_spot_v7_release_state_v7.py
tests/test_zrpf_spot_v7_release_store_cutover_v1.py
```

Acceptance:

- imported history exactly matches a finalized Store V3 checkpoint;
- old store retirement and new-store activation are explicit;
- selection, revocation, and settlement serialize on one write lock;
- a concurrent revocation causes the settlement or revocation to retry, and a
  settled transaction can never use a release revoked first.

### PR D: governed live Firecracker mint

Files:

```text
src/integration/_zrpf_spot_v7_live_firecracker_execution_v1.py
tools/zrpf_spot_v7_firecracker_root_supervisor.py
tools/zrpf_spot_v7_firecracker_linux_runner.py
tests/integration/test_zrpf_spot_v7_live_firecracker_execution_v1.py
```

Acceptance:

- the mint is reachable only from the completed privileged supervisor;
- output is candidate-bound and release-selected;
- teardown precedes mint;
- stale output, nonce replay, path replacement, cgroup escape, netns escape,
  altered artifact, altered release, and incomplete teardown reject;
- a real KVM/Jailer run produces the evidence. Mock-only evidence is insufficient.

### PR E: release-governed finality checker

Files:

```text
src/integration/zrpf_spot_v7_checkpoint_finality_checker_adapter_v2.py
tests/integration/test_zrpf_spot_v7_checkpoint_finality_checker_adapter_v2.py
```

Acceptance:

- exact checker manifest and executable are selected by the locked release;
- the checker runs once;
- exact request/response bytes remain replayable;
- checker substitution, release revision drift, and revocation reject.

### PR F: V7 atomic authority store

Files:

```text
src/integration/_zrpf_spot_v7_authority_commit_capability_v1.py
src/integration/_zrpf_spot_v7_atomic_settlement_schema_v7.py
src/integration/_zrpf_spot_v7_atomic_settlement_engine_v7.py
src/integration/_zrpf_spot_v7_atomic_settlement_history_v7.py
src/integration/zrpf_spot_v7_atomic_authority_store_v7.py
tests/integration/test_zrpf_spot_v7_atomic_authority_store_v7.py
```

Build this PR last. It consumes the exact private types from PRs A through E.
It must contain no test-only mint in production modules.

## Mandatory negative and concurrency tests

1. A forged nominal object cannot reach the transaction.
2. A raw report with every authority Boolean set true rejects.
3. A proof and runtime payload for different settlement commitments reject.
4. A proof and release manifest for different program IDs reject.
5. A policy or checker selected by a stale release revision rejects.
6. A revocation committed before settlement causes settlement rejection.
7. Concurrent settlement and revocation from one release cursor cannot both
   claim they observed the unrevoked pre-state.
8. Two workers submitting the same action/nullifier yield exactly one commit.
9. Two different proofs for the same economic action yield exactly one commit.
10. A DA response included after its deadline rejects.
11. A valid sampled response absent from the finalized body rejects.
12. A finality successor from the wrong prior cursor rejects.
13. A runtime nonce or output reused under a different proof rejects.
14. A crash after any individual insert rolls back every economic and evidence
    row.
15. An ambiguous commit acknowledgement is reconciled by exact retry.
16. Database reopening replays and revalidates all proof, runtime, release, DA,
    finality, replay, and economic history without executing external binaries.
17. Any persisted byte or digest mutation prevents reopening.
18. Release-store rollback below the highest externally anchored revision
    pauses settlement.

## Promotion gate

The V7 path may be described as authority-bearing only after all of these are
machine-verified on one final source closure:

```text
fresh V6/V7 image IDs and receipts
exact semantic receipt mutation rejection
one-verification Spot proof projection
finalized DA response inclusion
authenticated external monotonic release anchor
unified release/settlement transaction
release-selected finality checker
live privileged Firecracker/Jailer run
complete cgroup/netns teardown evidence
single-transaction crash and concurrency evidence
source-built replay
release manifest and revocation replay
independent security review
```

Until then retain:

```text
proof_receipt_authority = false
runtime_authority = false
release_authority = false
settlement_authority = false
production_authority = false
```

## Current safe next step

Implement PR A and PR B while the Firecracker lane completes its live evidence.
They are independent and close real authority gaps. Start PR C only after the
external release-finality protocol and old-store retirement procedure are
governed. PR F is mechanically small once those prerequisites exist because the
V6 store already contains the economic atomic-commit core.
