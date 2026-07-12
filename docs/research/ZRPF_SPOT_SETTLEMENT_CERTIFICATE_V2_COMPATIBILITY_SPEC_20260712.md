# ZRPF State-Bound Spot Settlement Certificate V2 Compatibility Specification

Date: 2026-07-12

Status: implemented and host-tested for T17; settlement guest, L2 image pin,
receipt verification, sealed verifier, atomic admission, and settlement
authority pending

## Scope

This specification defines a proof-neutral state-bound compatibility composer:

```text
compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2(
  exact ProposedValueAggregateV5,
  exact SpotSettlementAuthorizationInputV1,
  exact SparseMerkleCellTransitionWitnessV1,
  derived semantic_claim_binding,
  exact FullBlobDataAvailabilityCertificateV1,
) -> SettlementEpochCertificateV1 | typed reject
```

The composer must call `derive_spot_settlement_state_projection_v2`. The
resulting action batch and `SettlementEffectPlanV2` use the sparse witness's
complete ledger pre-state and post-state roots. Raw Spot subtree roots remain
the sole cell pre-value and post-value hashes.

The semantic claim binding is an externally derived input to this compatibility
composer. A future guest derives it only after verifying the exact L2 proposal
receipt under its governed L2 image. This host function authenticates no
receipt, image, or claim binding.

The V1 opaque-root and strict full-blob APIs and their exact replay bytes remain
unchanged.

## Independently Replayable V2 Data

`OrdinarySpotSettlementReplayDataV2` has this exact framing:

```text
replay_data_version = 2: u16 big-endian
V5 proposal byte length: u32 big-endian
exact encode_value_aggregate_proposal_v5 bytes
authorization_subject_id: bytes32
authorization_scope_id: bytes32
authorization_nonce: u64 big-endian
authorization_grant_id: bytes32
sparse witness byte length: u32 big-endian
exact encode_sparse_merkle_cell_transition_witness_v1 bytes
settlement plan byte length: u32 big-endian
exact encode_settlement_effect_plan_v2 bytes
```

The complete blob is nonempty and at most 8 MiB. Decoding bounds the outer
input and every declared component before allocating or copying. It exact-
decodes the proposal, authorization, sparse witness, and settlement plan,
calls `derive_spot_settlement_state_projection_v2`, and requires byte-exact
equality with the rederived plan. Stale versions, zero authorization IDs,
truncation, trailing bytes, component oversize, combined oversize,
noncanonical inner bytes, witness substitution, authorization substitution,
proposal substitution, and plan substitution reject.

The stable data-schema identifier is:

```text
H(u16_be(len(domain)), domain)
domain = zenodex.zrpf.ordinary_spot_settlement_replay_data.schema.v2
```

The replay blob contains no DA certificate because certifying bytes that embed
their own certificate is circular. It also contains no transaction payload,
source receipt, receipt verdict, runtime image, or ledger capability.

## Strict Full-Blob Composer

After deriving the state-bound projection, the composer:

1. validates the recomposed plan;
2. requires zero ordinary message, carry, and reward rows in that order;
3. reconstructs and independently revalidates the exact V2 replay blob;
4. validates the full-blob certificate's self-consistency;
5. requires application, chain/domain, epoch, public storage policy, and V2
   replay schema equality with the V5 scope;
6. validates the certificate against the exact replay bytes;
7. derives the proof-tree, schedule, and empty-carry roots;
8. constructs the existing canonical `SettlementEpochCertificateV1`.

The schedule preimage is the existing V1 schedule contract and includes the V5
`conflict_schedule_root`, canonical action order, action IDs, batch commitment,
and validated V2 plan commitment.

The returned certificate maps `pre_state_root` and `post_state_root` from the
validated sparse-ledger action batch and plan. The DA field is the validated
full-blob certificate root. All other field mappings retain the existing V1
certificate contract.

## Future Guest Input

`OrdinarySpotSettlementGuestInputV2` is a proof-neutral exact envelope:

```text
guest_input_version = 2: u16 big-endian
V5 proposal byte length: u32 big-endian
exact canonical V5 proposal bytes
exact fixed authorization fields in replay order
sparse witness byte length: u32 big-endian
exact canonical sparse witness bytes
full-blob certificate byte length: u32 big-endian
exact encode_full_blob_da_certificate_v1 bytes
```

The type has private fields and validated construction. Counts and lengths are
bounded before component allocation. Exact decoding rejects stale versions,
zero authorization IDs, malformed or noncanonical components, truncation,
trailing bytes, and every component or total bound violation.

Construction, self-validation, encoding, and exact decoding share the same
typed authorization validator. The subject, scope, and grant identifier types
also reject zero bytes before a guest input can be constructed through the safe
API.

This envelope contains no `receipt_valid` Boolean, expected or host self image,
semantic claim binding, L2 image ID, settlement guest image ID, receipt bytes,
or verifier metadata. A future settlement guest must verify the L2 receipt
assumption against a compile-time governed image, derive the L2 claim binding
from that verified image and these exact proposal bytes, invoke the strict V2
composer, and commit the canonical settlement certificate. That guest and its
image identity are outside T17.

## Evidence

- independent fixed preimages for replay schema, replay bytes, guest-input
  bytes, schedule root, DA certificate root, and final certificate journal;
- exact replay decode and state-bound plan recomposition;
- exact guest-input round trip and independent manual framing;
- mutation coverage for proposal, all four authorization fields, sparse
  witness identity/path/value/root fields, semantic claim binding, DA scope,
  schema, policy, retention, and content;
- truncation of every prefix, trailing data, stale versions, empty components,
  individual component oversize, and combined bound overflow;
- compile-fail checks for private construction and absence of receipt verdict,
  host self-image, semantic claim binding, and authority accessors;
- confirmation that V1 replay and composer vectors remain unchanged.

The bounded boundary atlas is deterministic offline bug-finding evidence. It is
not a correctness proof.

## Explicit Non-Claims

T17 supplies no RISC0 settlement guest, L2 image pin, receipt verification,
sealed host verifier, runtime identity, semantic-claim authentication, external
storage or retrievability proof, source finality, authorization-grant existence,
durable replay protection, transaction isolation, rollback protection, atomic
ledger admission, payment, settlement authority, release authority, privacy,
throughput, or production authority.

The state-bound certificate remains a proof-neutral compatibility value until
a future guest verifies the exact L2 source and a sealed verifier authenticates
that guest under a governed image. Durable value movement additionally requires
one atomic ledger transaction that applies the independently checked effects
and replay protections.
