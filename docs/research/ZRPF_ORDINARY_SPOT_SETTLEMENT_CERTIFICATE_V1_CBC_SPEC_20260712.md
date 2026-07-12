# ZRPF Ordinary Spot Settlement Certificate V1 CBC Specification

Date: 2026-07-12

Status: proof-neutral opaque-root composer and strict full-blob replay-data
profile implemented and host-tested; sparse-Merkle-bound Spot projection V2,
authenticated guest, sealed verifier, and authority pending

## Scope

This specification defines one deterministic proof-neutral composer:

```text
compose_ordinary_spot_settlement_certificate_v1(
  exact ProposedValueAggregateV5,
  SpotSettlementAuthorizationInputV1,
  proposed semantic_claim_binding,
  proposed data_availability_certificate_root,
) -> SettlementEpochCertificateV1 | typed reject
```

The composer rederives `SpotSettlementProjectionV1`. It accepts no action
batch, settlement plan, proof-tree root, schedule root, carry-continuity root,
runtime program identity, receipt profile, verifier parameters, receipt, or
ledger capability from the caller.

The opaque-root function remains as a proof-neutral compatibility API. The
strict V1 function is also a compatibility API. It defines the full-blob
content-validation contract that a future guest must preserve. It still uses
raw semantic-subtree state endpoints through `SpotSettlementProjectionV1`, so
it cannot authorize settlement or serve as the settlement guest path. The
authoritative guest path requires the forthcoming sparse-Merkle state-bound
Spot projection V2.

## Canonical replay data

`OrdinarySpotSettlementReplayDataV1` contains exactly two canonical inner byte
strings:

```text
replay_data_version = 1: u16 big-endian
V5 proposal byte length: u32 big-endian
exact encode_value_aggregate_proposal_v5 bytes
SettlementEffectPlanV2 byte length: u32 big-endian
exact encode_settlement_effect_plan_v2 bytes
```

The complete replay blob is nonempty and at most 8 MiB so it fits one
`FullBlobDataAvailabilityCertificateV1`. Decoding bounds the outer bytes and
each declared inner length before copying. It exact-decodes both inner values,
recovers the four authorization fields from the plan's single embedded action,
rederives `SpotSettlementProjectionV1`, and requires byte-exact equality with
the decoded plan. Truncation, trailing bytes, stale versions, inner oversize,
noncanonical inner bytes, action-count drift, and plan substitution reject.

The stable data-schema identifier is:

```text
H(u16_be(len(domain)), domain)
domain = zenodex.zrpf.ordinary_spot_settlement_replay_data.schema.v1
```

This blob contains no transaction payloads and no source receipt artifacts.
The proposal carries transaction roots and child journal/claim commitments;
those commitments do not make their preimages available.

## Strict full-blob composer

```text
compose_ordinary_spot_settlement_certificate_with_full_blob_da_v1(
  exact ProposedValueAggregateV5,
  SpotSettlementAuthorizationInputV1,
  proposed semantic_claim_binding,
  exact FullBlobDataAvailabilityCertificateV1,
) -> SettlementEpochCertificateV1 | typed reject
```

The strict composer rederives the V1 projection and plan, reconstructs the
canonical replay blob, and requires the DA certificate to match, in order:

1. V5 scope application;
2. V5 scope chain/domain;
3. V5 single epoch;
4. V5 public policy as the storage-policy hash;
5. the exact replay-data schema identifier;
6. the exact replay blob through full content validation.

Only then does it place the DA certificate's `certificate_root` into the
settlement certificate. Retention remains governed by the full-blob
certificate constructor. The V5 operational DA roots describe propagated child
commitments and are not relabeled as validation of this replay blob.

## Exact certificate mapping

| Certificate field | Sole source |
| --- | --- |
| application, domain, epoch, pre-state | recomposed action batch |
| semantic profile | exact bytes of the V5 subtree value-profile ID |
| semantic journal hash | recomposed settlement plan source hash |
| semantic claim binding | explicit proof-neutral caller proposal |
| proof-tree root | derived V1 child-structure preimage below |
| semantic root | `ValueSubtree(V5.semantic_subtree.value_subtree_root)` |
| batch commitment and action/replay roots | recomposed action batch |
| plan commitment, post-state, row roots, policy | recomposed settlement plan |
| DA certificate root | opaque path: explicit proof-neutral caller proposal; strict path: exact validated full-blob certificate root |
| schedule certificate root | derived V1 action-order preimage below |
| carry-continuity certificate root | derived V1 empty-root preimage below |
| dependency manifest root | exact V5 proposal dependency manifest root |

The composer requires the projection action batch to equal the plan's embedded
batch and requires the projection source hash to equal the plan source hash.
These guards preserve the association if the projection implementation changes.

## Derived proof-tree root

Domain:

```text
zenodex.zrpf.ordinary_spot_certificate_proof_tree.v1
```

Fixed preimage after the big-endian `u16`-length-framed domain:

```text
V5 proposal_version: u16 big-endian
V5 aggregate_level: u8
V5 child_count: u8
V5 child_descriptors_root: bytes32
V5 child_claims_root: bytes32
V5 child_journals_root: bytes32
```

This root binds the ordered recursive child structure. It is deterministic
data and supplies no receipt verification.

## Derived schedule certificate root

Domain:

```text
zenodex.zrpf.ordinary_spot_schedule_certificate.v1
```

Fixed preimage:

```text
schedule_version = 1: u16 big-endian
V5 propagated conflict_schedule_root: bytes32
ordered_action_count: u16 big-endian
each ordered economic_action_id: bytes32
economic_action_batch_commitment: bytes32
settlement_effect_plan_commitment: bytes32
```

The batch constructor owns canonical action order. The derived root records
the propagated opaque conflict-schedule commitment, that exact action order,
and the exact recomposed batch and plan. It supplies no scheduling execution or
conflict-freedom result.

## Derived empty carry-continuity root

The ordinary Spot profile must have zero message, carry, and reward rows. The
composer rejects the first nonempty collection in message, carry, reward order.

Domain:

```text
zenodex.zrpf.ordinary_spot_empty_carry_continuity.v1
```

Fixed preimage:

```text
carry_profile_version = 1: u16 big-endian
message_count = 0: u16 big-endian
canonical empty messages_root: bytes32
carry_count = 0: u16 big-endian
canonical empty carries_root: bytes32
```

This root records the locally checked empty profile. It supplies no cross-epoch
or cross-domain carry-continuity result.

## Reject precedence

1. V5 self-consistency or ordinary Spot projection failure;
2. recomposed plan self-consistency failure;
3. projection-to-plan batch or source-hash mismatch;
4. nonempty message, carry, then reward rows;
5. derived-root or action-ID failure;
6. semantic-profile type conversion failure;
7. strict path only: replay-data construction or exact recomposition failure;
8. strict path only: full-blob certificate self-consistency, application,
   domain, epoch, storage-policy, schema, then content failure;
9. settlement-certificate construction failure.

The function is pure and performs no I/O or state mutation.

## Required evidence

- exact successful field mapping from the V5 proposal, recomposed batch, and
  recomposed plan;
- independent fixed-preimage vectors for proof-tree, schedule, empty carry,
  and final certificate journal hashes;
- mutation coverage for proposal scope, subtree, child structure,
  authorization, proposed claim binding, and proposed DA root;
- rejects for invalid Spot profile, supply change, and nonempty message, carry,
  or reward counts;
- confirmation that no runtime image, receipt, verifier, or ledger capability
  enters or exits the composer.
- exact replay-data codec and bound checks, stable schema and blob vectors, and
  canonical inner-pair recomposition rejects;
- strict full-blob application, domain, epoch, policy, schema, and content
  mutation rejects;
- confirmation that the DA claim covers replay bytes only, excluding
  transaction payloads and source receipt artifacts.

## Non-claims

The composer supplies no guest execution, receipt verification, source
finality, semantic-claim authentication, schedule validation,
carry-continuity validation, authorization-grant existence, state-tree update,
durable replay protection, ledger admission, payment, settlement authority,
release authority, privacy, throughput, or production claim. The opaque path
does not validate DA. The strict path validates only the canonical replay bytes
against the supplied full-blob certificate and its scoped metadata. It does not
prove external storage, transaction-payload availability, source-receipt
availability, or the authenticity of the V5 operational DA commitments.

Any future settlement guest must enforce the strict full-blob validation
contract after verifying the exact governed V5 source. It must not treat this
V1 composer as authority because V1 uses raw semantic-subtree state endpoints.
The guest must use the sparse-Merkle state-bound Spot projection V2 before a
sealed verifier or atomic admission layer is considered.
