# ZRPF Ordinary Spot Settlement Certificate V1 CBC Specification

Date: 2026-07-12

Status: proof-neutral composer implemented and host-tested; authenticated guest,
sealed receipt verifier, and ledger authority pending

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
| DA certificate root | explicit proof-neutral caller proposal |
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
ordered_action_count: u16 big-endian
each ordered economic_action_id: bytes32
economic_action_batch_commitment: bytes32
settlement_effect_plan_commitment: bytes32
```

The batch constructor owns canonical action order. The derived root records
that exact order and the exact recomposed batch and plan. It supplies no
scheduling execution or conflict-freedom result.

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
7. settlement-certificate construction failure.

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

## Non-claims

The composer supplies no guest execution, receipt verification, source
finality, semantic-claim authentication, DA validation, schedule validation,
carry-continuity validation, authorization-grant existence, state-tree update,
durable replay protection, ledger admission, payment, settlement authority,
release authority, privacy, throughput, or production claim.

The future settlement guest must run this same recomposition after verifying
the exact governed V5 receipt. A sealed host verifier must then authenticate
the settlement receipt and attach runtime identity before ledger admission is
considered.
