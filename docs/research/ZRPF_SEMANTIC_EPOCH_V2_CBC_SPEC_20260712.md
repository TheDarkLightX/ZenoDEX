# ZRPF Semantic Epoch V2 CBC Specification

Date: 2026-07-12

Status: implemented and host-tested statement ABI; fresh RISC0 proof evidence
pending

## Scoped claim

Semantic Epoch V2 removes the semantic guest runtime image from all untrusted
guest input and proof-neutral proposal bytes. The guest verifies exact L1
receipts under compiled dependency image B, recomposes the bounded semantic
statement, and commits a V2 proposal containing a dependency manifest over
programs A, B, and C. The sealed outer verifier verifies the semantic receipt
under governed runtime image D before decoding the journal. Only that verifier
attaches D, the A/B/C/D program manifest, and the D-plus-journal claim binding.
The verified receipt-security profile remains a separate field on the sealed
type.

This source-level and host-test result does not claim a current V2 receipt,
proof regeneration, durable admission, settlement, release, privacy, or
production authority.

## Disaster state

The V1 guest input carried a nonzero host value named
`expected_self_image_id`. Guest execution could prove a self-consistent journal
whose `actual_program_id` was false. The exact V1 outer verifier rejected the
mismatch, but generic receipt consumers could decode the journal and
misinterpret the host declaration as proof-authenticated program identity.

V2 makes that state unrepresentable in the active statement ABI.

## Authority flow

```text
untrusted V2 bytes with no D
  -> bounded canonical SemanticGuestInputV2
  -> env::verify(B, exact L1 journal bytes)
  -> bind authenticated disclosures
  -> derive semantic leaves and structural root under A/B/C policy
  -> dependency_manifest_root = H(profile, A, B, C, class)
  -> canonical ProposedSemanticEpochV2 with no D
  -> RISC0 receipt
  -> verify receipt cryptographically under governed D
  -> strict V2 proposal decode
  -> require exact governed dependency_manifest_root
  -> derive verified_program_id = D
  -> derive verified_program_manifest_root = H(D, profile, A, B, C, class)
  -> derive claim_binding = H(D, exact journal bytes)
  -> VerifiedSemanticEpochReceiptV2
```

The proof-neutral proposal exposes neither `actual_program_id` nor
`program_manifest_root`. Those accessors exist only on the sealed verified
receipt type as `verified_program_id` and
`verified_program_manifest_root`.

## Canonical objects

### SemanticGuestInputV2

```text
schema_version = 2
level_one_count: u8
for each L1 disclosure:
  exact L1 journal bytes
  leaf_count: u8
  for each leaf:
    exact adapter journal bytes
    semantic opening: bytes32
```

Bounds:

```text
1 <= level_one_count <= 8
1 <= leaves_per_level_one <= 8
0 < journal_bytes <= 4,096
maximum input bytes = 297,115
```

V1 bytes reject under the V2 decoder. V2 bytes reject under the V1 decoder.
There is no compatibility fallback.

### ProposedSemanticEpochV2

```text
proposal_schema_version = 2
semantic_statement_version = 1
scope
semantic_profile_id
partition
leaf_count
operation_count
count_unit_id
proof_tree_root
commitments
semantic_epoch_root
dependency_manifest_root
```

The proposal hash uses domain:

```text
zenodex.zrpf.semantic_epoch_proposal_hash.v2
```

The dependency manifest uses framed domain:

```text
zenodex.zrpf.semantic_epoch_dependency_manifest.v1
```

and commits, in order:

```text
semantic_profile_id
"adapter_program_id"
adapter_program_id A
"level_one_program_id"
level_one_program_id B
"level_two_program_id"
level_two_program_id C
unreleased_semantic_epoch_dependency_manifest
```

The semantic root continues to use the V1 semantic statement domain and
profile. Therefore, for identical canonical semantic leaves and scope:

```text
SemanticRootV2(leaves, scope) = SemanticRootV1(leaves, scope)
```

This equality is a semantic-identity compatibility result. It transfers no
receipt, image, verifier, admission, release, or settlement authority.

## Runtime identity attachment

Let `P` be the exact decoded V2 proposal, `D` the governed semantic guest image,
and `Deps = (A, B, C)`.

```text
VerifyReceipt(receipt, D) = true
P.dependency_manifest_root = DependencyManifest(Deps)
```

are required before constructing:

```text
VerifiedSemanticEpochReceiptV2 {
  verified_program_id = D,
  verified_program_manifest_root = RuntimeManifest(D, Deps),
  claim_binding = ClaimBinding(D, exact(P)),
  receipt_security_profile,
  proposal = P
}
```

No public constructor accepts a proposal, typed receipt, Boolean verification
flag, program ID, or manifest as an authentication capability.

Admission must bind both `receipt_security_profile` and
`verified_program_manifest_root`. The program manifest alone does not commit
the receipt kind, verifier parameters, hash suite, or control ID. A future
single authority-manifest root must commit both surfaces before replacing that
pair.

## Historical V1 migration

V1 artifacts, hashes, and evidence remain unchanged. Their source commit and
retained receipts continue to support their original bounded historical replay
claim. Active code exposes the V1 sealed verifier only through the explicit
`historical_semantic_epoch_v1` namespace.

Fresh V2 promotion requires separate:

- guest and verifier source closures;
- A/B/C/D image identities and ELF hashes;
- positive V2 receipts;
- receipt-authenticated dependency-manifest substitution rejection;
- receipt-authenticated wrong-D and exact proposal substitution rejection;
- exact seal-mutation rejection;
- source-built replay evidence;
- claim and non-claim manifest entries.

## Current source and host-test negatives

- V1 input bytes reject under the V2 decoder.
- V2 input bytes reject under the V1 decoder.
- V1 proposal bytes reject under the V2 decoder.
- V2 proposal bytes reject under the V1 decoder.
- No source reachable from the active V2 guest statement path accepts semantic
  D. Self-bearing V1 codec, binder, and composer modules require the
  `historical-v1` feature, which the V2 guest disables.
- A fake or development receipt cannot enter the sealed V2 type.
- The identity-attachment helper rejects a substituted dependency manifest
  before constructing runtime identity.
- At the identity-attachment helper boundary, changing D changes verified
  program identity and runtime manifest while leaving the proof-neutral
  semantic epoch root independent of D.

These tests establish source-level and host-boundary behavior. They do not
authenticate dependency substitution, wrong D, proposal substitution, or seal
mutation through a real V2 receipt.

## Pending receipt-authenticated negatives

- dependency-manifest substitution after cryptographic receipt verification;
- wrong-D rejection before proposal interpretation;
- exact proposal substitution under the correct D;
- exact Succinct seal mutation of a valid V2 receipt.

All four require fresh real V2 receipt evidence and remain pending.

## Non-claims

- no fresh V2 RISC0 proof or receipt evidence;
- no complete economic action identity or global action nullifier;
- no asset conservation or authorized mint/burn theorem;
- no pre-state to post-state continuity theorem;
- no nonempty receipt, message, carry, schedule, or DA composition;
- no durable atomic ledger admission;
- no proof-generation or cross-host reproducibility;
- no public replay, settlement, release, privacy, throughput, or production
  authority.
