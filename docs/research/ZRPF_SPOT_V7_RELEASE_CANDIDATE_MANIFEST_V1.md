# ZRPF Spot V7 Release Candidate Manifest V1

Date: 2026-07-14

Status: exact authority-neutral candidate format implemented

Authority: none

## Claim scope

`SpotV7ReleaseCandidateManifestV1` is the pure identity object that precedes a
future release selector. It binds one proposed bounded Spot V7 release surface
through exact canonical bytes and two domain-separated commitments:

```text
exact candidate body
  -> exact role-ordered evidence inventory
  -> evidence_inventory_root
  -> candidate_id
  -> independently expected candidate-ID check
```

The implementation reads no files and executes no proof, verifier, runtime, or
database operation. A successful check establishes only that the supplied
canonical candidate bytes recompose to the independently expected candidate
ID.

## Bound release surface

The candidate binds these groups:

```text
scope:
  application, chain, domain, release profile,
  proof profile, receipt-security profile

lineage:
  revision, parent candidate, proposed activation and expiration,
  minimum rollback revision, revocation policy, rollback policy,
  explicit absent revocation record

source and build:
  source commit and tree, source closure, complete build-input closure,
  toolchain manifest, build-container manifest

proofs:
  V6 program, image-identity, receipt, journal, and mutation roots
  V7 program, image-identity, receipt, journal, and mutation roots

manifests:
  verifier, authority, and replay manifests

runtime:
  runtime manifest, machine config, artifact set,
  root-supervisor contract and executable,
  Firecracker profile, authority-input profile

policies:
  operational, data-availability, and finality policy roots
```

Every commitment in those groups has exactly one fixed evidence role. The
inventory contains 31 rows in protocol order. Each row has the exact fields
`role`, `codec`, `artifact_sha256`, `bound_identity`, and `size_bytes`.
`artifact_sha256` identifies the exact artifact bytes. `bound_identity`
identifies the semantic root or ID that the role-specific artifact checker
must later derive. Unknown, missing, reordered, duplicated, aliased, wrongly
encoded, empty, or oversized rows reject. The candidate checker requires every
bound commitment to equal its row's `bound_identity`. Fields explicitly named
`*_sha256` additionally require `bound_identity = artifact_sha256`. Semantic
roots and IDs remain separate because they can use domain-separated or
structured derivations. Each role has a fixed size ceiling, and the sum of all
proposed sizes cannot exceed 1 GiB.

This is a proposed content-identity relation. The checker does not read the
named artifacts or establish that their internal claims are true. Every
`size_bytes` value is publisher-proposed metadata in this candidate-only
slice; a later artifact-opening boundary must compare it with the exact bytes
read from a stable descriptor. That boundary must also parse the artifact and
derive its declared `bound_identity`; committing both values does not prove
their relation.

## Canonical format

The document is ASCII JSON with:

- sorted object keys;
- compact separators;
- one trailing newline;
- a 256 KiB byte limit;
- maximum structural depth four;
- exact fields at every object level;
- decoded duplicate-key rejection, including escaped aliases;
- floating-point and non-finite-number rejection;
- exact integer widths and Boolean types;
- fixed `format_flags = 1` and `reserved_u32 = 0`.

The inventory commitment is:

```text
evidence_inventory_root = SHA256(
    u16be(len(inventory_domain))
 || inventory_domain
 || u64be(len(canonical_inventory_bytes))
 || canonical_inventory_bytes
)
```

The candidate commitment uses the same framing over the complete canonical
candidate document excluding `candidate_id` and including the derived
`evidence_inventory_root`:

```text
candidate_id = SHA256(
    u16be(len(candidate_domain))
 || candidate_domain
 || u64be(len(canonical_identity_bytes))
 || canonical_identity_bytes
)
```

An outer consumer must supply the expected candidate ID independently. A
self-consistent document alone does not select a release.

## Lifecycle boundary

Revision one requires an absent parent. Every later revision requires one
nonzero parent candidate ID. Proposed expiration is either absent or strictly
later than proposed activation. The minimum rollback revision cannot exceed the
candidate revision.

V1 requires `revocation_record_root = null`. Revocation is future registry
state and cannot be smuggled into a candidate. The immutable candidate still
binds the revocation and rollback policies that a later selector must enforce.

All of these authority fields are exactly `false`:

```text
candidate_selected
candidate_current
activation_authority
revocation_authority
rollback_authority
source_to_binary_verified
proof_evidence_verified
runtime_execution_verified
release_authority
settlement_authority
production_authority
```

Integer substitution for a Boolean rejects.

## Active distinguishing witnesses

The fixture uses position-distinct, non-palindromic digests, non-palindromic
source identities, distinct chain/domain strings, and asymmetric multi-byte
integers. Its fixed values are:

```text
canonical bytes: 12,472
canonical SHA-256:
  4aef5bb5bbc792b741d3949372c757e6e021bc4feabf50dfa045ebe5f4d58976
candidate ID:
  719db33cbac91d95251592c874a08754530f8210c3504e844af5e1f490cda6ac
candidate-body scalar positions: 220
```

The mutation corpus proves these representation choices are active:

- every candidate-body scalar changes the candidate ID or typed-rejects;
- all 32 `format_flags` bit mutations reject;
- all 32 `reserved_u32` bit mutations reject;
- evidence-row reversal and role swaps reject;
- wrong-role codec and duplicate digest aliasing reject;
- raw artifact SHA-256 and semantic identity positions are independently
  active, and substituting one for the other rejects unless the field is
  explicitly a raw `*_sha256` binding;
- proof-root swaps and multi-byte digest reversals cannot preserve identity;
- absent parent, absent expiration, and absent revocation-record states remain
  distinct;
- derived inventory-root and candidate-ID mutations reject at their own
  boundaries.

This is deterministic mutation evidence. It is not a proof of parser or hash
correctness.

## Disaster-state defenses

| Disaster state | V1 defense |
| --- | --- |
| field omitted or silently defaulted | exact fields and no defaults |
| digest used in the wrong release role | fixed role order plus commitment-to-row binding |
| raw artifact digest confused with a domain-separated semantic root | separate `artifact_sha256` and `bound_identity` fields plus role-specific equality rules |
| V6/V7 receipt or journal identity swapped | distinct role-bound roots and candidate-ID change |
| stale candidate treated as current | all selector/current authority properties are constant false |
| revocation embedded as a caller label | revocation record must be exactly absent |
| rollback lineage omitted | revision, parent, rollback floor, and policy root are committed |
| ambiguous JSON accepted | bounded canonical ASCII decoder with duplicate and float rejection |
| evidence inventory grows without bound | exact 31 rows, per-role ceilings, and checked 1 GiB aggregate ceiling |

## Evidence

Focused replay:

```bash
python3 -m pytest -q \
  tests/test_zrpf_spot_v7_release_candidate_manifest_v1.py

python3 -m mypy --follow-imports=skip \
  tools/zrpf_spot_v7_release_candidate_manifest_v1.py \
  tests/test_zrpf_spot_v7_release_candidate_manifest_v1.py
```

The required `zrpf-assurance` workflow inventories the module and its focused
test in Ruff, mypy, and pytest.

## Non-claims and next boundary

V1 does not establish artifact-byte verification, source-to-binary provenance,
cross-host reproducibility, proof validity, mutation rejection by RISC0, live
runtime execution, DA or finality satisfaction, release selection, activation,
revocation, rollback, settlement, privacy, or production readiness.

The next release layer should consume a checked candidate plus separately
governed selector state. That layer must enforce monotonic revision, exact
parent continuity, activation windows, revocation, rollback policy, and an
external monotonic anchor before it can create a selected-release capability.
