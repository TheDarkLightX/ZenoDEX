# ZRPF Economic Profile Snapshot V1

Status: implemented contract candidate; proof-neutral; unmounted; no verifier,
settlement, migration, activation, or publication authority.

## Purpose

`EconomicProfileSnapshotV1` commits one authority epoch and writer epoch to the
exact economic lane, route release, proof-shape, verifier, migration, policy,
and terminal registry roots selected for that epoch. It also binds the complete
closed economic-lane registry to twelve canonically ordered per-lane module
release registries and checks the executable route dependencies and primary
route coverage visible in those registries.

The snapshot is immutable ordinary data. A future release-aware verifier must
authenticate an active snapshot and construct an opaque
`VerifiedEconomicEpochV1` before any ledger publisher may rely on it.

## ShapeForge Working Model

```text
Phi = <M, S, A, T, V, O, G, Obs, K, E, Gap, N, Delta>

M = zenodex_economic_profile_snapshot_v1
S = governed_whole_economy_registry_selection
A = guard
T = contract_strengthening
V = {
  profile_version,
  authority_epoch,
  writer_epoch,
  transition_mode,
  predecessor_profile_id,
  economic_lane_registry_root,
  route_release_registry_root,
  proof_shape_registry_root,
  verifier_registry_root,
  migration_registry_root,
  policy_registry_root,
  terminal_registry_root
}
O = {
  construct_snapshot,
  validate_successor,
  bind_economic_registries,
  derive_profile_id,
  exact_codec
}
G = {
  nonzero_content_derived_profile_id,
  exact_transition_predecessor_cardinality,
  strict_authority_epoch_increase,
  strict_writer_epoch_rotation,
  exact_lane_and_route_registry_roots,
  exactly_twelve_canonical_lane_module_registries,
  exact_lane_module_registry_roots,
  exact_route_dependency_release_occurrence,
  lifecycle_purpose_specific_dependency_status,
  enabled_lane_has_primary_route,
  disabled_lane_has_no_primary_route,
  canonical_bounded_encoding
}
Obs = {
  profile_id,
  exact_registry_binding_success_or_typed_reject,
  exact_successor_validation_success_or_typed_reject
}
K = (
  authority_epoch,
  writer_epoch,
  transition_mode,
  predecessor_profile_id,
  ordered_registry_roots
)
E = {
  contract: typed constructors and fail_closed_decode,
  implemented: deterministic Rust core,
  tested_discovery: AAA, BVA, BVE, SETBVE_informed_boundaries, mutation,
                    fixed_vectors, reject_is_noop
}
Gap = {
  authenticated_profile_activation,
  guest_enforcement_of_lifecycle_purpose,
  proof_shape_registry_implementation_and_binding,
  verifier_registry_implementation_and_binding,
  migration_registry_and_certificate_verification,
  policy_and_terminal_registry_implementation_and_binding,
  authenticated_command_occurrence,
  module_and_route_receipts,
  recursive_epoch_composer,
  release_aware_verifier,
  atomic_zenoledger_publisher
}
N = {
  profile_bytes_are_not_an_authority_witness,
  proved_migration_mode_does_not_verify_a_migration_certificate,
  lifecycle_metadata_does_not_prove_guest_semantics,
  committed_unimplemented_registry_roots_are_not_registry_validation,
  route_coverage_is_not_complete_M6_workflow_coverage
}
Delta = one bounded content_addressed whole_economy_registry_snapshot_guard
```

The promoted ShapeForge seed in this candidate has no ZRPF profile slice, and
the coordinated bundle artifacts named by the local ShapeForge workflow are
absent. This document records the bounded working model without claiming a
promoted ShapeForge-bundle update.

## Stable Contract

```text
ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1 = 1
MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1 = 512

EconomicProfileTransitionModeV1 = {
  Genesis,
  GovernanceUpdate,
  ProvedMigration
}

EconomicProfileRegistryRootsV1 {
  economic_lane_registry_root: CommitmentV3,
  route_release_registry_root: CommitmentV3,
  proof_shape_registry_root: CommitmentV3,
  verifier_registry_root: CommitmentV3,
  migration_registry_root: CommitmentV3,
  policy_registry_root: CommitmentV3,
  terminal_registry_root: CommitmentV3
}

EconomicProfileSnapshotContentV1 {
  authority_epoch: u64,
  writer_epoch: u64,
  transition_mode: EconomicProfileTransitionModeV1,
  predecessor_profile_id: Option<EconomicProfileIdV1>,
  registry_roots: EconomicProfileRegistryRootsV1
}

EconomicProfileSnapshotV1 {
  profile_version: u16,
  profile_id: EconomicProfileIdV1,
  content: EconomicProfileSnapshotContentV1
}
```

Every `CommitmentV3` and `EconomicProfileIdV1` is nonzero by construction.
Genesis requires no predecessor. Governance updates and proved migrations
require exactly one predecessor identity.

## Profile Identity

The profile ID is:

```text
SHA256(
  u16_be(len("zenodex.global_settlement.economic_profile_snapshot_id.v1")) ||
  "zenodex.global_settlement.economic_profile_snapshot_id.v1" ||
  u16_be(profile_version) ||
  u64_be(authority_epoch) ||
  u64_be(writer_epoch) ||
  u8(transition_mode) ||
  u8(predecessor_presence) ||
  predecessor_profile_id_if_present ||
  economic_lane_registry_root ||
  route_release_registry_root ||
  proof_shape_registry_root ||
  verifier_registry_root ||
  migration_registry_root ||
  policy_registry_root ||
  terminal_registry_root
)
```

Changing either epoch, transition mode, predecessor, or any one registry root
changes the identity. The fixed test profile ID is:

```text
c856e3c1e624a53f4ad0d6cb54e11abf179940632348050296f6ed0c876a7628
```

## Successor And Registry Binding

`validate_successor_of` rejects genesis as a successor, a predecessor mismatch,
and an authority or writer epoch that is equal to or below the previous value.
It checks ordered profile continuity only. Governance authentication and
migration proof verification remain external obligations.

`bind_economic_registries` applies these checks in deterministic order:

1. Recompute and match the exact economic-lane registry root.
2. Recompute and match the exact route-release registry root.
3. Require exactly twelve module registries in `EconomicLaneIdV1::ALL` order.
4. Bind each module registry to the exact root in its lane-registry entry.
5. Require every route dependency release to occur in its lane registry.
6. Require `ActiveNewRelease` dependencies to admit new-object creation and
   `PinnedExistingObjects` dependencies to admit existing-object transitions.
7. Require each enabled lane to own at least one primary route and each disabled
   lane to own none.

The lifecycle purpose is content-bound through the route registry root. The
state-bound lifecycle resolver independently derives a unique route from that
purpose and authenticated object pins. Module guests must still enforce that
the command semantics and effects satisfy the declared purpose.

The proof-shape, verifier, migration, policy, and terminal commitments are
identity-bound roots. Their concrete registry types and exact binding functions
remain future work. Supplying those roots does not validate their contents.

## Exact Codec

The canonical wire encoding is bounded Postcard. Decode rejects empty and
larger-than-512-byte input before allocation, stale versions, counterfeit
profile IDs, malformed or nonminimal integers, trailing bytes, and any input
that does not exactly re-encode. Serde object decoding rejects unknown fields at
the profile, content, and registry-root levels.

The SHA-256 digest of the fixed canonical Postcard fixture is:

```text
8ec33e007c885c7964a0bc729d646331901d110d6bad0b9183e3c4445e7843bf
```

## Required Evidence

The executable Rust contract contains fifteen invariant-named tests with
explicit Arrange, Act, and Assert phases where applicable. The boundary set
combines specification BVA with deterministic behavioral exploration:

- predecessor cardinality for all three transition modes;
- authority and writer epoch values at `0`, `1`, and `u64::MAX`;
- lower, equal, and upper successor-epoch neighbors;
- module-registry cardinality at `11`, `12`, and `13`;
- all seven module release statuses;
- enabled and disabled lane primary-route partitions;
- exact dependency occurrence and one-defect unknown-release mutation;
- mutation of each committed registry root;
- empty, maximum-plus-one, stale, counterfeit, nonminimal, trailing, and
  unknown-field codec cases;
- fixed profile-ID and encoded-byte digest vectors;
- immutable reject-is-no-op observations.

Boundary Value Exploration and SETBVE inform candidate boundary discovery. The
normative contract and deterministic local tests decide what enters this
evidence slice; exploratory output has no authority.

## Negative Knowledge And Nonclaims

This profile does not authenticate governance, verify any RISC0 receipt, bind a
proof image to a journal, prove module or route execution, authenticate an
occurrence or replay key, prove lifecycle-purpose semantics, verify a migration
certificate, or construct `VerifiedEconomicEpochV1`.

It does not mount ZenoLedger, publish an atomic transition, establish global
custody or conservation, prove complete terminal obligations, cover the 81 M6
scenarios, close inherited dependency advisories, or establish RC or production
readiness.

## Shape Delta And Next Target

The new guard gives one content-derived identity to the exact registry roots,
lane-module release view, route dependency lifecycle admission, lane coverage,
and writer/authority epoch continuity of a candidate economic profile.

The next contract target is `EconomicCommandOccurrenceV1`. It must bind a
canonical `(height, tx_index, op_index)`, authenticated subject and grant,
nonce/replay scope, exact profile, pre-root, route, lifecycle purpose, and
consumed objects. That occurrence will still remain ordinary data until a
release-aware verifier checks the proof graph and constructs an opaque authority
witness.
