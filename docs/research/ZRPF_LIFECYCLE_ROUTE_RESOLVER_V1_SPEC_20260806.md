# ZRPF Lifecycle Route Resolver V1

Status: implemented and tested structural contract; research-only, unmounted,
and without proof-verification, settlement, or publication authority.

Date: 2026-08-06

## Purpose

An `EconomicCommandOccurrenceV1` carries a route release ID so its replay
identity is complete. The active-profile binder previously accepted any known
route whose command variant matched. State-authenticated object release pins
were checked only after that route had already been selected.

The V1 lifecycle resolver removes the proposed route from the authority
decision. Each route dependency now commits one closed selection purpose:

```text
ActiveNewRelease
PinnedExistingObjects
```

The state binder independently derives the unique matching route from the
command variant, the profile-committed route and module registries, and every
authenticated consumed-object release pin. It then compares that derived route
with the occurrence's proposed route. A mismatch rejects without constructing
`StateBoundEconomicCommandOccurrenceV1`.

## ShapeForge model

```text
Phi := <
  M = zenodex_lifecycle_route_resolver_v1,
  S = one_profile_state_bound_command,
  A = guard,
  T = remove_proposed_route_authority,
  V = command_variant, route_dependency_purposes, module_release_statuses,
      state_authenticated_object_release_pins,
  O = validate_pins, derive_unique_route, compare_proposed_route,
  G = exact_pin_coverage, one_release_per_pinned_lane,
      ActiveNew_release_admission, existing_release_admission,
      unique_matching_route,
  Obs = StateBoundEconomicCommandOccurrenceV1_or_typed_reject,
  K = profile_id, writer_epoch, pre_state_root, command_variant,
      canonical_consumed_objects,
  E = AAA_regressions, lifecycle_BVA, paired_sparse_Merkle_membership,
      identity_and_codec_vectors, mutation_killing_negatives,
  Gap = guest_enforcement_of_declared_lifecycle_semantics,
        same_lane_cross_release_coordination, global_effect_plan,
        conservation_checker, recursive_guests, release_aware_epoch_verifier,
        atomic_publisher,
  N = caller_selected_drain_route, unpinned_drain_route,
      conflicting_same_lane_release_pins, ambiguous_active_routes,
      purpose_status_mismatch,
  Delta = proposed_route_is_replay_data_and_only_the_derived_route_can_bind
>
```

Strongest evidence class: `contract`.

## Functional-core contract

```text
profile-bound occurrence
+ profile-bound global state
+ exact object-release openings
  -> typed reject
   | state-bound occurrence whose proposed route equals the derived route
```

The resolver is deterministic and performs no I/O. It allocates no unbounded
collection. It scans the profile-bounded route registry and uses fixed
twelve-lane arrays for pin coverage.

For each route dependency:

- `ActiveNewRelease` requires the dependency release to equal the lane
  registry's sole `ACTIVE_NEW` release. Zero pinned objects are allowed. Every
  pinned object in that lane must have been created by the same active release.
- `PinnedExistingObjects` requires at least one authenticated consumed object
  in that lane. All such objects must pin the dependency's exact release, which
  must admit existing-object transitions.

Every authenticated pin lane must occur in the selected route. Zero matching
routes and multiple matching routes are separate typed rejections. A command
cannot combine objects from two creating releases in one lane under this V1
shape.

## Identity and pre-release compatibility

`RouteDependencyLifecyclePurposeV1` is inserted into each dependency's route
identity immediately after `module_release_id`:

```text
lane_code || module_release_id || lifecycle_purpose_code || role_mask || ...
```

This intentional pre-release V1 contract strengthening changes route release
IDs, route registry roots, profile IDs that bind those roots, and command
occurrence IDs that bind routes. Earlier uncommitted V1 values cannot be mixed
with this candidate. No mounted production profile or settlement authority is
migrated by this patch.

The fixed two-dependency fixture now has:

```text
route_release_id = 9a25ec0269e0fde35c4d89d4c38648b1ee29feb381f290afa280e9bcd2351207
sha256(canonical_postcard) = 2e293076bf0822ce7d43c0b2a4762e743e35891c8c390dff4a7eb198eaa362cb
```

## Preflight and pattern record

- Authority owned: structural module-release and route selection only.
- Authority excluded: command authentication, economic effects, proof
  verification, current-head checks, and publication.
- Trusted constructors: exact route/profile/state constructors followed by
  `bind_profile_bound_occurrence_to_global_state_v1`.
- Ownership: route and state values are immutable owned data; binding witnesses
  borrow exact inputs and are private and non-serializable.
- Staleness: profile ID, writer epoch, route registry root, and pre-state root
  are checked before route derivation.
- Replay: the occurrence continues to commit the proposed route; successful
  binding establishes equality with the independently derived route.
- Rejection: no witness, candidate state, effects, receipt, replay update, or
  outbox value is returned.
- Complexity: route scan is bounded by 256 routes, each with at most eight
  dependencies and twelve fixed lane positions.
- Migration: this changes pre-release canonical route identities; historical
  proof verification and activated profile migration remain future contracts.

## Executable evidence

The tests use explicit Arrange, Act, and Assert phases and cover:

- zero consumed objects selecting the active-new route;
- one active-release object remaining on the active route;
- one old-release object selecting the exact drain route;
- caller substitution in both directions;
- a drain-only route with zero pins producing no match;
- two active routes for one command producing ambiguity;
- two valid same-root sparse-Merkle openings with conflicting same-lane
  releases rejecting before route selection;
- active-new purpose paired with a drain-only release rejecting at profile
  binding;
- lifecycle-purpose identity separation and unknown discriminant rejection;
- all updated route, registry, profile, and occurrence fixed vectors.

## Nonclaims

- A route lifecycle purpose is governed metadata. Module and composition guests
  must enforce that the command semantics and effects satisfy it.
- V1 cannot represent one command that requires two module releases from the
  same lane. A lane coordinator or new route shape is required.
- This resolver does not prove conservation, custody, liability, terminal
  drain, migration continuity, proof receipt validity, or current consensus
  head.
- No Python/Tau/Lean/Kani refinement, RISC0 guest, verified epoch, ZenoLedger
  commit, API mount, RC, production-readiness, or whole-economy settlement
  claim is added.

## Next proof-worthy gap

Define `GlobalEconomicEffectPlanV1` and its complete per-asset conservation,
custody, liability, fee-allocation, replay, terminal-obligation, and outbox
checks. The plan must bind this derived route and remain ordinary data until a
module/route proof and release-aware epoch verifier authenticate it.
