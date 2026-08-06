# ZRPF Route Release Registry V1

Status: implemented contract candidate; proof-neutral; unmounted;
no profile, route-execution, settlement, or publication authority.

## Purpose

`RouteReleaseRegistryV1` is the bounded deterministic lookup contract between
an economic command variant plus its state-derived module release set and one
exact `RouteReleaseV1`. It prevents fallback routing, ambiguous route choice,
and iteration-order selection inside a candidate registry.

The selector and registry are immutable typed data. A future
`EconomicProfileSnapshotV1` and authenticated command-occurrence builder must
derive the selector from governed profile state, the authenticated command,
and persistent object release pins. Supplying a selector to this contract does
not authenticate those facts or construct an authority witness.

## ShapeForge Working Model

```text
Phi = <M, S, A, T, V, O, G, Obs, K, E, Gap, N, Delta>

M = zenodex_zrpf_route_registry_v1
S = governed_command_to_route_selection
A = guard
T = contract_strengthening
V = {
  registry_version,
  ordered_route_releases,
  command_variant_root,
  canonical_module_release_selection
}
O = {
  construct_registry,
  derive_selection_from_route,
  resolve_exact,
  bind_exact_module_registry_union,
  derive_registry_root,
  exact_codec
}
G = {
  one_to_256_routes,
  one_to_eight_selection_dependencies,
  unique_selection_lanes,
  lane_sorted_selection,
  unique_route_release_ids,
  unique_selection_keys,
  selection_key_sorted_routes,
  exact_module_registry_union,
  exact_dependency_release_occurrence,
  canonical_bounded_encoding
}
Obs = {
  canonical_registry_root,
  exact_selected_route_or_typed_reject
}
K = (
  command_variant_root,
  lane_sorted_list(lane_id, module_release_id)
)
E = {
  contract: typed constructors and fail_closed_decode,
  implemented: deterministic Rust core,
  tested_discovery: AAA, BVA_SETBVE, mutation, and fixed vectors
}
Gap = {
  governed_profile_snapshot,
  authenticated_selector_derivation,
  route_lifecycle_activation,
  occurrence_and_replay_binding,
  actual_module_receipts_and_ports,
  recursive_composer,
  release_aware_verifier,
  migration_certificate,
  atomic_publisher
}
N = {
  caller_selected_route_has_no_authority,
  no_default_or_fallback_route,
  duplicate_selection_is_ambiguous_and_rejected,
  iteration_order_is_not_route_policy,
  module_release_occurrence_does_not_prove_lifecycle_admission
}
Delta = one bounded canonical fail_closed command_and_release_set selector
```

The existing promoted ShapeForge seed has no ZRPF release/profile slice, and
the other coordinated ShapeForge artifacts referenced by the local skill are
absent from this candidate. This specification records the bounded working
model without claiming a promoted ShapeForge-bundle update.

## Stable Contract

```text
ROUTE_RELEASE_REGISTRY_VERSION_V1 = 1
MAX_ROUTE_RELEASES_PER_REGISTRY_V1 = 256
MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1 =
  256 * MAX_ROUTE_RELEASE_BYTES_V1 + 64

RouteModuleReleaseSelectionV1 {
  lane_id: EconomicLaneIdV1,
  module_release_id: LaneModuleReleaseIdV1
}

RouteSelectionKeyV1 {
  command_variant_root: CommitmentV3,
  module_releases: Vec<RouteModuleReleaseSelectionV1>
}

RouteReleaseRegistryV1 {
  registry_version: u16,
  routes: Vec<RouteReleaseV1>
}
```

The route count bound is a V1 allocation and denial-of-service ceiling. It is
not evidence that 256 routes are sufficient for the final M6 profile. Raising
or reinterpreting the bound requires a new registry contract and evidence.

## Selection Semantics

The selection key contains:

1. the exact command-variant root;
2. one to eight `(lane_id, module_release_id)` pairs;
3. pairs in ascending `EconomicLaneIdV1` order;
4. at most one pair for each lane.

`RouteSelectionKeyV1::from_route` derives this key from a validated route. It
sorts only the selector's lane/release facts. It does not reorder the route's
semantic dependency sequence. The selected `RouteReleaseV1` continues to own
the ordered composition plan.

Two routes in one registry may not share a selection key. Therefore, the same
command variant and module release set cannot ambiguously select two role,
schema, policy, port-pairing, resource, or dependency-order variants. A profile
that intends different semantics must commit a distinct command variant or a
different registry snapshot.

`resolve` returns the exact route or `UnknownRouteSelection`. It has no default,
nearest-match, lifecycle inference, or fallback behavior.

## Canonical Registry Order And Root

Routes are stored in ascending `RouteSelectionKeyV1` order. Duplicate route
release IDs, duplicate selection keys, and any other permutation reject.

The canonical root is:

```text
SHA256(
  u16_be(len("zenodex.global_settlement.route_release_registry.v1")) ||
  "zenodex.global_settlement.route_release_registry.v1" ||
  u16_be(registry_version) ||
  u16_be(route_count) ||
  concat(route_release_id)
)
```

Each route release ID is itself content-derived over the complete route
contract. The registry root therefore binds the exact ordered route records
through their content identities.

The fixed two-route registry root is:

```text
e5747633f19f5c1806dc51106119e6fc8a67a7337dccfd92be24f74ab132c190
```

The SHA-256 digest of that registry's canonical Postcard encoding is:

```text
1daec76c0cc00c1bd466298e13db61d929f95e69bd5fbc92d4fe75c77c54de79
```

## Exact Module Registry Union Binding

`bind_module_release_registries` derives the sorted union of every lane used by
every registered route. The supplied lane module registries must match that
union exactly in count and lane order. Every route dependency's exact module
release ID must occur in the corresponding lane registry.

This binding is independent of route composition order. It permits a route to
compose lanes in semantic order while the registry-union input remains
canonical by lane ID.

The binding checks record occurrence only. It does not interpret Candidate,
Shadow, ActiveNew, DrainOnly, VerifyOnly, Retired, or Revoked status. A future
profile resolver must enforce route purpose, object pinning, coexistence, and
release lifecycle admission.

## Exact Codec

The canonical encoding is bounded Postcard. Decode rejects empty and oversized
input before allocation, bounds the route vector while decoding, reconstructs
the validated registry, rejects trailing bytes, and requires exact re-encoding.

Stale versions, route counts above 256, nonminimal integer encodings,
noncanonical route order, ambiguous selection, and malformed nested route
records reject. Serde struct decoding rejects unknown fields at the registry,
selection, and selection-entry layers. Authority consumers must use the exact
bounded decoder for registry bytes.

## Invariants And Invalid-State Closure

Constructor-time invariants:

- registry route count is in `[1, 256]`;
- selection dependency count is in `[1, 8]`;
- selector lanes are unique and strictly ascending;
- route IDs are unique;
- route selection keys are unique and strictly ascending.

Boundary-only invariants:

- wire input is nonempty and bounded;
- Postcard bytes are exact and canonical;
- the supplied module registry list is the exact sorted required-lane union;
- every route dependency release occurs in its lane registry.

Compile-time structure:

- lane and release identities use closed typed values;
- selector entries contain no role, policy, schema, or composition-order field;
- route semantics remain owned by `RouteReleaseV1`.

Rejected construction and lookup do not mutate caller-owned selector, route,
or registry values.

## Required Evidence

The executable contract includes:

- registry BVA at `0`, `1`, `256`, and `257` routes;
- selector BVA at `0`, `1`, `8`, and `9` module releases;
- duplicate and reversed selector lanes;
- exact success plus unknown command and unknown release rejection;
- duplicate route ID and ambiguous selector rejection;
- all six permutations of a three-route registry, with exactly one accepted;
- exact module-registry union binding at `N-1`, `N`, and `N+1`, reordered and
  duplicate lanes, unknown release, and composition-order independence;
- fixed registry root and encoded digest;
- empty, maximum-plus-one byte, stale, nonminimal, trailing, reordered, and
  over-count wire rejection;
- unknown registry, selector, and selector-entry fields;
- reject-is-no-op checks.

## Negative Knowledge And Nonclaims

The selector is caller-constructible plain data. This contract does not derive
it from authenticated commands or committed objects, authenticate a profile,
select ActiveNew versus DrainOnly purpose, verify a receipt, consume a nonce or
object, pair private ports, compose proofs, migrate state, or publish a ledger
transition.

The registry root is an input to future governance and profile contracts. Its
existence does not establish governance history, activation, complete M6 route
coverage, production readiness, or whole-economy settlement authority.

## Shape Delta And Next Target

The new shape eliminates ambiguous duplicate selectors, implicit fallback, and
iteration-order route choice inside one candidate registry. Command identity,
module-release coexistence facts, and composition order are now separated
explicitly.

The next contract target is `EconomicProfileSnapshotV1`: it must bind this
route-registry root with the exact lane, module, proof-shape, verifier,
migration, policy, terminal, writer-epoch, and activation state needed to make
route selection governance-aware. Even that snapshot remains data until a
release-aware verifier constructs an opaque authority witness.
