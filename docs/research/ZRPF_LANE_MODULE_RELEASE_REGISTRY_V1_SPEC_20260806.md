# ZRPF Lane Module Release Registry V1

Status: implemented contract candidate; proof-neutral; unmounted; no settlement
or publication authority.

## Purpose

`LaneModuleReleaseRegistryV1` commits the bounded set of module releases known
for one economic lane. It closes the gap between a caller-constructible
`LaneModuleReleaseV1` record and the `module_release_registry_root` already
present in each `GlobalEconomicLaneRegistryV1` row.

The registry is immutable typed data. It can establish internal consistency and
exact root equality. A future profile verifier must still establish that this
root is the governed root for the current authority epoch.

## ShapeForge Boundary

```text
S = lane_module_release_registry_v1
A = guard
T = contract_strengthening
V = {
  registry_version,
  lane_id,
  ordered_release_records,
  predecessor_edges,
  active_new_count,
  registry_root
}
O = {
  construct,
  canonical_root,
  resolve_new_object_release,
  resolve_existing_object_release,
  bind_global_lane_entry,
  exact_codec
}
G = {
  bounded_nonempty_set,
  one_lane,
  unique_sorted_release_ids,
  reachable_acyclic_predecessors,
  at_most_one_active_new,
  exact_lane_row_root
}
N = {
  empty_or_oversized_set,
  mixed_lane,
  duplicate_or_reordered_release,
  orphan_or_cyclic_predecessor,
  multiple_active_new,
  wrong_lane_row_or_root,
  stale_or_noncanonical_wire
}
Gap = {
  governance_history,
  profile_authority_witness,
  migration_certificate,
  route_authority,
  module_transition_proof,
  atomic_publisher
}
```

The promoted ShapeForge seed remains unchanged because this checkout has no
recorded regeneration command for that artifact family. This document is the
reviewable bounded delta.

## Stable Contract

```text
LANE_MODULE_RELEASE_REGISTRY_VERSION_V1 = 1
MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1 = 64
MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1 = 131200

LaneModuleReleaseRegistryV1 {
  registry_version: u16,
  lane_id: EconomicLaneIdV1,
  releases: Vec<LaneModuleReleaseV1>
}
```

The release set must contain between 1 and 64 records. Every record must name
the registry lane. Release IDs are unique and strictly increasing in their
typed byte order. Canonical construction rejects permutations instead of
sorting caller input.

At most one record may have status `ActiveNew`. Zero is valid for a disabled,
shadow-only, or draining lane. Each non-genesis migration predecessor must be
present in the same registry. The bounded predecessor graph must terminate and
must not cycle. Multiple genesis records are representable because V1 does not
invent a release-family or asset-namespace policy.

Validation order is stable:

1. registry version;
2. count bound;
3. lane equality;
4. duplicate identity;
5. canonical identity order;
6. `ActiveNew` cardinality;
7. predecessor presence;
8. predecessor-cycle exclusion.

All rejection paths leave the supplied release records unchanged.

## Canonical Root

```text
SHA256(
  u16_be(len("zenodex.global_settlement.lane_module_release_registry.v1")) ||
  "zenodex.global_settlement.lane_module_release_registry.v1" ||
  u16_be(registry_version) ||
  lane_code ||
  u16_be(release_count) ||
  concat(release.canonical_record_commitment())
)
```

The release record commitment binds both content-derived release ID and current
lifecycle status. A status transition therefore preserves the release ID and
changes the registry root.

For the two-release Spot fixture in the executable evidence, the fixed root is:

```text
73f1c33fa26c0b108b9eaea69023f17cf8f2e147ce2b85276c1027ba0a58a9aa
```

`bind_global_lane_entry` requires exact lane identity and exact equality between
this root and `EconomicLaneRegistryEntryV1.module_release_registry_root`.
`EconomicLaneCommandStatusV1` remains the independent global lane admission
guard; root binding does not override or reinterpret it.

## Resolution

`resolve_new_object_release` returns the unique `ActiveNew` record and applies
its existing release-level new-object admission check. Absence rejects.

`resolve_existing_object_release` resolves the exact creating release ID and
applies its existing-object admission check. Only `ActiveNew` and `DrainOnly`
can pass. Unknown, retired, verify-only, revoked, candidate, and shadow records
reject with typed errors.

Both methods return references into immutable registry data. Neither creates an
authority witness.

## Exact Codec

The canonical encoding is bounded Postcard. Decode rejects before authority is
exposed on:

- empty or maximum-plus-one input;
- stale registry version;
- release count above 64;
- malformed or counterfeit nested release records;
- unknown enum discriminants;
- mixed lanes, duplicate IDs, noncanonical order, excess `ActiveNew` records,
  orphan predecessors, or predecessor cycles;
- trailing bytes or a byte sequence that does not exactly re-encode.

The fixed SHA-256 digest of the canonical two-release Postcard fixture is:

```text
7ed91130146db720c18b7613f29135376e32f06511308c1bded99a52fc14a375
```

## Evidence

The Rust tests cover:

- BVA at 0, 1, 64, and 65 release records;
- same-lane, duplicate-ID, and exact-order mutations;
- every permutation of a three-record set, with exactly one accepted;
- 0, 1, and 2 `ActiveNew` records;
- connected and orphan predecessor cases;
- new-object and existing-object resolution with reject-is-no-op;
- an independent root mirror, fixed root, correct row binding, wrong lane, and
  wrong root;
- lifecycle-status root separation;
- canonical round trip, fixed digest, stale version, trailing, empty,
  maximum-plus-one, and reordered wire input;
- parity with all existing `LaneModuleReleaseV1` tests after nested validated
  deserialization was added.

## Negative Knowledge

This registry does not prove lifecycle transition history, governance approval,
release equivalence, coexistence economics, migration correctness, terminal
execution, resource consumption, guest semantics, receipt validity, route
selection, profile activation, no-bypass, or atomic ZenoLedger publication.

A matching `EconomicLaneRegistryEntryV1` is still ordinary caller-constructible
typed data. It becomes authoritative only after a future release-aware profile
verifier checks the governed profile root and constructs an opaque witness.

## Next Safe Slice

Define bounded `RouteReleaseV1` content identity for exact ordered module
dependencies, dependency roles, port schemas, Oracle policy, issue/burn policy,
and resource ceilings. Route selection must remain governed data and must not be
caller-selected or settlement-authoritative until profile verification exists.
