# ZRPF Lane Module Release V1

Date: 2026-08-06
Status: `CONTRACT_IMPLEMENTED`, unmounted and without proof or settlement authority

## Scope

This slice defines the proof-system-neutral content identity and lifecycle
contract for one economic lane module release. A release binds its exact lane,
schemas, command variants, guest image, source/spec/toolchain provenance,
terminal coverage, migration compatibility, and resource ceilings. The release
ID is derived from those fields. Callers cannot supply a different ID for the
same content.

Lifecycle status is excluded from content identity so one immutable release may
advance through governance states without changing its implementation identity.
The status is included in the canonical release-record commitment.

This contract lives in `zenodex-zrpf-protocol-v3`. It contains no verifier,
registry activation, route selection, module transition, proof guest, or ledger
publisher.

## ShapeForge Delta

```text
Phi := <
  M = zenodex_shape_reference_v3,
  S = lane_module_release_v1,
  A = guard,
  T = contract_strengthening,
  V = {content_roots, resource_limits, migration_mode, terminal_status, lifecycle_status},
  O = {derive_release_id, transition_status, admit_new, admit_drain, exact_codec},
  G = {content_identity, closed_transition_graph, terminal_complete_activation, bounded_resources},
  Obs = {typed_release_or_stable_reject, release_id, record_commitment},
  K = none,
  E = {contract, boundary, property, mutation_negative},
  Gap = {release_set_root, routes, module_transition, proof_guest, publisher, migration_certificate},
  N = {caller_selected_id, lifecycle_skip, incomplete_activation, zero_resource, stale_or_noncanonical_wire},
  Delta = {content_derived_lane_release_identity_and_fail_closed_lifecycle}
>
```

The perturbed axis is release admission. Economic policy, transition semantics,
proof recursion, profile activation, and publication remain unchanged.

## Content Contract

`LaneModuleReleaseContentV1` contains:

```text
lane_id
state_schema_root
command_schema_root
effect_schema_root
private_port_schema_root
command_variants_root
guest_image_id
spec_root
source_root
toolchain_root
terminal_coverage_status
terminal_coverage_root
migration_mode
predecessor_release_id?
migration_compatibility_root
max_command_bytes
max_state_bytes
max_journal_bytes
max_cycles
```

All roots and the guest image ID use nonzero typed 32-byte values. Every
resource ceiling is explicit and nonzero. V1 accepts values through the integer
type maxima; later route and profile contracts must impose release-specific
operational budgets and verify actual usage against these ceilings. Decoded
release content exposes the four ceilings through immutable read-only getters
so those consumers can perform the comparison.

Migration mode and predecessor cardinality are exact:

| Migration mode | Predecessor |
| --- | --- |
| `Genesis` | absent |
| `CoexistAndDrain` | exactly one nonzero release ID |
| `ProvedBulkMigration` | exactly one nonzero release ID |

The compatibility root is committed evidence metadata. This slice does not
verify a coexistence theorem or migration certificate.

## Content-Derived Identity

The release ID is:

```text
SHA256(
  u16_be(len("zenodex.global_settlement.lane_module_release_id.v1")) ||
  "zenodex.global_settlement.lane_module_release_id.v1" ||
  u16_be(release_version) ||
  lane_code ||
  schema_roots ||
  command_variants_root ||
  guest_image_id || spec_root || source_root || toolchain_root ||
  terminal_status_code || terminal_coverage_root ||
  migration_mode_code || predecessor_presence || predecessor_if_present ||
  migration_compatibility_root ||
  u32_be(max_command_bytes) ||
  u32_be(max_state_bytes) ||
  u32_be(max_journal_bytes) ||
  u64_be(max_cycles)
)
```

Lifecycle status is deliberately absent. The release-record commitment binds
it separately:

```text
SHA256(
  u16_be(len("zenodex.global_settlement.lane_module_release_record.v1")) ||
  "zenodex.global_settlement.lane_module_release_record.v1" ||
  u16_be(release_version) || release_id || status_code
)
```

The fixed content-ID vector is:

```text
bccb5f3d9db235c60e823e89bfade730efb13bc17a30be755bb8dc0a3e092de0
```

The SHA-256 digest of its canonical `ActiveNew` Postcard record is:

```text
5dd4a6981186f18d87249585f8482ce0e889fbccb36bf823aafa26b714572c41
```

Tests independently mutate every schema root, command-variant root, guest image,
provenance root, terminal field, migration field, lane, and resource ceiling.
Each mutation changes the release ID. Changing only lifecycle status preserves
the release ID and changes the record commitment.

## Lifecycle Contract

Stable status codes are:

| Code | Status |
| ---: | --- |
| 0 | `Candidate` |
| 1 | `Shadow` |
| 2 | `ActiveNew` |
| 3 | `DrainOnly` |
| 4 | `VerifyOnly` |
| 5 | `Retired` |
| 6 | `Revoked` |

Ordinary forward edges are:

```text
Candidate -> Shadow -> ActiveNew -> DrainOnly -> VerifyOnly -> Retired
```

Every non-revoked status may transition directly to `Revoked`. All other edges,
including same-state transitions and transitions out of `Revoked`, reject.
The test matrix evaluates all 49 ordered status pairs.

`ActiveNew` alone admits new-object creation. `ActiveNew` and `DrainOnly` admit
transitions for objects already pinned to the release. Other statuses reject
both admission forms. These methods return ordinary typed results and cannot
publish state.

`ActiveNew`, `DrainOnly`, `VerifyOnly`, and `Retired` require terminal coverage
status `Complete`. `Candidate`, `Shadow`, and `Revoked` may retain incomplete
coverage while carrying no current command authority. Promotion of an
incomplete shadow release to `ActiveNew` rejects without changing the source
record.

## Exact Codec

The canonical Postcard record is bounded to 2,048 bytes and rejects:

- empty or oversized input;
- trailing bytes;
- unknown enum discriminants;
- zero typed IDs or roots;
- invalid migration predecessor cardinality;
- stale release version;
- a release ID that differs from recomputed content identity;
- any byte sequence that does not round-trip to the exact canonical encoding.

The decoder constructs validated migration and resource values before it can
construct a release record.

## Evidence

`protocol/tests/lane_module_release_v1.rs` and its identity support module cover:

- all 49 lifecycle pairs and exact status codes;
- terminal-incomplete direct and transition-based activation rejection;
- exact new-object and existing-object admission by status;
- reject-is-no-op for lifecycle and admission failures;
- identity mutation for every content field group;
- lifecycle-status identity exclusion and record-commitment inclusion;
- migration predecessor cardinality;
- resource limits at zero, one, and integer maxima;
- canonical round trip, fixed vectors, counterfeit ID, stale version, invalid
  status discriminant, trailing, empty, and maximum-plus-one byte boundaries.

## Negative Knowledge

This contract does not bind a lane registry root to a canonical release set. It
does not prove lifecycle history, governance authorization, release equivalence,
coexistence, migration correctness, terminal behavior, resource consumption,
guest semantics, receipt validity, command-to-lane mapping, route selection,
profile activation, no-bypass, or atomic ZenoLedger publication.

An `ActiveNew` value is ordinary caller-constructible typed data. Current
authority requires a future release registry and profile verifier to establish
that exact record under the active authority epoch. Semver remains descriptive
and absent from this authority contract.

The promoted ShapeForge seed remains unchanged because this checkout has no
recorded regeneration command for that artifact family. This document is the
reviewable contract candidate until the promoted bundle can be rebuilt and
validated by its recorded pipeline.

## Next Safe Slice

Define a bounded canonical `LaneModuleReleaseRegistryV1` for one lane. Require
unique release IDs, one lane across all records, at most one `ActiveNew` release,
predecessor reachability, exact record ordering, and a root that can equal the
corresponding `GlobalEconomicLaneRegistryV1` row. Keep registry resolution
ordinary typed data until profile verification supplies an opaque authority
witness.
