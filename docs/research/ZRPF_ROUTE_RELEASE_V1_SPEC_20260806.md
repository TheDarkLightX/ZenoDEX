# ZRPF Route Release V1

Status: implemented contract candidate; proof-neutral; unmounted;
no route-selection, settlement, or publication authority.

## Purpose

`RouteReleaseV1` defines the exact bounded composition shape assigned to one
economic command variant. It binds ordered lane-module dependencies, each
dependency's lifecycle selection purpose, roles, and public schemas,
route-level private-port pairing, explicit Oracle and issue/burn policy, and
aggregate resource ceilings to a content-derived route release ID.

The route release is immutable typed data. A caller may construct candidate
data, but cannot select the authoritative route. A future governed route
registry and profile verifier must bind the command occurrence to the active
route release before any proof or publication path can rely on it.

## ShapeForge Boundary

```text
S = route_release_v1
A = guard
T = contract_strengthening
V = {
  route_release_version,
  route_release_id,
  command_variant_root,
  ordered_dependencies,
  dependency_lifecycle_purposes,
  dependency_roles,
  receipt_and_port_schema_roots,
  port_pairing_root,
  oracle_policy,
  issue_burn_policy,
  resource_limits
}
O = {
  construct,
  derive_route_release_id,
  bind_module_release_registries,
  exact_codec
}
G = {
  one_to_eight_dependencies,
  unique_lane_dependencies,
  exactly_one_primary_role,
  closed_nonempty_role_sets,
  oracle_role_policy_coherence,
  issue_burn_role_policy_coherence,
  exact_order_binding,
  nonzero_resource_limits,
  exact_module_release_references
}
N = {
  empty_or_oversized_dependency_set,
  duplicate_lane,
  zero_or_multiple_primary_roles,
  empty_duplicate_or_unknown_roles,
  missing_or_unexpected_oracle_role,
  missing_or_unexpected_issue_burn_role,
  zero_resource_limit,
  wrong_registry_count_order_or_release,
  stale_counterfeit_trailing_or_noncanonical_wire
}
Gap = {
  governed_command_to_route_registry,
  economic_profile_authority_witness,
  authenticated_command_occurrence,
  actual_module_receipts,
  exact_private_port_values,
  route_composer_proof,
  release_aware_verifier,
  migration_certificate,
  atomic_publisher
}
```

The promoted ShapeForge bundle remains unchanged because this checkout has no
recorded regeneration command for that artifact family. This specification is
the bounded review surface.

## Stable Contract

```text
ROUTE_RELEASE_VERSION_V1 = 1
MAX_ROUTE_DEPENDENCIES_V1 = 8
MAX_ROUTE_RELEASE_BYTES_V1 = 4096

RouteReleaseV1 {
  route_release_version: u16,
  route_release_id: RouteReleaseIdV1,
  content: RouteReleaseContentV1
}

RouteReleaseContentV1 {
  command_variant_root: CommitmentV3,
  dependencies: Vec<RouteModuleDependencyV1>,
  port_pairing_root: CommitmentV3,
  oracle_policy: RouteOraclePolicyV1,
  issue_burn_policy: RouteIssueBurnPolicyV1,
  resource_limits: RouteResourceLimitsV1
}
```

Every dependency binds:

- one `EconomicLaneIdV1`;
- one exact `LaneModuleReleaseIdV1`;
- one closed `RouteDependencyLifecyclePurposeV1`;
- a nonempty closed role set;
- the expected lane-module receipt journal schema root;
- the dependency input private-port schema root;
- the dependency output private-port schema root.

Dependency order is semantic and is never silently sorted. Reordering a valid
dependency sequence derives a different route release ID. A route contains
between one and eight dependencies, every lane appears at most once, and
exactly one dependency carries the `Primary` role.

The lifecycle purpose is either `ActiveNewRelease` or
`PinnedExistingObjects`. Profile binding checks the former with
`admit_new_object_creation` and the latter with
`admit_existing_object_transition`. State binding applies the exact resolver in
`ZRPF_LIFECYCLE_ROUTE_RESOLVER_V1_SPEC_20260806.md`.

## Closed Dependency Roles

The V1 role set is:

```text
Primary
State
Oracle
Custody
Fee
IssueBurn
Terminal
```

One dependency may carry several roles. The canonical wire representation is
a nonzero seven-bit mask. Empty masks, duplicate roles at construction, and
unknown bits reject.

`RouteOraclePolicyV1` is either `Forbidden` or `Required(policy_root)`.
Forbidden requires zero `Oracle` roles; Required requires exactly one.

`RouteIssueBurnPolicyV1` is `Forbidden`, `IssueOnly(policy_root)`,
`BurnOnly(policy_root)`, or `IssueAndBurn(policy_root)`. Forbidden requires zero
`IssueBurn` roles; every authorizing variant requires exactly one.

These values bind policy identity. They do not prove that a module receipt
implemented or satisfied the policy.

## Resource Limits

The route commits nonzero ceilings for:

```text
max_total_journal_bytes: u32
max_private_port_bytes: u32
max_composition_cycles: u64
```

The dependency count is exact and separately bounded at eight. Consumers must
compare actual use with these ceilings; storing a release alone performs no
resource accounting.

## Content-Derived Identity

```text
SHA256(
  u16_be(len("zenodex.global_settlement.route_release_id.v1")) ||
  "zenodex.global_settlement.route_release_id.v1" ||
  u16_be(route_release_version) ||
  command_variant_root ||
  u8(dependency_count) ||
  concat(
    lane_code ||
    module_release_id ||
    lifecycle_purpose_code ||
    role_mask ||
    receipt_journal_schema_root ||
    input_port_schema_root ||
    output_port_schema_root
  ) ||
  port_pairing_root ||
  oracle_policy_encoding ||
  issue_burn_policy_encoding ||
  u32_be(max_total_journal_bytes) ||
  u32_be(max_private_port_bytes) ||
  u64_be(max_composition_cycles)
)
```

Policy encodings use one byte for the closed mode followed by the policy root
for every non-forbidden mode. The route release ID excludes no content field.

## Registry Binding

`bind_module_release_registries` takes one lane release registry per ordered
dependency. It requires exact cardinality and lane order, and requires the
dependency's exact module release ID to occur in that registry. The binding
does not reinterpret module lifecycle status and does not establish that any
registry is governed by the active economic profile.

## Exact Codec

The canonical encoding is bounded Postcard. Decode rejects empty or oversized
input before allocation, bounds the dependency sequence while decoding, then
reconstructs the validated content-derived value. It rejects stale versions,
counterfeit IDs, malformed or unknown lifecycle, role-mask, and policy variants,
incoherent content, trailing bytes, and any sequence that does not exactly
re-encode.

Serde struct decoding also rejects unknown fields at the route, content,
dependency, and resource-limit layers. Authority consumers must still use the
bounded exact Postcard decoder.

The fixed two-dependency route release ID is:

```text
9a25ec0269e0fde35c4d89d4c38648b1ee29feb381f290afa280e9bcd2351207
```

The SHA-256 digest of that route's canonical Postcard encoding is:

```text
2e293076bf0822ce7d43c0b2a4762e743e35891c8c390dff4a7eb198eaa362cb
```

## Required Evidence

The executable contract must include:

- BVA at 0, 1, 8, and 9 dependencies;
- both lifecycle purposes plus an unknown lifecycle discriminant;
- empty, duplicate, multi-role, and unknown role-mask cases;
- zero, one, and two Primary-role dependencies;
- duplicate-lane rejection;
- Oracle and issue/burn policy-role coherence negatives;
- order sensitivity and field-by-field identity separation;
- resource BVA at zero, one, and integer maxima;
- exact registry count, order, and release-reference binding;
- fixed route ID and encoded-byte digest;
- stale version, counterfeit identity, unknown discriminant, unknown struct
  field, nonminimal Postcard integer, empty, maximum-plus-one byte, and
  trailing-byte rejection;
- reject-is-no-op checks for caller-owned dependency data.

## Negative Knowledge

This route value alone does not select a route for a command or authenticate an occurrence,
verify a module receipt, pair actual private-port values, enforce Oracle truth,
authorize issue or burn, prove resource use, compose proofs, activate a profile,
perform migration, mount an adapter, or publish state.
