# ZRPF Global Economic Lane Registry V1

Date: 2026-08-06
Status: `CONTRACT_IMPLEMENTED`, unmounted and without proof or settlement authority

## Scope

This slice establishes the first closed vocabulary in `GlobalSettlementABI V1`.
It defines the exact whole-economy lane identities, commits one explicit command
status and one module-release-registry root per lane, and fails closed before a
transition when an identifier is unknown, malformed, or disabled.

The implementation lives in the proof-system-neutral
`zenodex-zrpf-protocol-v3` crate. It uses integer codes, exact uppercase labels,
bounded canonical Postcard encoding, and a domain-separated SHA-256 commitment.

## ShapeForge Delta

```text
Phi := <
  M = zenodex_shape_reference_v3,
  S = global_economic_lane_registry_v1,
  A = guard,
  T = contract_strengthening,
  V = {lane_id, command_status, module_release_registry_root},
  O = {parse_exact, canonical_commitment, resolve_new_command_lane},
  G = {closed_lane_id, complete_canonical_registry, enabled_for_new_command},
  Obs = {typed_lane_or_stable_reject, registry_commitment},
  K = none,
  E = {contract, boundary, property, mutation_negative},
  Gap = {release_semantics, command_variant_mapping, route, proof, publisher, migration},
  N = {open_string_lane, omitted_lane, duplicate_lane, reordered_lane, disabled_admission},
  Delta = {twelve_lane_total_registry_and_fail_closed_resolution}
>
```

The perturbed axis is the lane-admission guard. Economic policy, route choice,
proof recursion, and publication remain unchanged.

## Closed Lane Set

| Code | Stable ID |
| ---: | --- |
| 0 | `ASSET_TRANSFER` |
| 1 | `SPOT_LIQUIDITY` |
| 2 | `FARM_INCENTIVES` |
| 3 | `ZDEX_TOKENOMICS` |
| 4 | `ZUSD_MONETARY` |
| 5 | `PERPS_MARKET` |
| 6 | `ORACLE_MARKET` |
| 7 | `SEALED_AUCTION` |
| 8 | `STRATEGY_ESCROW` |
| 9 | `PROOF_REWARDS` |
| 10 | `EXTERNAL_CUSTODY` |
| 11 | `GOVERNANCE_MIGRATION` |

Matching is byte-exact and case-sensitive. Whitespace, prefixes, suffixes,
embedded NULs, unknown codes, and research-only aliases reject.

## Registry Contract

Each canonical row is:

```text
EconomicLaneRegistryEntryV1 {
  lane_id
  command_status in {Disabled, Enabled}
  module_release_registry_root
}
```

`GlobalEconomicLaneRegistryV1` contains exactly twelve rows in code order. Every
lane appears once. Disabled lanes remain explicit committed rows. A release root
is a nonzero commitment supplied through the existing `CommitmentV3` type.

The registry commitment is:

```text
SHA256(
  u16_be(len(domain)) ||
  "zenodex.global_settlement.economic_lane_registry.v1" ||
  u16_be(registry_version) ||
  u16_be(entry_count) ||
  concat(lane_code || status_code || module_release_registry_root)
)
```

The fixed test vector for a registry with only `SPOT_LIQUIDITY` and
`ORACLE_MARKET` enabled is:

```text
d564854ac0ecbcbe63cf2f7a4ea459e2fd9568b7020ed06be352747090609fd2
```

The SHA-256 digest of the canonical Postcard encoding for the test registry
with only `GOVERNANCE_MIGRATION` enabled is:

```text
3fac997953febe4979b0257c128ec138a3d28b220a99db2305c46cad9e84fe66
```

## Rejection and No-Op Contract

Construction rejects the following classes before a registry value exists:

- wrong version;
- row cardinality other than twelve;
- duplicate lane;
- noncanonical lane order;
- zero module-release-registry roots through `CommitmentV3` construction;
- empty, oversized, trailing, malformed, or noncanonical Postcard input.

New-command resolution returns a typed lane only when exact parsing succeeds
and that lane's status is `Enabled`. It returns a stable typed rejection for an
unknown identifier or disabled lane. The registry is immutable, and negative
tests compare both the complete value and commitment before and after reject.

## Evidence

`protocol/tests/global_settlement_abi_v1.rs` covers:

- all twelve exact label/code round trips and unknown-code neighbors;
- identifier length neighbors, case mutations, whitespace, NUL, and unknown ID;
- a single case mutation for every registered label;
- disabled rejection and enabled admission;
- cardinalities `0`, `1`, `11`, `12`, and `13`;
- duplicate and reordered twelve-row registries;
- independent commitment reconstruction and a fixed vector;
- exact codec digest and round trip plus empty, maximum-plus-one, trailing,
  unknown-discriminant, and wrong-version rejects;
- reject-is-no-op for identifier and status failures.

## Negative Knowledge

This contract supplies no module release record, content-derived release ID,
release lifecycle transition, command-variant registry, route release, profile
snapshot, module transition, global effect plan, invariant proof, receipt,
migration certificate, ZenoLedger commit, adapter mount, or no-bypass evidence.
The module-release-registry root is committed data whose contents remain
unverified in this slice. `resolve_new_command_lane` returns ordinary typed data
and cannot authorize settlement.

The promoted ShapeForge seed is unchanged because this checkout has no recorded
regeneration command for that artifact family. This document is the reviewable
contract candidate until the ShapeForge promotion pipeline can rebuild and
validate the complete promoted bundle.

## Next Safe Slice

Define `LaneModuleReleaseV1` with content-derived identity, exact lifecycle
status, command-schema and guest-image commitments, terminal-coverage binding,
and compatibility metadata. Then bind each lane registry root to a canonical
release set and test `ACTIVE_NEW`, `DRAIN_ONLY`, disabled, revoked, and unknown
release admission without mounting any publisher.
