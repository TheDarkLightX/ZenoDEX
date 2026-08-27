#!/usr/bin/env python3
"""Targets, source universes, applicability grid, and obligation rows (WholeEconomyDisasterCoverageV1).

Everything here is derived from owned pinned bytes.  The grid is
``targets x 9 phases x 12 families``; every cell is classified from an
explicit registry decision or stays ``APPLICABILITY_UNKNOWN``.  Source-derived
universes are composition inputs, counted and rooted, never obligations by
themselves.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Mapping, Sequence, cast

from tools.runtime_disaster_discovery_primitives_v1 import (
    RejectCodeV1,
    decode_strict_json,
    domain_hash_hex,
    domain_root,
    reject,
    require_bool,
    require_closed_object,
    require_enum,
    require_identifier,
    require_int,
    require_list,
    require_object,
    require_root,
    require_string,
    require_token,
    require_token_list,
    require_unique_ids,
    sha256_hex,
    validate_repo_path,
)
from tools.runtime_disaster_discovery_registry_v1 import (
    BadPredicateV1,
    CellKey,
    RegistryV1,
)
from tools.runtime_disaster_discovery_sources_v1 import BoundSourceV1, OwnedSourceV1, bind_artifact
from tools.runtime_disaster_discovery_vocabulary_v1 import (
    AGGREGATE_FAMILIES_V1,
    ATTACK_FAMILIES_V1,
    CLOSURE_MODES_V1,
    DANGEROUS_SURFACES_PATH_V1,
    EXPECTED_M6_CAPABILITY_MANIFEST_ROOT_V1,
    M6_LANE_ORDER_V1,
    M6_MANIFEST_HASH_DOMAIN_V1,
    M6_MANIFEST_PATH_V1,
    MAX_PRIORITY_SCORE_V1,
    MAX_SOURCE_BYTES_V1,
    OBLIGATION_ID_PREFIX_V1,
    POKAYOKE_MATRIX_PATH_V1,
    REGISTRY_PATH_V1,
    SHAPEFORGE_SEED_PATH_V1,
    STATEFUL_BRIDGE_PATH_V1,
    UNSPECIFIED_V1,
    V1_FLOOR_APPLICABILITY_CELLS,
    V1_FLOOR_CAPABILITIES,
    V1_FLOOR_EXCLUSIONS,
    V1_FLOOR_ROUTES,
    WRITER_INVENTORY_PATH_V1,
    ApplicabilityV1,
    InvariantFamilyV1,
    InventoryUniverseV1,
    LifecyclePhaseV1,
    TargetKindV1,
)

# --------------------------------------------------------------------------
# Targets from the M6 capability manifest
# --------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class TargetV1:
    kind: TargetKindV1
    target_id: str
    lane_id: str | None
    disposition: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind.value,
            "target_id": self.target_id,
            "lane_id": self.lane_id,
            "disposition": self.disposition,
        }


@dataclass(frozen=True, slots=True)
class M6ManifestViewV1:
    manifest_root: str
    lane_ids: tuple[str, ...]
    targets: tuple[TargetV1, ...]
    capability_count: int
    route_count: int
    exclusion_count: int


def _lane_targets(obj: Mapping[str, object]) -> tuple[tuple[str, ...], list[TargetV1]]:
    targets: list[TargetV1] = []
    lane_ids: list[str] = []
    for index, lane in enumerate(require_list(obj.get("lanes"), "lanes")):
        row = require_object(lane, f"lanes[{index}]")
        lane_id = require_token(row.get("lane_id"), f"lanes[{index}].lane_id")
        disposition = require_token(row.get("disposition"), f"lanes[{index}].disposition")
        capabilities = require_token_list(
            row.get("capabilities"), f"lanes[{index}].capabilities", unique=True
        )
        if not capabilities:
            raise reject(RejectCodeV1.MANIFEST_INVALID, f"lane without capabilities: {lane_id}")
        lane_ids.append(lane_id)
        targets.extend(
            TargetV1(TargetKindV1.CAPABILITY, f"{lane_id}:{capability}", lane_id, disposition)
            for capability in capabilities
        )
    if tuple(lane_ids) != M6_LANE_ORDER_V1:
        raise reject(RejectCodeV1.MANIFEST_INVALID, "lane ids or order")
    return tuple(lane_ids), targets


def parse_m6_manifest(data: bytes) -> M6ManifestViewV1:
    """Derive the 103 + 4 + 4 targets in manifest order and check the exact root."""

    obj = require_object(
        decode_strict_json(data, name="m6 manifest", max_bytes=MAX_SOURCE_BYTES_V1), "m6 manifest"
    )
    if obj.get("schema") != "zenodex/m6-capability-manifest/v1":
        raise reject(RejectCodeV1.MANIFEST_INVALID, "schema")
    if obj.get("manifest_complete") is not False:
        raise reject(RejectCodeV1.MANIFEST_INVALID, "manifest_complete must remain false")
    lane_ids, targets = _lane_targets(obj)
    routes = require_token_list(
        obj.get("required_cross_lane_routes"), "required_cross_lane_routes", unique=True
    )
    targets.extend(
        TargetV1(TargetKindV1.CROSS_LANE_ROUTE, route, None, "REQUIRED_ROUTE") for route in routes
    )
    exclusion_ids: list[str] = []
    for index, item in enumerate(
        require_list(obj.get("explicit_exclusions"), "explicit_exclusions")
    ):
        row = require_closed_object(
            item, ("capability", "disposition"), f"explicit_exclusions[{index}]"
        )
        capability = require_token(row["capability"], f"explicit_exclusions[{index}].capability")
        exclusion_ids.append(capability)
        disposition = require_token(row["disposition"], f"explicit_exclusions[{index}].disposition")
        targets.append(TargetV1(TargetKindV1.EXPLICIT_EXCLUSION, capability, None, disposition))
    require_unique_ids(exclusion_ids, "explicit_exclusions")
    if not routes or not exclusion_ids:
        raise reject(RejectCodeV1.MANIFEST_INVALID, "routes and exclusions must be nonempty")
    require_unique_ids([target.target_id for target in targets], "targets")
    manifest_root = domain_root(M6_MANIFEST_HASH_DOMAIN_V1, obj)
    if manifest_root != EXPECTED_M6_CAPABILITY_MANIFEST_ROOT_V1:
        raise reject(RejectCodeV1.MANIFEST_ROOT_DRIFT, manifest_root)
    return M6ManifestViewV1(
        manifest_root=manifest_root,
        lane_ids=lane_ids,
        targets=tuple(targets),
        capability_count=sum(1 for target in targets if target.kind is TargetKindV1.CAPABILITY),
        route_count=len(routes),
        exclusion_count=len(exclusion_ids),
    )


# --------------------------------------------------------------------------
# Source-derived inventory universes (composition inputs, not grid cells)
# --------------------------------------------------------------------------

AttributeValue = str | int | bool | tuple[str, ...]


@dataclass(frozen=True, slots=True)
class InventoryEntryV1:
    universe: InventoryUniverseV1
    entry_id: str
    source_path: str
    attributes: tuple[tuple[str, AttributeValue], ...]

    def to_canonical(self) -> dict[str, object]:
        return {
            "universe": self.universe.value,
            "entry_id": self.entry_id,
            "source_path": self.source_path,
            "attributes": {key: value for key, value in self.attributes},
        }


def _entry(
    universe: InventoryUniverseV1,
    entry_id: str,
    source_path: str,
    attributes: Mapping[str, AttributeValue],
) -> InventoryEntryV1:
    return InventoryEntryV1(universe, entry_id, source_path, tuple(sorted(attributes.items())))


def _string_count(value: object, name: str) -> int:
    items = require_list(value, name)
    for index, item in enumerate(items):
        require_string(item, f"{name}[{index}]")
    return len(items)


def _text_sha256(value: object, name: str) -> str:
    return sha256_hex(require_string(value, name).encode("utf-8"))


def _tuple_or_list(value: object, name: str) -> tuple[object, ...]:
    if type(value) is tuple:
        return value
    if type(value) is list:
        return tuple(value)
    raise reject(RejectCodeV1.TYPE_MISMATCH, f"{name}: sequence required")


def _bridge_literal(tree: ast.Module, symbol: str) -> object:
    for node in tree.body:
        target_names: list[str] = []
        value: ast.expr | None = None
        if isinstance(node, ast.Assign):
            target_names = [item.id for item in node.targets if isinstance(item, ast.Name)]
            value = node.value
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            target_names = [node.target.id]
            value = node.value
        if symbol in target_names and value is not None:
            try:
                return ast.literal_eval(value)
            except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError) as exc:
                raise reject(
                    RejectCodeV1.BRIDGE_INVENTORY_UNEXTRACTABLE, f"{symbol}: non-literal"
                ) from exc
    raise reject(RejectCodeV1.BRIDGE_INVENTORY_UNEXTRACTABLE, f"{symbol}: missing")


def _bridge_axis_entry(axis: object, index: int, known: frozenset[str]) -> InventoryEntryV1:
    name = f"DISASTER_SEARCH_EXPANSION_AXES[{index}]"
    row = require_object(axis, name)
    axis_id = require_token(row.get("axis_id"), f"{name}.axis_id")
    surfaces = require_token_list(
        list(_tuple_or_list(row.get("surface_ids"), f"{name}.surface_ids")),
        f"{name}.surface_ids",
        unique=True,
    )
    return _entry(
        InventoryUniverseV1.BRIDGE_EXPANSION_AXIS,
        axis_id,
        STATEFUL_BRIDGE_PATH_V1,
        {
            "priority_score": require_int(
                row.get("priority_score"),
                f"{name}.priority_score",
                low=-MAX_PRIORITY_SCORE_V1,
                high=MAX_PRIORITY_SCORE_V1,
            ),
            "surface_ids": surfaces,
            "unregistered_surface_ids": tuple(item for item in surfaces if item not in known),
            "mutation_family_count": len(
                _tuple_or_list(row.get("mutation_families"), f"{name}.mutation_families")
            ),
            "declared_command_count": len(_tuple_or_list(row.get("commands"), f"{name}.commands")),
        },
    )


def derive_bridge_axes(
    data: bytes, surface_ids: Sequence[str]
) -> tuple[tuple[InventoryEntryV1, ...], tuple[str, ...]]:
    """Extract declared expansion axes by parsing the bridge source; never import or execute it."""

    try:
        tree = ast.parse(data.decode("utf-8"), filename=STATEFUL_BRIDGE_PATH_V1)
    except (UnicodeDecodeError, SyntaxError, ValueError, RecursionError) as exc:
        raise reject(RejectCodeV1.BRIDGE_INVENTORY_UNEXTRACTABLE, "parse") from exc
    axes = _bridge_literal(tree, "DISASTER_SEARCH_EXPANSION_AXES")
    critical = _bridge_literal(tree, "CRITICAL_DISASTER_SURFACE_IDS")
    if type(axes) is not tuple or type(critical) is not tuple:
        raise reject(RejectCodeV1.BRIDGE_INVENTORY_UNEXTRACTABLE, "shape")
    critical_ids = require_token_list(list(critical), "CRITICAL_DISASTER_SURFACE_IDS", unique=True)
    known = frozenset(surface_ids)
    entries = tuple(_bridge_axis_entry(axis, index, known) for index, axis in enumerate(axes))
    require_unique_ids([entry.entry_id for entry in entries], "DISASTER_SEARCH_EXPANSION_AXES")
    return entries, critical_ids


def _surface_ids(data: bytes) -> tuple[str, ...]:
    obj = require_object(
        decode_strict_json(data, name="dangerous surfaces", max_bytes=MAX_SOURCE_BYTES_V1),
        "dangerous surfaces",
    )
    return tuple(
        require_token(require_object(item, f"surfaces[{index}]").get("id"), f"surfaces[{index}].id")
        for index, item in enumerate(require_list(obj.get("surfaces"), "surfaces"))
    )


def derive_dangerous_surfaces(
    data: bytes, critical_ids: Sequence[str]
) -> tuple[InventoryEntryV1, ...]:
    obj = require_object(
        decode_strict_json(data, name="dangerous surfaces", max_bytes=MAX_SOURCE_BYTES_V1),
        "dangerous surfaces",
    )
    if obj.get("schema") != "zenodex/stateful-dangerous-surface-manifest/v1":
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "dangerous surfaces schema")
    entries: list[InventoryEntryV1] = []
    for index, item in enumerate(require_list(obj.get("surfaces"), "surfaces")):
        name = f"surfaces[{index}]"
        row = require_object(item, name)
        surface_id = require_token(row.get("id"), f"{name}.id")
        entries.append(
            _entry(
                InventoryUniverseV1.DANGEROUS_SURFACE,
                surface_id,
                DANGEROUS_SURFACES_PATH_V1,
                {
                    "machine_family": require_string(
                        row.get("machine_family"), f"{name}.machine_family"
                    ),
                    "invariant_boundary_sha256": _text_sha256(
                        row.get("invariant_boundary"), f"{name}.invariant_boundary"
                    ),
                    "witness_ids": require_token_list(
                        row.get("witness_ids"), f"{name}.witness_ids", unique=True
                    ),
                    "harness_count": _string_count(row.get("harnesses"), f"{name}.harnesses"),
                    "critical": surface_id in critical_ids,
                },
            )
        )
    require_unique_ids([entry.entry_id for entry in entries], "surfaces")
    if not entries:
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "no dangerous surfaces")
    return tuple(entries)


def _writer_entry(item: object, name: str) -> InventoryEntryV1:
    row = require_object(item, name)
    return _entry(
        InventoryUniverseV1.WRITER_ENTRYPOINT,
        require_token(row.get("entrypoint_id"), f"{name}.entrypoint_id"),
        WRITER_INVENTORY_PATH_V1,
        {
            "path": validate_repo_path(row.get("path"), f"{name}.path"),
            "symbol": require_identifier(row.get("symbol"), f"{name}.symbol"),
            "kind": require_string(row.get("kind"), f"{name}.kind"),
            "m6_mount_status": require_string(
                row.get("m6_mount_status"), f"{name}.m6_mount_status"
            ),
            "commit_port_route": require_string(
                row.get("commit_port_route"), f"{name}.commit_port_route"
            ),
            "requires_unique_commit_port": require_bool(
                row.get("requires_unique_commit_port"), f"{name}.requires_unique_commit_port"
            ),
        },
    )


def _coverage_row(
    item: object, name: str, registered: frozenset[str], lane_ids: Sequence[str]
) -> InventoryEntryV1:
    row = require_object(item, name)
    entrypoint_id = require_token(row.get("entrypoint_id"), f"{name}.entrypoint_id")
    if entrypoint_id not in registered:
        raise reject(
            RejectCodeV1.INVENTORY_SOURCE_INVALID, f"{name}: unregistered writer {entrypoint_id}"
        )
    row_lanes = require_token_list(row.get("lane_ids"), f"{name}.lane_ids", unique=True)
    if any(lane not in lane_ids for lane in row_lanes):
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, f"{name}: unknown lane")
    return _entry(
        InventoryUniverseV1.WRITER_COVERAGE_ROW,
        require_token(row.get("coverage_id"), f"{name}.coverage_id"),
        WRITER_INVENTORY_PATH_V1,
        {
            "entrypoint_id": entrypoint_id,
            "release_status": require_string(row.get("release_status"), f"{name}.release_status"),
            "lane_ids": row_lanes,
            "workflow_ids": require_token_list(
                row.get("workflow_ids"), f"{name}.workflow_ids", unique=True
            ),
            "assurance_statuses": require_token_list(
                row.get("assurance_statuses"), f"{name}.assurance_statuses", unique=True
            ),
        },
    )


def derive_writer_inventory(
    data: bytes, lane_ids: Sequence[str]
) -> tuple[tuple[InventoryEntryV1, ...], tuple[InventoryEntryV1, ...]]:
    obj = require_object(
        decode_strict_json(data, name="writer inventory", max_bytes=MAX_SOURCE_BYTES_V1),
        "writer inventory",
    )
    if obj.get("schema") != "zenodex/m6-writer-inventory/v1":
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "writer inventory schema")
    entries = tuple(
        _writer_entry(item, f"entries[{index}]")
        for index, item in enumerate(require_list(obj.get("entries"), "entries"))
    )
    require_unique_ids([entry.entry_id for entry in entries], "entries")
    registered = frozenset(entry.entry_id for entry in entries)
    contract = require_object(obj.get("coverage_contract"), "coverage_contract")
    if contract.get("schema") != "zenodex/m6-writer-coverage/v1":
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "writer coverage schema")
    rows = tuple(
        _coverage_row(item, f"coverage_contract.rows[{index}]", registered, lane_ids)
        for index, item in enumerate(require_list(contract.get("rows"), "coverage_contract.rows"))
    )
    require_unique_ids([entry.entry_id for entry in rows], "coverage_contract.rows")
    if not entries or not rows:
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "empty writer inventory")
    return entries, rows


def _ids_of(value: object, name: str) -> tuple[str, ...]:
    return require_token_list(
        [
            require_object(item, f"{name}[{index}]").get("id")
            for index, item in enumerate(require_list(value, name))
        ],
        name,
        unique=True,
    )


def _scenario_entry(
    item: object, name: str, actor_ids: Sequence[str], control_ids: Sequence[str]
) -> InventoryEntryV1:
    row = require_object(item, name)
    actors = require_token_list(row.get("actors"), f"{name}.actors", unique=True)
    controls = require_token_list(row.get("controls"), f"{name}.controls", unique=True)
    if any(actor not in actor_ids for actor in actors) or any(
        control not in control_ids for control in controls
    ):
        raise reject(
            RejectCodeV1.INVENTORY_SOURCE_INVALID, f"{name}: unregistered actor or control"
        )
    evidence_lane = require_object(row.get("evidence_lane"), f"{name}.evidence_lane")
    promotion = require_object(row.get("promotion_boundary"), f"{name}.promotion_boundary")
    bounded_model = require_object(row.get("bounded_model"), f"{name}.bounded_model")
    return _entry(
        InventoryUniverseV1.POKAYOKE_SCENARIO,
        require_token(row.get("id"), f"{name}.id"),
        POKAYOKE_MATRIX_PATH_V1,
        {
            "severity": require_string(row.get("severity"), f"{name}.severity"),
            "stage": require_string(row.get("stage"), f"{name}.stage"),
            "ordered_participants": actors,
            "controls": controls,
            "disaster_state_sha256": _text_sha256(
                row.get("disaster_state"), f"{name}.disaster_state"
            ),
            "evidence_lane_status": require_string(
                evidence_lane.get("status"), f"{name}.evidence_lane.status"
            ),
            "claim_status": require_string(
                promotion.get("claim_status"), f"{name}.promotion_boundary.claim_status"
            ),
            "declared_bound_count": _string_count(
                bounded_model.get("bounds"), f"{name}.bounded_model.bounds"
            ),
            "side_channel_count": len(
                require_list(row.get("side_channels"), f"{name}.side_channels")
            ),
            "covert_channel_count": len(
                require_list(row.get("covert_channels"), f"{name}.covert_channels")
            ),
        },
    )


def derive_pokayoke_scenarios(data: bytes) -> tuple[InventoryEntryV1, ...]:
    obj = require_object(
        decode_strict_json(data, name="pokayoke matrix", max_bytes=MAX_SOURCE_BYTES_V1),
        "pokayoke matrix",
    )
    if obj.get("schema") != "zenodex/adversarial_hardening_pokayoke_matrix/v1":
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "pokayoke schema")
    actor_ids = _ids_of(obj.get("actors"), "actors")
    control_ids = _ids_of(obj.get("control_classes"), "control_classes")
    entries = tuple(
        _scenario_entry(item, f"scenarios[{index}]", actor_ids, control_ids)
        for index, item in enumerate(require_list(obj.get("scenarios"), "scenarios"))
    )
    require_unique_ids([entry.entry_id for entry in entries], "scenarios")
    if not entries:
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "no pokayoke scenarios")
    return entries


def _invariant_entry(item: object, name: str) -> InventoryEntryV1:
    row = require_closed_object(item, ("id", "formula", "sources"), name)
    sources = tuple(
        validate_repo_path(source, f"{name}.sources[{position}]")
        for position, source in enumerate(require_list(row["sources"], f"{name}.sources"))
    )
    if len(set(sources)) != len(sources) or not sources:
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, f"{name}: sources")
    return _entry(
        InventoryUniverseV1.SHAPEFORGE_CROSS_SLICE_INVARIANT,
        require_token(row["id"], f"{name}.id"),
        SHAPEFORGE_SEED_PATH_V1,
        {"formula_sha256": _text_sha256(row["formula"], f"{name}.formula"), "sources": sources},
    )


def _transform_entry(
    item: object, name: str, axes: Sequence[str], slice_ids: Sequence[str]
) -> InventoryEntryV1:
    row = require_object(item, name)
    axis = require_token(row.get("axis"), f"{name}.axis")
    slice_id = require_token(row.get("slice_id"), f"{name}.slice_id")
    if axis not in axes or slice_id not in slice_ids:
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, f"{name}: axis or slice")
    return _entry(
        InventoryUniverseV1.SHAPEFORGE_SCENARIO_TRANSFORM,
        require_token(row.get("scenario_id"), f"{name}.scenario_id"),
        SHAPEFORGE_SEED_PATH_V1,
        {
            "axis": axis,
            "slice_id": slice_id,
            "improvement_target": require_string(
                row.get("improvement_target"), f"{name}.improvement_target"
            ),
            "status_if_unproved": require_string(
                row.get("status_if_unproved"), f"{name}.status_if_unproved"
            ),
            "perturbation_sha256": _text_sha256(row.get("perturbation"), f"{name}.perturbation"),
            "evidence_required_count": _string_count(
                row.get("evidence_required"), f"{name}.evidence_required"
            ),
            "expected_effect_count": _string_count(
                row.get("expected_effects"), f"{name}.expected_effects"
            ),
        },
    )


def derive_shapeforge(
    data: bytes,
) -> tuple[tuple[InventoryEntryV1, ...], tuple[InventoryEntryV1, ...]]:
    obj = require_object(
        decode_strict_json(data, name="shapeforge seed", max_bytes=MAX_SOURCE_BYTES_V1),
        "shapeforge seed",
    )
    if obj.get("schema") != "shapeforge/world-model-seed/v1":
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "shapeforge schema")
    axes = require_token_list(obj.get("slice_axes"), "slice_axes", unique=True)
    slice_ids = require_token_list(
        [
            require_object(item, f"slices[{index}]").get("slice_id")
            for index, item in enumerate(require_list(obj.get("slices"), "slices"))
        ],
        "slices",
        unique=True,
    )
    invariants = tuple(
        _invariant_entry(item, f"cross_slice_invariants[{index}]")
        for index, item in enumerate(
            require_list(obj.get("cross_slice_invariants"), "cross_slice_invariants")
        )
    )
    require_unique_ids([entry.entry_id for entry in invariants], "cross_slice_invariants")
    transforms = tuple(
        _transform_entry(item, f"scenario_transforms[{index}]", axes, slice_ids)
        for index, item in enumerate(
            require_list(obj.get("scenario_transforms"), "scenario_transforms")
        )
    )
    require_unique_ids([entry.entry_id for entry in transforms], "scenario_transforms")
    if not invariants or not transforms:
        raise reject(RejectCodeV1.INVENTORY_SOURCE_INVALID, "empty shapeforge universes")
    return invariants, transforms


def aggregate_family_entries() -> tuple[InventoryEntryV1, ...]:
    return tuple(
        _entry(
            InventoryUniverseV1.AGGREGATE_FAMILY,
            family.value,
            REGISTRY_PATH_V1,
            {"invariant_family": family.value},
        )
        for family in AGGREGATE_FAMILIES_V1
    )


def derive_entries(
    bound: Mapping[str, BoundSourceV1], lane_ids: Sequence[str]
) -> tuple[InventoryEntryV1, ...]:
    surface_ids = _surface_ids(bound[DANGEROUS_SURFACES_PATH_V1].data)
    axes, critical_ids = derive_bridge_axes(bound[STATEFUL_BRIDGE_PATH_V1].data, surface_ids)
    surfaces = derive_dangerous_surfaces(bound[DANGEROUS_SURFACES_PATH_V1].data, critical_ids)
    writers, coverage_rows = derive_writer_inventory(bound[WRITER_INVENTORY_PATH_V1].data, lane_ids)
    scenarios = derive_pokayoke_scenarios(bound[POKAYOKE_MATRIX_PATH_V1].data)
    invariants, transforms = derive_shapeforge(bound[SHAPEFORGE_SEED_PATH_V1].data)
    entries = (
        *surfaces,
        *writers,
        *coverage_rows,
        *scenarios,
        *axes,
        *invariants,
        *transforms,
        *aggregate_family_entries(),
    )
    for universe in InventoryUniverseV1:
        require_unique_ids(
            [entry.entry_id for entry in entries if entry.universe is universe], universe.value
        )
    return entries


# --------------------------------------------------------------------------
# Obligation keys, cells, and rows
# --------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class ObligationKeyV1:
    """Canonical obligation identity.  ``obligation_id`` is WEDC1- + SHA-256."""

    semantic_requirement_root: str
    target_kind: TargetKindV1
    target_id: str
    ordered_participants: tuple[str, ...]
    lifecycle_phase: LifecyclePhaseV1
    invariant_family: InvariantFamilyV1
    attack_family: str
    bad_predicate_id: str
    bounds_profile_id: str
    closure_mode: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "semantic_requirement_root": self.semantic_requirement_root,
            "target_kind": self.target_kind.value,
            "target_id": self.target_id,
            "ordered_participants": list(self.ordered_participants),
            "lifecycle_phase": self.lifecycle_phase.value,
            "invariant_family": self.invariant_family.value,
            "attack_family": self.attack_family,
            "bad_predicate_id": self.bad_predicate_id,
            "bounds_profile_id": self.bounds_profile_id,
            "closure_mode": self.closure_mode,
        }

    @property
    def obligation_id(self) -> str:
        return OBLIGATION_ID_PREFIX_V1 + domain_hash_hex(
            "wedc1-obligation-key", self.to_canonical()
        )

    @property
    def cell(self) -> CellKey:
        return (self.target_kind, self.target_id, self.lifecycle_phase, self.invariant_family)


_KEY_FIELDS = (
    "semantic_requirement_root",
    "target_kind",
    "target_id",
    "ordered_participants",
    "lifecycle_phase",
    "invariant_family",
    "attack_family",
    "bad_predicate_id",
    "bounds_profile_id",
    "closure_mode",
)


def parse_obligation_key(value: object, name: str) -> ObligationKeyV1:
    raw = require_closed_object(value, _KEY_FIELDS, name)
    attack_family = require_token(raw["attack_family"], f"{name}.attack_family")
    closure_mode = require_token(raw["closure_mode"], f"{name}.closure_mode")
    if attack_family not in ATTACK_FAMILIES_V1 or closure_mode not in CLOSURE_MODES_V1:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}: attack family or closure mode")
    return ObligationKeyV1(
        semantic_requirement_root=require_root(
            raw["semantic_requirement_root"], f"{name}.semantic_requirement_root"
        ),
        target_kind=cast(
            TargetKindV1, require_enum(raw["target_kind"], TargetKindV1, f"{name}.target_kind")
        ),
        target_id=require_token(raw["target_id"], f"{name}.target_id"),
        ordered_participants=require_token_list(
            raw["ordered_participants"], f"{name}.ordered_participants", unique=True
        ),
        lifecycle_phase=cast(
            LifecyclePhaseV1,
            require_enum(raw["lifecycle_phase"], LifecyclePhaseV1, f"{name}.lifecycle_phase"),
        ),
        invariant_family=cast(
            InvariantFamilyV1,
            require_enum(raw["invariant_family"], InvariantFamilyV1, f"{name}.invariant_family"),
        ),
        attack_family=attack_family,
        bad_predicate_id=require_token(raw["bad_predicate_id"], f"{name}.bad_predicate_id"),
        bounds_profile_id=require_token(raw["bounds_profile_id"], f"{name}.bounds_profile_id"),
        closure_mode=closure_mode,
    )


@dataclass(frozen=True, slots=True)
class ApplicabilityCellV1:
    target_kind: TargetKindV1
    target_id: str
    lifecycle_phase: LifecyclePhaseV1
    invariant_family: InvariantFamilyV1
    classification: ApplicabilityV1
    basis: str

    @property
    def cell(self) -> CellKey:
        return (self.target_kind, self.target_id, self.lifecycle_phase, self.invariant_family)

    def to_canonical(self) -> dict[str, object]:
        return {
            "target_kind": self.target_kind.value,
            "target_id": self.target_id,
            "lifecycle_phase": self.lifecycle_phase.value,
            "invariant_family": self.invariant_family.value,
            "classification": self.classification.value,
            "basis": self.basis,
        }


@dataclass(frozen=True, slots=True)
class ObligationRowV1:
    key: ObligationKeyV1
    obligation_id: str
    applicability: ApplicabilityV1
    predicate: BadPredicateV1 | None

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "key": self.key.to_canonical(),
            "applicability": self.applicability.value,
        }


@dataclass(frozen=True, slots=True)
class ObligationInventoryV1:
    manifest: M6ManifestViewV1
    cells: tuple[ApplicabilityCellV1, ...]
    rows: tuple[ObligationRowV1, ...]
    entries: tuple[InventoryEntryV1, ...]
    stale_certificate_cell_count: int

    def row(self, obligation_id: str) -> ObligationRowV1 | None:
        return next((row for row in self.rows if row.obligation_id == obligation_id), None)

    def entry(self, universe: InventoryUniverseV1, entry_id: str) -> InventoryEntryV1 | None:
        return next(
            (row for row in self.entries if row.universe is universe and row.entry_id == entry_id),
            None,
        )

    def classification_counts(self) -> dict[str, int]:
        counts = {classification.value: 0 for classification in ApplicabilityV1}
        for cell in self.cells:
            counts[cell.classification.value] += 1
        return counts

    def universe_counts(self) -> dict[str, int]:
        counts = {universe.value: 0 for universe in InventoryUniverseV1}
        for entry in self.entries:
            counts[entry.universe.value] += 1
        return counts

    def universe_roots(self) -> dict[str, str]:
        return {
            universe.value: domain_root(
                "wedc1-inventory-universe",
                {
                    "universe": universe.value,
                    "entries": [
                        entry.to_canonical() for entry in self.entries if entry.universe is universe
                    ],
                },
            )
            for universe in InventoryUniverseV1
        }

    def cells_root(self) -> str:
        return domain_root(
            "wedc1-applicability-cells", [cell.to_canonical() for cell in self.cells]
        )

    def rows_root(self) -> str:
        return domain_root("wedc1-obligation-rows", [row.to_canonical() for row in self.rows])

    def inventory_root(self) -> str:
        return domain_root(
            "wedc1-obligation-inventory",
            {
                "cells_root": self.cells_root(),
                "rows_root": self.rows_root(),
                "universe_roots": self.universe_roots(),
            },
        )


def _classify_cell(
    registry: RegistryV1,
    cell: CellKey,
    subject_commit: str,
    subject_tree: str,
    artifacts: Mapping[str, OwnedSourceV1],
) -> ApplicabilityCellV1:
    decision = registry.decision_for(cell)
    classification = ApplicabilityV1.APPLICABILITY_UNKNOWN
    basis = "DEFAULT_UNCLASSIFIED"
    if decision is not None:
        classification = decision.classification
        basis = "REGISTRY_DECISION"
        if decision.certificate is not None:
            bind_artifact(
                artifacts, decision.certificate.artifact_path, decision.certificate.artifact_sha256
            )
            if (
                decision.certificate.subject_commit != subject_commit
                or decision.certificate.subject_tree != subject_tree
            ):
                classification = ApplicabilityV1.APPLICABILITY_UNKNOWN
                basis = "STALE_CERTIFICATE_SUBJECT"
    return ApplicabilityCellV1(cell[0], cell[1], cell[2], cell[3], classification, basis)


def _unspecified_key(manifest_root: str, cell: ApplicabilityCellV1) -> ObligationKeyV1:
    return ObligationKeyV1(
        semantic_requirement_root=manifest_root,
        target_kind=cell.target_kind,
        target_id=cell.target_id,
        ordered_participants=(),
        lifecycle_phase=cell.lifecycle_phase,
        invariant_family=cell.invariant_family,
        attack_family=UNSPECIFIED_V1,
        bad_predicate_id=UNSPECIFIED_V1,
        bounds_profile_id=UNSPECIFIED_V1,
        closure_mode=UNSPECIFIED_V1,
    )


def predicate_key(manifest_root: str, predicate: BadPredicateV1) -> ObligationKeyV1:
    return ObligationKeyV1(
        semantic_requirement_root=manifest_root,
        target_kind=predicate.target_kind,
        target_id=predicate.target_id,
        ordered_participants=predicate.ordered_participants,
        lifecycle_phase=predicate.lifecycle_phase,
        invariant_family=predicate.invariant_family,
        attack_family=predicate.attack_family,
        bad_predicate_id=predicate.bad_predicate_id,
        bounds_profile_id=predicate.bounds_profile_id,
        closure_mode=predicate.closure_mode,
    )


def _check_floor(manifest: M6ManifestViewV1, registry: RegistryV1, cell_count: int) -> None:
    floor = registry.denominator_floor
    if (
        manifest.capability_count < max(floor.capabilities, V1_FLOOR_CAPABILITIES)
        or manifest.route_count < max(floor.routes, V1_FLOOR_ROUTES)
        or manifest.exclusion_count < max(floor.exclusions, V1_FLOOR_EXCLUSIONS)
    ):
        raise reject(RejectCodeV1.DENOMINATOR_BELOW_FLOOR, "manifest targets below the hard floor")
    if cell_count == 0 or cell_count < max(floor.applicability_cells, V1_FLOOR_APPLICABILITY_CELLS):
        raise reject(RejectCodeV1.DENOMINATOR_BELOW_FLOOR, f"{cell_count} cells")


def _build_rows(
    manifest_root: str, cells: Sequence[ApplicabilityCellV1], registry: RegistryV1
) -> tuple[ObligationRowV1, ...]:
    rows: list[ObligationRowV1] = []
    for cell in cells:
        predicates = registry.predicates_for(cell.cell)
        if not predicates:
            key = _unspecified_key(manifest_root, cell)
            rows.append(ObligationRowV1(key, key.obligation_id, cell.classification, None))
            continue
        for predicate in predicates:
            key = predicate_key(manifest_root, predicate)
            rows.append(ObligationRowV1(key, key.obligation_id, cell.classification, predicate))
    require_unique_ids([row.obligation_id for row in rows], "obligation rows")
    for predicate in registry.bad_predicates:
        if not any(row.predicate is predicate for row in rows):
            raise reject(RejectCodeV1.PREDICATE_CELL_NOT_REQUIRED, predicate.bad_predicate_id)
    return tuple(rows)


def derive_inventory(
    registry: RegistryV1,
    bound: Mapping[str, BoundSourceV1],
    *,
    subject_commit: str,
    subject_tree: str,
    artifacts: Mapping[str, OwnedSourceV1],
) -> ObligationInventoryV1:
    """Derive targets, cells, rows, and source universes from owned pinned bytes only."""

    manifest = parse_m6_manifest(bound[M6_MANIFEST_PATH_V1].data)
    cells = tuple(
        _classify_cell(
            registry,
            (target.kind, target.target_id, phase, family),
            subject_commit,
            subject_tree,
            artifacts,
        )
        for target in manifest.targets
        for phase in LifecyclePhaseV1
        for family in InvariantFamilyV1
    )
    _check_floor(manifest, registry, len(cells))
    known_cells = {cell.cell for cell in cells}
    for decision in registry.applicability_decisions:
        if decision.cell not in known_cells:
            raise reject(
                RejectCodeV1.APPLICABILITY_DECISION_INVALID, f"unknown cell {decision.target_id}"
            )
    rows = _build_rows(manifest.manifest_root, cells, registry)
    entries = derive_entries(bound, manifest.lane_ids)
    return ObligationInventoryV1(
        manifest=manifest,
        cells=cells,
        rows=rows,
        entries=entries,
        stale_certificate_cell_count=sum(
            1 for cell in cells if cell.basis == "STALE_CERTIFICATE_SUBJECT"
        ),
    )
