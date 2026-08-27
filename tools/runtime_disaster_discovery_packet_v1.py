#!/usr/bin/env python3
"""Denominator, flags, packet core, receipt root, and independent verification (WholeEconomyDisasterCoverageV1).

The packet's canonical core is hashed under a domain-separated receipt root.
Timestamps, duration, and previews live in telemetry outside the root.  The
verifier rebuilds the whole core from its own reads and requires byte-exact
equality; ``whole_economy_claim_allowed`` is constant ``False``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from types import MappingProxyType
from typing import Final, Mapping, Sequence, cast

from tools.runtime_disaster_discovery_evidence_v1 import (
    ExecutionObservationV1,
    ObligationResultV1,
    build_denominator_status_counts,
    expected_result_keys,
    obligation_statuses,
    parse_result,
    verify_results,
)
from tools.runtime_disaster_discovery_inventory_v1 import ObligationInventoryV1
from tools.runtime_disaster_discovery_primitives_v1 import (
    MAX_BOUND_V1,
    RejectCodeV1,
    canonical_bytes,
    decode_strict_json,
    domain_root,
    reject,
    require_bool,
    require_closed_object,
    require_enum,
    require_int,
    require_list,
    require_object,
    require_root,
    require_string,
    require_token,
)
from tools.runtime_disaster_discovery_registry_v1 import RegistryV1
from tools.runtime_disaster_discovery_sources_v1 import (
    BoundSourceV1,
    OwnedSourceV1,
    parse_source_pin,
)
from tools.runtime_disaster_discovery_subject_v1 import ExactSubjectV1, parse_subject
from tools.runtime_disaster_discovery_vocabulary_v1 import (
    BOUNDED_STATUSES_V1,
    CLAIM_CEILING_V1,
    CLOSURE_STATUSES_V1,
    COVERAGE_RATIO_WITHHELD_V1,
    HISTORICAL_MINIMUM_RELEASE_EVIDENCE_CELLS_V1,
    HISTORICAL_STRICT_RELEASE_CLOSURE_V1,
    LEGACY_BRIDGE_SCHEMAS_V1,
    MAX_PACKET_BYTES_V1,
    PACKET_SCHEMA_V1,
    V1_FLOOR_APPLICABILITY_CELLS,
    V1_FLOOR_CAPABILITIES,
    V1_FLOOR_EXCLUSIONS,
    V1_FLOOR_ROUTES,
    ApplicabilityV1,
    DenominatorStateV1,
    EvidenceStatusV1,
    ExecutionPremiseV1,
    HeadBindingV1,
    InvariantFamilyV1,
    InventoryUniverseV1,
    LifecyclePhaseV1,
    NoEffectOutcomeV1,
    RegistrySectionStateV1,
)

_FORBIDDEN_PACKET_TEXT_RE = re.compile(r"%|percent", re.IGNORECASE)

PACKET_NONCLAIMS_V1: Final = (
    "This packet closes denominator and evidence-association integrity only.",
    "No economic safety, proof, release, mount, settlement, writer, migration, finality, or production authority is granted.",
    "The whole-economy scalar remains WITHHELD while any applicability cell is unknown or any composition registry is incomplete.",
    "Exit-zero or passing tests yield at most NOT_WITNESSED_IN_TESTS; formal success closes only an exact bound theorem, predicate, and toolchain.",
    "The historical 0/967 manifest-derived baseline is an immutable diagnosis of the implementation base and is not rewritten here.",
    "Accounting locations and control domains never imply legal custody, title, possession, or key control.",
)


@dataclass(frozen=True, slots=True)
class DenominatorV1:
    state: DenominatorStateV1
    capabilities: int
    routes: int
    exclusions: int
    targets: int
    lifecycle_phases: int
    invariant_families: int
    applicability_cells: int
    classification_counts: Mapping[str, int]
    obligation_rows: int
    unspecified_rows: int
    predicate_rows: int
    stale_certificate_cells: int
    composition_registry_state: RegistrySectionStateV1
    composition_cells: int
    inventory_entry_counts: Mapping[str, int]
    composition_pending_entries: int
    evidence_status_counts: Mapping[str, int]
    historical_strict_release_closure: str
    historical_minimum_release_evidence_cells: int
    coverage_ratio: str

    def __post_init__(self) -> None:
        for field_name in (
            "classification_counts",
            "inventory_entry_counts",
            "evidence_status_counts",
        ):
            value = getattr(self, field_name)
            if type(value) is not dict:
                raise TypeError(f"denominator {field_name} must be an exact dictionary")
            object.__setattr__(self, field_name, MappingProxyType(dict(value)))

    def to_canonical(self) -> dict[str, object]:
        return {
            "state": self.state.value,
            "capabilities": self.capabilities,
            "routes": self.routes,
            "exclusions": self.exclusions,
            "targets": self.targets,
            "lifecycle_phases": self.lifecycle_phases,
            "invariant_families": self.invariant_families,
            "applicability_cells": self.applicability_cells,
            "classification_counts": dict(self.classification_counts),
            "obligation_rows": self.obligation_rows,
            "unspecified_rows": self.unspecified_rows,
            "predicate_rows": self.predicate_rows,
            "stale_certificate_cells": self.stale_certificate_cells,
            "composition_registry_state": self.composition_registry_state.value,
            "composition_cells": self.composition_cells,
            "inventory_entry_counts": dict(self.inventory_entry_counts),
            "composition_pending_entries": self.composition_pending_entries,
            "evidence_status_counts": dict(self.evidence_status_counts),
            "historical_strict_release_closure": self.historical_strict_release_closure,
            "historical_minimum_release_evidence_cells": self.historical_minimum_release_evidence_cells,
            "coverage_ratio": self.coverage_ratio,
        }


@dataclass(frozen=True, slots=True)
class FlagsV1:
    integrity_ok: bool
    execution_complete: bool
    bounded_discovery_complete: bool
    formal_closure_complete: bool
    whole_economy_claim_allowed: bool

    def to_canonical(self) -> dict[str, object]:
        return {
            "integrity_ok": self.integrity_ok,
            "execution_complete": self.execution_complete,
            "bounded_discovery_complete": self.bounded_discovery_complete,
            "formal_closure_complete": self.formal_closure_complete,
            "whole_economy_claim_allowed": self.whole_economy_claim_allowed,
        }


def build_denominator(
    inventory: ObligationInventoryV1,
    registry: RegistryV1,
    statuses: Mapping[str, EvidenceStatusV1],
) -> DenominatorV1:
    classification_counts = inventory.classification_counts()
    incomplete = (
        classification_counts[ApplicabilityV1.APPLICABILITY_UNKNOWN.value] > 0
        or registry.applicability_state is not RegistrySectionStateV1.COMPLETE
        or registry.composition_state is not RegistrySectionStateV1.COMPLETE
        or len(inventory.entries) > 0
    )
    manifest = inventory.manifest
    return DenominatorV1(
        state=DenominatorStateV1.DENOMINATOR_INCOMPLETE
        if incomplete
        else DenominatorStateV1.DENOMINATOR_CLOSED_EXACT,
        capabilities=manifest.capability_count,
        routes=manifest.route_count,
        exclusions=manifest.exclusion_count,
        targets=len(manifest.targets),
        lifecycle_phases=len(LifecyclePhaseV1),
        invariant_families=len(InvariantFamilyV1),
        applicability_cells=len(inventory.cells),
        classification_counts=classification_counts,
        obligation_rows=len(inventory.rows),
        unspecified_rows=sum(1 for row in inventory.rows if row.predicate is None),
        predicate_rows=sum(1 for row in inventory.rows if row.predicate is not None),
        stale_certificate_cells=inventory.stale_certificate_cell_count,
        composition_registry_state=registry.composition_state,
        composition_cells=0,
        inventory_entry_counts=inventory.universe_counts(),
        composition_pending_entries=len(inventory.entries),
        evidence_status_counts=build_denominator_status_counts(statuses),
        historical_strict_release_closure=HISTORICAL_STRICT_RELEASE_CLOSURE_V1,
        historical_minimum_release_evidence_cells=HISTORICAL_MINIMUM_RELEASE_EVIDENCE_CELLS_V1,
        coverage_ratio=COVERAGE_RATIO_WITHHELD_V1,
    )


def build_flags(
    inventory: ObligationInventoryV1,
    registry: RegistryV1,
    results: Sequence[ObligationResultV1],
    statuses: Mapping[str, EvidenceStatusV1],
    denominator: DenominatorV1,
) -> FlagsV1:
    required_rows = tuple(
        row for row in inventory.rows if row.applicability is ApplicabilityV1.REQUIRED
    )
    predicate_rows = tuple(row for row in inventory.rows if row.predicate is not None)
    all_classified = (
        denominator.classification_counts[ApplicabilityV1.APPLICABILITY_UNKNOWN.value] == 0
    )
    every_required_has_predicate = all(row.predicate is not None for row in required_rows)
    every_predicate_has_runner = all(
        row.predicate is not None and bool(registry.runners_for(row.predicate.bad_predicate_id))
        for row in predicate_rows
    )
    expected = expected_result_keys(inventory, registry)
    observed = tuple(sorted((result.obligation_id, result.runner_id) for result in results))
    execution_complete = (
        all_classified
        and every_required_has_predicate
        and every_predicate_has_runner
        and bool(expected)
        and expected == observed
        and denominator.state is DenominatorStateV1.DENOMINATOR_CLOSED_EXACT
    )
    killed_all = all(result.killed_mutant_ids == result.required_mutant_ids for result in results)
    no_effect_observed = all(
        item.outcome is NoEffectOutcomeV1.UNCHANGED
        for result in results
        for item in result.no_effect_observations
    )
    bounded = (
        execution_complete
        and killed_all
        and no_effect_observed
        and all(statuses[row.obligation_id] in BOUNDED_STATUSES_V1 for row in required_rows)
    )
    formal = bounded and all(
        statuses[row.obligation_id] in CLOSURE_STATUSES_V1 for row in required_rows
    )
    return FlagsV1(
        integrity_ok=True,
        execution_complete=execution_complete,
        bounded_discovery_complete=bounded,
        formal_closure_complete=formal,
        whole_economy_claim_allowed=False,
    )


@dataclass(frozen=True, slots=True)
class PacketCoreV1:
    subject: ExactSubjectV1
    execution_premise: ExecutionPremiseV1
    source_bindings: tuple[BoundSourceV1, ...]
    cells_root: str
    rows_root: str
    universe_roots: Mapping[str, str]
    inventory_root: str
    denominator: DenominatorV1
    results: tuple[ObligationResultV1, ...]
    flags: FlagsV1
    claim_ceiling: str
    nonclaims: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.universe_roots) is not dict:
            raise TypeError("packet universe roots must be an exact dictionary")
        object.__setattr__(
            self,
            "universe_roots",
            MappingProxyType(dict(self.universe_roots)),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PACKET_SCHEMA_V1,
            "subject": self.subject.to_canonical(),
            "execution_premise": self.execution_premise.value,
            "source_bindings": [binding.to_canonical() for binding in self.source_bindings],
            "cells_root": self.cells_root,
            "rows_root": self.rows_root,
            "universe_roots": dict(self.universe_roots),
            "inventory_root": self.inventory_root,
            "denominator": self.denominator.to_canonical(),
            "results": [result.to_canonical() for result in self.results],
            "flags": self.flags.to_canonical(),
            "claim_ceiling": self.claim_ceiling,
            "nonclaims": list(self.nonclaims),
        }

    @property
    def receipt_root(self) -> str:
        return domain_root("wedc1-receipt-root", self.to_canonical())


def build_packet_core(
    *,
    subject: ExactSubjectV1,
    premise: ExecutionPremiseV1,
    bound: Mapping[str, BoundSourceV1],
    inventory: ObligationInventoryV1,
    registry: RegistryV1,
    results: Sequence[ObligationResultV1],
) -> PacketCoreV1:
    ordered_results = tuple(
        sorted(results, key=lambda result: (result.obligation_id, result.runner_id))
    )
    statuses = obligation_statuses(inventory, registry, ordered_results)
    denominator = build_denominator(inventory, registry, statuses)
    flags = build_flags(inventory, registry, ordered_results, statuses, denominator)
    return PacketCoreV1(
        subject=subject,
        execution_premise=premise,
        source_bindings=tuple(bound[pin.path] for pin in registry.source_pins),
        cells_root=inventory.cells_root(),
        rows_root=inventory.rows_root(),
        universe_roots=inventory.universe_roots(),
        inventory_root=inventory.inventory_root(),
        denominator=denominator,
        results=ordered_results,
        flags=flags,
        claim_ceiling=CLAIM_CEILING_V1,
        nonclaims=PACKET_NONCLAIMS_V1,
    )


@dataclass(frozen=True, slots=True)
class PacketV1:
    core: PacketCoreV1
    receipt_root: str
    telemetry: dict[str, object]

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PACKET_SCHEMA_V1,
            "canonical_core": self.core.to_canonical(),
            "receipt_root": self.receipt_root,
            "telemetry": dict(self.telemetry),
        }


_PACKET_FIELDS = ("schema", "canonical_core", "receipt_root", "telemetry")
_CORE_FIELDS = (
    "schema",
    "subject",
    "execution_premise",
    "source_bindings",
    "cells_root",
    "rows_root",
    "universe_roots",
    "inventory_root",
    "denominator",
    "results",
    "flags",
    "claim_ceiling",
    "nonclaims",
)
_TELEMETRY_FIELDS = ("generated_at", "duration_ms", "python_version", "stdout_previews")
_DENOMINATOR_FIELDS = tuple(DenominatorV1.__dataclass_fields__)
_DENOMINATOR_COUNT_FIELDS = (
    "capabilities",
    "routes",
    "exclusions",
    "targets",
    "lifecycle_phases",
    "invariant_families",
    "applicability_cells",
    "obligation_rows",
    "unspecified_rows",
    "predicate_rows",
    "stale_certificate_cells",
    "composition_cells",
    "composition_pending_entries",
    "historical_minimum_release_evidence_cells",
)
_FLAG_FIELDS = tuple(FlagsV1.__dataclass_fields__)


def _parse_binding(value: object, name: str) -> BoundSourceV1:
    raw = require_closed_object(value, ("pin", "head_binding"), name)
    return BoundSourceV1(
        parse_source_pin(raw["pin"], f"{name}.pin"),
        b"",
        cast(
            HeadBindingV1, require_enum(raw["head_binding"], HeadBindingV1, f"{name}.head_binding")
        ),
    )


def _int_map(value: object, name: str, keys: Sequence[str]) -> dict[str, int]:
    raw = require_closed_object(value, keys, name)
    return {key: require_int(raw[key], f"{name}.{key}", low=0, high=MAX_BOUND_V1) for key in keys}


def _parse_denominator(value: object, name: str) -> DenominatorV1:
    raw = require_closed_object(value, _DENOMINATOR_FIELDS, name)
    counts = {
        field: require_int(raw[field], f"{name}.{field}", low=0, high=MAX_BOUND_V1)
        for field in _DENOMINATOR_COUNT_FIELDS
    }
    return DenominatorV1(
        state=cast(
            DenominatorStateV1, require_enum(raw["state"], DenominatorStateV1, f"{name}.state")
        ),
        classification_counts=_int_map(
            raw["classification_counts"],
            f"{name}.classification_counts",
            [item.value for item in ApplicabilityV1],
        ),
        composition_registry_state=cast(
            RegistrySectionStateV1,
            require_enum(
                raw["composition_registry_state"],
                RegistrySectionStateV1,
                f"{name}.composition_registry_state",
            ),
        ),
        inventory_entry_counts=_int_map(
            raw["inventory_entry_counts"],
            f"{name}.inventory_entry_counts",
            [item.value for item in InventoryUniverseV1],
        ),
        evidence_status_counts=_int_map(
            raw["evidence_status_counts"],
            f"{name}.evidence_status_counts",
            [item.value for item in EvidenceStatusV1],
        ),
        historical_strict_release_closure=require_token(
            raw["historical_strict_release_closure"], f"{name}.historical_strict_release_closure"
        ),
        coverage_ratio=require_token(raw["coverage_ratio"], f"{name}.coverage_ratio"),
        **counts,
    )


def _parse_flags(value: object, name: str) -> FlagsV1:
    raw = require_closed_object(value, _FLAG_FIELDS, name)
    flags = FlagsV1(
        **{field: require_bool(raw[field], f"{name}.{field}") for field in _FLAG_FIELDS}
    )
    if flags.whole_economy_claim_allowed:
        raise reject(RejectCodeV1.WHOLE_ECONOMY_CLAIM_FORBIDDEN, name)
    return flags


def _parse_telemetry(value: object) -> dict[str, object]:
    raw = require_closed_object(value, _TELEMETRY_FIELDS, "packet.telemetry")
    previews = require_list(raw["stdout_previews"], "packet.telemetry.stdout_previews")[:32]
    return {
        "generated_at": require_string(
            raw["generated_at"], "packet.telemetry.generated_at", max_chars=64
        ),
        "duration_ms": require_int(
            raw["duration_ms"], "packet.telemetry.duration_ms", low=0, high=MAX_BOUND_V1
        ),
        "python_version": require_string(
            raw["python_version"], "packet.telemetry.python_version", max_chars=64
        ),
        "stdout_previews": [
            require_string(item, f"packet.telemetry.stdout_previews[{index}]")
            for index, item in enumerate(previews)
        ],
    }


def _parse_core(core_raw: Mapping[str, object]) -> PacketCoreV1:
    if core_raw["schema"] != PACKET_SCHEMA_V1:
        raise reject(RejectCodeV1.SCHEMA_MISMATCH, "canonical_core")
    universe_roots_raw = require_closed_object(
        core_raw["universe_roots"],
        [item.value for item in InventoryUniverseV1],
        "canonical_core.universe_roots",
    )
    claim_ceiling = require_token(core_raw["claim_ceiling"], "canonical_core.claim_ceiling")
    if claim_ceiling != CLAIM_CEILING_V1:
        raise reject(RejectCodeV1.CALLER_SUPPLIED_CEILING, claim_ceiling)
    nonclaims = tuple(
        require_string(item, f"canonical_core.nonclaims[{index}]")
        for index, item in enumerate(
            require_list(core_raw["nonclaims"], "canonical_core.nonclaims")
        )
    )
    if nonclaims != PACKET_NONCLAIMS_V1:
        raise reject(RejectCodeV1.NONCLAIMS_MISMATCH, "canonical_core.nonclaims")
    return PacketCoreV1(
        subject=parse_subject(core_raw["subject"], "canonical_core.subject"),
        execution_premise=cast(
            ExecutionPremiseV1,
            require_enum(
                core_raw["execution_premise"],
                ExecutionPremiseV1,
                "canonical_core.execution_premise",
            ),
        ),
        source_bindings=tuple(
            _parse_binding(item, f"canonical_core.source_bindings[{index}]")
            for index, item in enumerate(
                require_list(core_raw["source_bindings"], "canonical_core.source_bindings")
            )
        ),
        cells_root=require_root(core_raw["cells_root"], "canonical_core.cells_root"),
        rows_root=require_root(core_raw["rows_root"], "canonical_core.rows_root"),
        universe_roots={
            key: require_root(universe_roots_raw[key], f"canonical_core.universe_roots.{key}")
            for key in sorted(universe_roots_raw)
        },
        inventory_root=require_root(core_raw["inventory_root"], "canonical_core.inventory_root"),
        denominator=_parse_denominator(core_raw["denominator"], "canonical_core.denominator"),
        results=tuple(
            parse_result(item, f"canonical_core.results[{index}]")
            for index, item in enumerate(
                require_list(core_raw["results"], "canonical_core.results")
            )
        ),
        flags=_parse_flags(core_raw["flags"], "canonical_core.flags"),
        claim_ceiling=claim_ceiling,
        nonclaims=nonclaims,
    )


def parse_packet(data: bytes) -> PacketV1:
    """Parse a discovery packet under closed rules and recompute its receipt root."""

    top = require_object(
        decode_strict_json(data, name="packet", max_bytes=MAX_PACKET_BYTES_V1), "packet"
    )
    schema = top.get("schema")
    if schema in LEGACY_BRIDGE_SCHEMAS_V1:
        raise reject(RejectCodeV1.LEGACY_BRIDGE_RECEIPT_REJECTED, str(schema))
    if schema != PACKET_SCHEMA_V1:
        raise reject(RejectCodeV1.SCHEMA_MISMATCH, "packet")
    raw = require_closed_object(top, _PACKET_FIELDS, "packet")
    core_raw = require_closed_object(raw["canonical_core"], _CORE_FIELDS, "canonical_core")
    if _FORBIDDEN_PACKET_TEXT_RE.search(canonical_bytes(core_raw).decode("utf-8")) is not None:
        raise reject(RejectCodeV1.PERCENTAGE_FORBIDDEN, "canonical_core")
    core = _parse_core(core_raw)
    receipt_root = require_root(raw["receipt_root"], "packet.receipt_root")
    if receipt_root != core.receipt_root:
        raise reject(RejectCodeV1.RECEIPT_ROOT_MISMATCH, receipt_root)
    return PacketV1(
        core=core, receipt_root=receipt_root, telemetry=_parse_telemetry(raw["telemetry"])
    )


def _check_packet_floor(denominator: DenominatorV1) -> None:
    if denominator.applicability_cells == 0 or denominator.targets == 0:
        raise reject(RejectCodeV1.DENOMINATOR_EMPTY, "denominator")
    if (
        denominator.capabilities < V1_FLOOR_CAPABILITIES
        or denominator.routes < V1_FLOOR_ROUTES
        or denominator.exclusions < V1_FLOOR_EXCLUSIONS
        or denominator.applicability_cells < V1_FLOOR_APPLICABILITY_CELLS
    ):
        raise reject(
            RejectCodeV1.DENOMINATOR_BELOW_FLOOR, "packet denominator below the hard V1 minimum"
        )


def verify_packet(
    packet: PacketV1,
    *,
    subject: ExactSubjectV1,
    bound: Mapping[str, BoundSourceV1],
    inventory: ObligationInventoryV1,
    registry: RegistryV1,
    artifacts: Mapping[str, OwnedSourceV1],
    expected_premise: ExecutionPremiseV1,
    replayed_observations: Mapping[str, ExecutionObservationV1],
) -> PacketCoreV1:
    """Independently rebuild the canonical core and require exact equality."""

    core = packet.core
    if core.subject.registry_sha256 != registry.sha256:
        raise reject(RejectCodeV1.REGISTRY_STALE, core.subject.registry_sha256)
    if core.subject.commit != subject.commit or core.subject.tree != subject.tree:
        raise reject(RejectCodeV1.SUBJECT_MISMATCH, "commit or tree")
    if core.subject != subject:
        raise reject(RejectCodeV1.SUBJECT_MISMATCH, "subject roots")
    expected_bindings = tuple(bound[pin.path] for pin in registry.source_pins)
    observed_binding_rows = tuple(
        (binding.pin, binding.head_binding) for binding in core.source_bindings
    )
    expected_binding_rows = tuple(
        (binding.pin, binding.head_binding) for binding in expected_bindings
    )
    if observed_binding_rows != expected_binding_rows:
        raise reject(RejectCodeV1.SOURCE_PINS_ROOT_MISMATCH, "source bindings")
    if core.execution_premise is not expected_premise:
        raise reject(RejectCodeV1.FLAGS_MISMATCH, "execution premise")
    if (
        core.cells_root != inventory.cells_root()
        or core.rows_root != inventory.rows_root()
        or core.universe_roots != inventory.universe_roots()
        or core.inventory_root != inventory.inventory_root()
    ):
        raise reject(RejectCodeV1.INVENTORY_ROOT_MISMATCH, "inventory roots")
    _check_packet_floor(core.denominator)
    verify_results(
        core.results,
        inventory=inventory,
        registry=registry,
        subject=subject,
        artifacts=artifacts,
        replayed_observations=replayed_observations,
    )
    for result in core.results:
        if result.execution_premise is not core.execution_premise:
            raise reject(RejectCodeV1.FLAGS_MISMATCH, f"result premise {result.obligation_id}")
    statuses = obligation_statuses(inventory, registry, core.results)
    denominator = build_denominator(inventory, registry, statuses)
    if core.denominator != denominator:
        raise reject(RejectCodeV1.DENOMINATOR_MISMATCH, "recomputed denominator differs")
    flags = build_flags(inventory, registry, core.results, statuses, denominator)
    if core.flags != flags:
        raise reject(RejectCodeV1.FLAGS_MISMATCH, "recomputed flags differ")
    expected = PacketCoreV1(
        subject=subject,
        execution_premise=expected_premise,
        source_bindings=tuple(
            BoundSourceV1(binding.pin, b"", binding.head_binding) for binding in expected_bindings
        ),
        cells_root=inventory.cells_root(),
        rows_root=inventory.rows_root(),
        universe_roots=inventory.universe_roots(),
        inventory_root=inventory.inventory_root(),
        denominator=denominator,
        results=core.results,
        flags=flags,
        claim_ceiling=CLAIM_CEILING_V1,
        nonclaims=PACKET_NONCLAIMS_V1,
    )
    if canonical_bytes(expected.to_canonical()) != canonical_bytes(core.to_canonical()):
        raise reject(RejectCodeV1.RECEIPT_CORE_MISMATCH, "canonical core bytes differ")
    if expected.receipt_root != packet.receipt_root:
        raise reject(RejectCodeV1.RECEIPT_ROOT_MISMATCH, packet.receipt_root)
    return expected
