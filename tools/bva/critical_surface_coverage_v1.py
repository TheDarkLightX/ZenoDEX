"""Closed manifest validator for critical value-moving BVA evidence."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, cast

from tools.bva.critical_surface_coverage_common_v1 import (
    CoverageManifestError,
    exact_keys,
    load_json_object,
    object_value,
    relative_repo_path,
    repo_file,
    require,
    string_list,
)
from tools.bva.critical_surface_source_binding_v1 import check_source_binding

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = Path(__file__).with_name("critical_surface_coverage_v1.json")
SCHEMA = "zenodex/critical-bva-coverage/v1"
REQUIRED_BOUNDARY_CLASSES = (
    "numeric_lower_triplet",
    "numeric_upper_triplet",
    "exact_type_aliases",
    "absent_null_malformed",
    "empty_singleton_max_size",
    "cross_field_mixed_predicates",
    "reject_is_noop",
    "runtime_spec_parity",
    "stateful_sequence",
    "resource_bounds",
)
MANDATORY_SURFACES = (
    "spot_swap_and_fees",
    "liquidity",
    "perpetuals",
    "zusd",
    "oracle",
    "zeno_ledger_and_proof",
    "keys",
    "fire_and_zenocover",
)
TOP_LEVEL_KEYS = frozenset(
    {"schema", "production_complete", "notes", "required_boundary_classes", "surfaces"}
)
SURFACE_KEYS = frozenset(
    {
        "id",
        "status",
        "inventory_complete",
        "commands",
        "authoritative_fields",
        "covered_boundary_classes",
        "missing_boundary_classes",
        "not_applicable_boundary_classes",
        "not_applicable_reasons",
        "evidence",
        "action_parameters",
        "source_model",
    }
)


def _partition(
    surface: Mapping[str, Any],
    *,
    surface_id: str,
) -> tuple[set[str], set[str], set[str]]:
    covered = set(
        string_list(
            surface.get("covered_boundary_classes"),
            context=f"{surface_id}.covered_boundary_classes",
            allow_empty=True,
        )
    )
    missing = set(
        string_list(
            surface.get("missing_boundary_classes"),
            context=f"{surface_id}.missing_boundary_classes",
            allow_empty=True,
        )
    )
    not_applicable = set(
        string_list(
            surface.get("not_applicable_boundary_classes"),
            context=f"{surface_id}.not_applicable_boundary_classes",
            allow_empty=True,
        )
    )
    require(not covered & missing, f"{surface_id}: covered/missing overlap")
    require(not covered & not_applicable, f"{surface_id}: covered/not-applicable overlap")
    require(not missing & not_applicable, f"{surface_id}: missing/not-applicable overlap")
    require(
        covered | missing | not_applicable == set(REQUIRED_BOUNDARY_CLASSES),
        f"{surface_id}: boundary-class partition incomplete",
    )
    return covered, missing, not_applicable


def _check_not_applicable_reasons(
    surface: Mapping[str, Any],
    *,
    surface_id: str,
    not_applicable: set[str],
) -> None:
    reasons = object_value(
        surface.get("not_applicable_reasons"),
        context=f"{surface_id}.not_applicable_reasons",
    )
    require(set(reasons) == not_applicable, f"{surface_id}: not-applicable reasons mismatch")
    require(
        all(type(reason) is str and bool(reason) for reason in reasons.values()),
        f"{surface_id}: not-applicable reasons must be non-empty strings",
    )


def _check_evidence(
    surface: Mapping[str, Any],
    *,
    repo_root: Path,
    surface_id: str,
) -> None:
    evidence = string_list(surface.get("evidence"), context=f"{surface_id}.evidence")
    for raw_path in evidence:
        relative = relative_repo_path(raw_path, context=f"{surface_id}.evidence")
        require(relative.parts[0] == "tests", f"{surface_id}: evidence must live under tests")
        require(relative.suffix in {".py", ".json"}, f"{surface_id}: unsupported evidence type")
        repo_file(repo_root, relative, context=f"{surface_id}.evidence")


def _check_surface(
    surface: Mapping[str, Any],
    *,
    repo_root: Path,
    expected_id: str,
) -> bool:
    exact_keys(surface, SURFACE_KEYS, context=expected_id)
    require(surface.get("id") == expected_id, f"surface order or identity drift at {expected_id}")
    status = surface.get("status")
    require(status in {"partial", "complete"}, f"{expected_id}: invalid status")
    inventory_complete = surface.get("inventory_complete")
    require(type(inventory_complete) is bool, f"{expected_id}: inventory_complete must be bool")
    commands = string_list(surface.get("commands"), context=f"{expected_id}.commands")
    fields = string_list(
        surface.get("authoritative_fields"),
        context=f"{expected_id}.authoritative_fields",
    )
    _, missing, not_applicable = _partition(surface, surface_id=expected_id)
    _check_not_applicable_reasons(
        surface,
        surface_id=expected_id,
        not_applicable=not_applicable,
    )
    _check_evidence(surface, repo_root=repo_root, surface_id=expected_id)
    has_source = "source_model" in surface
    has_parameters = "action_parameters" in surface
    require(
        has_source is has_parameters,
        f"{expected_id}: source model and action parameters must appear together",
    )
    if has_source:
        check_source_binding(
            surface,
            repo_root=repo_root,
            surface_id=expected_id,
            commands=commands,
            authoritative_fields=fields,
        )
    if status == "partial":
        return False
    require(
        inventory_complete is True, f"{expected_id}: complete status requires complete inventory"
    )
    require(not missing, f"{expected_id}: complete status cannot retain missing classes")
    require(
        has_source, f"{expected_id}: complete status requires source-bound finite model evidence"
    )
    return True


def check_manifest(
    path: Path = DEFAULT_MANIFEST,
    *,
    require_complete: bool = False,
    repo_root: Path = REPO_ROOT,
) -> dict[str, object]:
    manifest = load_json_object(path, context=str(path))
    exact_keys(manifest, TOP_LEVEL_KEYS, context="manifest")
    require(manifest.get("schema") == SCHEMA, "schema mismatch")
    require(
        type(manifest.get("notes")) is str and bool(manifest.get("notes")),
        "notes must be a non-empty string",
    )
    required = string_list(
        manifest.get("required_boundary_classes"),
        context="required_boundary_classes",
    )
    require(
        tuple(required) == REQUIRED_BOUNDARY_CLASSES,
        "required boundary class inventory drift",
    )
    raw_surfaces = manifest.get("surfaces")
    require(type(raw_surfaces) is list, "surfaces: expected list")
    surfaces = cast(list[object], raw_surfaces)
    require(len(surfaces) == len(MANDATORY_SURFACES), "mandatory surface inventory mismatch")
    complete = [
        _check_surface(
            object_value(raw, context=f"surfaces[{index}]"),
            repo_root=repo_root,
            expected_id=surface_id,
        )
        for index, (raw, surface_id) in enumerate(zip(surfaces, MANDATORY_SURFACES, strict=True))
    ]
    derived_complete = all(complete)
    require(type(manifest.get("production_complete")) is bool, "production_complete must be bool")
    require(
        manifest.get("production_complete") is derived_complete,
        "production_complete does not match derived status",
    )
    incomplete = [
        surface_id
        for surface_id, is_complete in zip(MANDATORY_SURFACES, complete, strict=True)
        if not is_complete
    ]
    if require_complete:
        require(
            derived_complete,
            "critical BVA coverage incomplete: " + ",".join(incomplete),
        )
    return {
        "ok": True,
        "schema": SCHEMA,
        "production_complete": derived_complete,
        "surface_count": len(surfaces),
        "incomplete_surfaces": incomplete,
    }


__all__ = [
    "CoverageManifestError",
    "DEFAULT_MANIFEST",
    "REQUIRED_BOUNDARY_CLASSES",
    "check_manifest",
]
