from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping

from .cantor_region_backend_invariance_receipt import CANTOR_REGION_BACKEND_INVARIANCE_RECEIPT_SCHEMA
from .cantor_shapeforge_bridge_report import (
    SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA,
    build_cantor_shapeforge_bridge_report,
)


def _is_nonempty_string(value: object) -> bool:
    return isinstance(value, str) and bool(value)


def _load_json_object(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"JSON payload must be an object: {path}")
    return data


def _safe_world_model_load_error(exc: Exception) -> str:
    if isinstance(exc, (json.JSONDecodeError, ValueError)):
        detail = " ".join(str(exc).split())
        return detail[:200] or type(exc).__name__
    if isinstance(exc, OSError):
        return f"world_model_load_failed:{type(exc).__name__}"
    return f"world_model_load_internal_error:{type(exc).__name__}"


def _slice_map(world_model: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    out: dict[str, Mapping[str, Any]] = {}
    for slice_obj in world_model.get("slices", []):
        if not isinstance(slice_obj, Mapping):
            continue
        slice_id = slice_obj.get("slice_id")
        if isinstance(slice_id, str):
            out[slice_id] = slice_obj
    return out


def _has_evidence(slice_obj: Mapping[str, Any], claim: str, evidence_class: str, source: str) -> bool:
    for item in slice_obj.get("evidence", []):
        if not isinstance(item, Mapping):
            continue
        if item.get("claim") == claim and item.get("class") == evidence_class and item.get("source") == source:
            return True
    return False


def verify_cantor_shapeforge_bridge_report_payload(
    payload: object,
    *,
    require_current: bool = False,
) -> tuple[bool, str | None]:
    if not isinstance(payload, Mapping):
        return False, "bridge payload must be an object"
    if payload.get("schema") != SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA:
        return False, "unsupported bridge schema"

    world_model_path = payload.get("world_model_path")
    world_model_id = payload.get("world_model_id")
    bundle_schema = payload.get("bundle_schema")
    backend_invariance = payload.get("backend_invariance")
    mapped_surfaces = payload.get("mapped_surfaces")
    unmapped_surfaces = payload.get("unmapped_surfaces")

    if not _is_nonempty_string(world_model_path):
        return False, "world_model_path must be a nonempty string"
    if not _is_nonempty_string(world_model_id):
        return False, "world_model_id must be a nonempty string"
    if bundle_schema != "zenodex/cantor-region-assurance-bundle/v1":
        return False, "unexpected bundle schema"
    if not isinstance(backend_invariance, Mapping):
        return False, "backend_invariance must be an object"
    if not isinstance(mapped_surfaces, list):
        return False, "mapped_surfaces must be a list"
    if not isinstance(unmapped_surfaces, list):
        return False, "unmapped_surfaces must be a list"
    if payload.get("mapped_surface_count") != len(mapped_surfaces):
        return False, "mapped_surface_count mismatch"
    if payload.get("unmapped_surface_count") != len(unmapped_surfaces):
        return False, "unmapped_surface_count mismatch"

    if backend_invariance.get("schema") != CANTOR_REGION_BACKEND_INVARIANCE_RECEIPT_SCHEMA:
        return False, "unexpected backend invariance schema"
    if backend_invariance.get("payload_equal") is not True:
        return False, "backend invariance must report equal payloads"

    world_model_file = Path(str(world_model_path))
    if not world_model_file.exists():
        return False, "world_model_path does not exist"
    try:
        world_model = _load_json_object(world_model_file)
    except Exception as exc:
        return False, _safe_world_model_load_error(exc)
    if world_model.get("world_model_id") != world_model_id:
        return False, "world model id mismatch"

    slice_map = _slice_map(world_model)
    mapped_names: set[str] = set()
    for surface in mapped_surfaces:
        if not isinstance(surface, Mapping):
            return False, "mapped surfaces must be objects"
        surface_name = surface.get("surface_name")
        primary_slice_id = surface.get("primary_slice_id")
        current_slice_status = surface.get("current_slice_status")
        partition_total = surface.get("partition_total")
        region_names = surface.get("region_names")
        refinement_pairs = surface.get("refinement_pairs")
        disjoint_pairs = surface.get("disjoint_pairs")
        suggested_sources = surface.get("suggested_sources")
        suggested_evidence = surface.get("suggested_evidence")
        related_slice_ids = surface.get("related_slice_ids")

        if not _is_nonempty_string(surface_name):
            return False, "mapped surface_name must be nonempty"
        if surface_name in mapped_names:
            return False, f"duplicate mapped surface: {surface_name!r}"
        mapped_names.add(str(surface_name))
        if not _is_nonempty_string(primary_slice_id):
            return False, f"mapped surface {surface_name!r} missing primary_slice_id"
        if primary_slice_id not in slice_map:
            return False, f"mapped surface {surface_name!r} references unknown slice"
        slice_obj = slice_map[primary_slice_id]
        if current_slice_status != slice_obj.get("status"):
            return False, f"mapped surface {surface_name!r} status mismatch"
        if partition_total is not True:
            return False, f"mapped surface {surface_name!r} partition_total must be true"
        if not isinstance(region_names, list) or not region_names:
            return False, f"mapped surface {surface_name!r} region_names must be non-empty"
        if not isinstance(refinement_pairs, list):
            return False, f"mapped surface {surface_name!r} refinement_pairs must be a list"
        if not isinstance(disjoint_pairs, list):
            return False, f"mapped surface {surface_name!r} disjoint_pairs must be a list"
        if not isinstance(suggested_sources, list) or not suggested_sources:
            return False, f"mapped surface {surface_name!r} suggested_sources must be non-empty"
        if not isinstance(suggested_evidence, list) or not suggested_evidence:
            return False, f"mapped surface {surface_name!r} suggested_evidence must be non-empty"
        if not isinstance(related_slice_ids, list):
            return False, f"mapped surface {surface_name!r} related_slice_ids must be a list"

        slice_sources = set(slice_obj.get("sources", [])) if isinstance(slice_obj.get("sources"), list) else set()
        for source in suggested_sources:
            if not _is_nonempty_string(source):
                return False, f"mapped surface {surface_name!r} has invalid suggested source"
            if source not in slice_sources:
                return False, f"mapped surface {surface_name!r} suggested source missing from world model"

        for related_slice_id in related_slice_ids:
            if not _is_nonempty_string(related_slice_id):
                return False, f"mapped surface {surface_name!r} has invalid related slice"
            if related_slice_id not in slice_map:
                return False, f"mapped surface {surface_name!r} references unknown related slice"

        for item in suggested_evidence:
            if not isinstance(item, Mapping):
                return False, f"mapped surface {surface_name!r} suggested_evidence entries must be objects"
            claim = item.get("claim")
            evidence_class = item.get("evidence_class")
            source = item.get("source")
            if not (_is_nonempty_string(claim) and _is_nonempty_string(evidence_class) and _is_nonempty_string(source)):
                return False, f"mapped surface {surface_name!r} suggested_evidence entries must be non-empty"
            if not _has_evidence(slice_obj, str(claim), str(evidence_class), str(source)):
                return False, f"mapped surface {surface_name!r} suggested evidence missing from world model"

    for surface in unmapped_surfaces:
        if not isinstance(surface, Mapping):
            return False, "unmapped surfaces must be objects"
        if not _is_nonempty_string(surface.get("surface_name")):
            return False, "unmapped surface_name must be nonempty"
        if not _is_nonempty_string(surface.get("reason")):
            return False, "unmapped surface reason must be nonempty"
        if not _is_nonempty_string(surface.get("suggested_improvement_target")):
            return False, "unmapped surface suggested_improvement_target must be nonempty"
        suggested_sources = surface.get("suggested_sources")
        if not isinstance(suggested_sources, list) or not suggested_sources:
            return False, "unmapped surface suggested_sources must be non-empty"

    if require_current:
        expected = build_cantor_shapeforge_bridge_report(world_model_path=world_model_file).to_dict()
        if dict(payload) != expected:
            return False, "bridge payload differs from current bridge construction"

    return True, None
