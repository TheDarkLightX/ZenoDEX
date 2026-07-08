#!/usr/bin/env python3
"""Validate ShapeForge JSON artifacts.

This validator is intentionally lightweight and fail-closed:
- required fields must exist
- ids must be unique
- enumerated values must be declared or supported
- cross references must resolve
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

WORLD_MODEL_SCHEMA = "shapeforge/world-model-seed/v1"
NEGATIVE_KNOWLEDGE_SCHEMA = "shapeforge/negative-knowledge-seed/v1"
TARGET_SHAPES_SCHEMA = "shapeforge/target-shapes-seed/v1"

WORLD_MODEL_TOP_LEVEL_KEYS = {
    "schema",
    "repo_root",
    "world_model_id",
    "description",
    "evidence_classes",
    "slice_axes",
    "slices",
    "cross_slice_invariants",
    "scenario_transforms",
}

SLICE_KEYS = {
    "slice_id",
    "status",
    "description",
    "candidate_family",
    "state_vars",
    "operators",
    "guards",
    "observables",
    "canonical_keys",
    "evidence",
    "sources",
    "known_gaps",
    "improvement_targets",
}

SCENARIO_KEYS = {
    "scenario_id",
    "slice_id",
    "axis",
    "perturbation",
    "expected_effects",
    "improvement_target",
    "evidence_required",
    "status_if_unproved",
}

NEGATIVE_TOP_LEVEL_KEYS = {
    "schema",
    "repo_root",
    "context_key",
    "world_model_id",
    "world_model_path",
    "description",
    "records",
}

TARGET_TOP_LEVEL_KEYS = {
    "schema",
    "repo_root",
    "world_model_id",
    "world_model_path",
    "negative_knowledge_path",
    "description",
    "evidence_classes",
    "target_shapes",
}

TARGET_SHAPE_KEYS = {
    "target_shape_id",
    "name",
    "description",
    "required",
    "clauses",
    "sources",
}

TARGET_CLAUSE_KEYS = {
    "clause_id",
    "label",
    "target_evidence_class",
    "support_mode",
    "requirements",
    "blocked_by_hypotheses",
    "notes",
}

TARGET_REQUIREMENT_KEYS = {
    "kind",
    "slice_id",
    "min_status",
    "invariant_id",
}

NEGATIVE_RECORD_KEYS = {
    "hypothesis_id",
    "context_key",
    "world_model_id",
    "slice_id",
    "scenario_id",
    "axis",
    "improvement_target",
    "negative_kind",
    "status",
    "claim",
    "current_evidence_class",
    "target_evidence_class",
    "preconditions",
    "trigger",
    "source_surfaces",
    "related_invariants",
    "evidence_or_falsifier",
    "replacement_claim",
    "replay_pointer",
}

ALLOWED_AXES = {
    "state_var",
    "operator",
    "guard",
    "observable",
    "canonical_key",
    "evidence",
}

ALLOWED_EVIDENCE_CLASSES = {
    "proved",
    "contract",
    "implemented",
    "tested_discovery",
    "hypothesis",
}

ALLOWED_NEGATIVE_KINDS = {
    "falsified",
    "blocked_promotion",
    "scope_boundary",
    "implementation_accident",
    "missing_guard",
    "missing_certificate",
    "disputed_source",
    "unknown",
}

ALLOWED_NEGATIVE_STATUSES = {
    "proposed",
    "falsified",
    "blocked",
    "supported",
    "proved",
    "narrowed",
}

ALLOWED_TARGET_SUPPORT_MODES = {
    "all_of",
    "any_of",
}

ALLOWED_TARGET_REQUIREMENT_KINDS = {
    "slice_status_at_least",
    "cross_invariant_present",
}


def _ids_unique(items: list[dict], key: str) -> bool:
    seen: set[str] = set()
    for item in items:
        value = item.get(key)
        if not isinstance(value, str) or not value:
            return False
        if value in seen:
            return False
        seen.add(value)
    return True


def _require(errors: list[str], condition: bool, message: str) -> None:
    if not condition:
        errors.append(message)


def _is_nonempty_string(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _is_nonempty_string_list(value: object) -> bool:
    return isinstance(value, list) and bool(value) and all(_is_nonempty_string(item) for item in value)


def _resolve_linked_path(base_artifact: Path, linked_path: str) -> Path | None:
    raw = Path(linked_path)
    if raw.is_absolute():
        return raw if raw.exists() else None

    candidates: list[Path] = [(Path.cwd() / raw).resolve()]
    candidates.extend((ancestor / raw).resolve() for ancestor in base_artifact.parents)

    seen: set[Path] = set()
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)
        if candidate.exists():
            return candidate
    return None


def validate_world_model_data(data: dict, path: Path) -> list[str]:
    errors: list[str] = []

    _require(errors, WORLD_MODEL_TOP_LEVEL_KEYS.issubset(data.keys()), f"{path}: missing top-level keys")
    _require(
        errors,
        data.get("schema") == WORLD_MODEL_SCHEMA,
        f"{path}: schema must equal {WORLD_MODEL_SCHEMA}",
    )

    evidence_classes = data.get("evidence_classes")
    slice_axes = data.get("slice_axes")
    slices = data.get("slices")
    scenarios = data.get("scenario_transforms")

    _require(errors, isinstance(evidence_classes, list) and evidence_classes, f"{path}: evidence_classes must be a nonempty list")
    _require(errors, isinstance(slice_axes, list) and slice_axes, f"{path}: slice_axes must be a nonempty list")
    _require(errors, isinstance(slices, list) and slices, f"{path}: slices must be a nonempty list")
    _require(errors, isinstance(scenarios, list), f"{path}: scenario_transforms must be a list")

    if errors:
        return errors

    evidence_class_set = set(evidence_classes)
    axis_set = set(slice_axes)
    _require(errors, axis_set <= ALLOWED_AXES, f"{path}: slice_axes contains unsupported values")
    _require(errors, _ids_unique(slices, "slice_id"), f"{path}: slice ids must be unique and nonempty")

    slice_ids = {slice_obj["slice_id"] for slice_obj in slices if isinstance(slice_obj, dict) and "slice_id" in slice_obj}

    for slice_obj in slices:
        if not isinstance(slice_obj, dict):
            errors.append(f"{path}: each slice must be an object")
            continue
        sid = slice_obj.get("slice_id", "<missing>")
        _require(errors, SLICE_KEYS.issubset(slice_obj.keys()), f"{path}: slice {sid} missing required keys")
        _require(errors, slice_obj.get("status") in evidence_class_set, f"{path}: slice {sid} has unknown status")

        for list_key in ("state_vars", "operators", "guards", "observables", "canonical_keys", "evidence", "sources", "known_gaps", "improvement_targets"):
            _require(errors, isinstance(slice_obj.get(list_key), list), f"{path}: slice {sid} field {list_key} must be a list")

        for field, key in (
            ("state_vars", "id"),
            ("operators", "id"),
            ("guards", "id"),
            ("observables", "id"),
            ("canonical_keys", "id"),
        ):
            items = slice_obj.get(field, [])
            if items:
                _require(errors, _ids_unique(items, key), f"{path}: slice {sid} field {field} must have unique ids")

        for evidence_item in slice_obj.get("evidence", []):
            if not isinstance(evidence_item, dict):
                errors.append(f"{path}: slice {sid} evidence entries must be objects")
                continue
            _require(errors, evidence_item.get("class") in evidence_class_set, f"{path}: slice {sid} has evidence with unknown class")
            _require(errors, _is_nonempty_string(evidence_item.get("claim")), f"{path}: slice {sid} evidence must include a nonempty claim")
            _require(errors, _is_nonempty_string(evidence_item.get("source")), f"{path}: slice {sid} evidence must include a nonempty source")

    _require(errors, _ids_unique(scenarios, "scenario_id"), f"{path}: scenario ids must be unique and nonempty")

    for scenario in scenarios:
        if not isinstance(scenario, dict):
            errors.append(f"{path}: each scenario must be an object")
            continue
        scenario_id = scenario.get("scenario_id", "<missing>")
        _require(errors, SCENARIO_KEYS.issubset(scenario.keys()), f"{path}: scenario {scenario_id} missing required keys")
        _require(errors, scenario.get("slice_id") in slice_ids, f"{path}: scenario {scenario_id} references unknown slice")
        _require(errors, scenario.get("axis") in axis_set, f"{path}: scenario {scenario_id} uses undeclared axis")
        _require(errors, isinstance(scenario.get("expected_effects"), list) and scenario["expected_effects"], f"{path}: scenario {scenario_id} must list expected effects")
        _require(errors, isinstance(scenario.get("evidence_required"), list) and scenario["evidence_required"], f"{path}: scenario {scenario_id} must declare evidence_required")
        for cls in scenario.get("evidence_required", []):
            _require(errors, cls in evidence_class_set, f"{path}: scenario {scenario_id} uses unknown evidence class {cls}")

    return errors


def validate_negative_knowledge_data(data: dict, path: Path) -> list[str]:
    errors: list[str] = []

    _require(errors, NEGATIVE_TOP_LEVEL_KEYS.issubset(data.keys()), f"{path}: missing top-level keys")
    _require(
        errors,
        data.get("schema") == NEGATIVE_KNOWLEDGE_SCHEMA,
        f"{path}: schema must equal {NEGATIVE_KNOWLEDGE_SCHEMA}",
    )
    _require(errors, _is_nonempty_string(data.get("repo_root")), f"{path}: repo_root must be a nonempty string")
    _require(errors, _is_nonempty_string(data.get("context_key")), f"{path}: context_key must be a nonempty string")
    _require(errors, _is_nonempty_string(data.get("world_model_id")), f"{path}: world_model_id must be a nonempty string")
    _require(errors, _is_nonempty_string(data.get("world_model_path")), f"{path}: world_model_path must be a nonempty string")
    _require(errors, _is_nonempty_string(data.get("description")), f"{path}: description must be a nonempty string")

    records = data.get("records")
    _require(errors, isinstance(records, list) and records, f"{path}: records must be a nonempty list")
    if errors:
        return errors

    _require(errors, _ids_unique(records, "hypothesis_id"), f"{path}: hypothesis ids must be unique and nonempty")

    context_key = data["context_key"]
    world_model_id = data["world_model_id"]
    world_model_path = data["world_model_path"]
    resolved_world_model_path = _resolve_linked_path(path, world_model_path)
    _require(errors, resolved_world_model_path is not None, f"{path}: linked world_model_path could not be resolved")

    linked_world_model: dict | None = None
    linked_slice_ids: set[str] = set()
    linked_scenario_ids: set[str] = set()
    linked_invariant_ids: set[str] = set()

    if resolved_world_model_path is not None:
        linked_errors = validate_artifact(resolved_world_model_path)
        if linked_errors:
            for linked_error in linked_errors:
                errors.append(f"{path}: linked world model invalid: {linked_error}")
        else:
            linked_world_model = json.loads(resolved_world_model_path.read_text())
            _require(
                errors,
                linked_world_model.get("world_model_id") == world_model_id,
                f"{path}: linked world model id must match top-level world_model_id",
            )
            linked_slice_ids = {
                slice_obj["slice_id"]
                for slice_obj in linked_world_model.get("slices", [])
                if isinstance(slice_obj, dict) and isinstance(slice_obj.get("slice_id"), str)
            }
            linked_scenario_ids = {
                scenario["scenario_id"]
                for scenario in linked_world_model.get("scenario_transforms", [])
                if isinstance(scenario, dict) and isinstance(scenario.get("scenario_id"), str)
            }
            linked_invariant_ids = {
                invariant["id"]
                for invariant in linked_world_model.get("cross_slice_invariants", [])
                if isinstance(invariant, dict) and isinstance(invariant.get("id"), str)
            }

    for record in records:
        if not isinstance(record, dict):
            errors.append(f"{path}: each record must be an object")
            continue

        hypothesis_id = record.get("hypothesis_id", "<missing>")
        _require(errors, NEGATIVE_RECORD_KEYS.issubset(record.keys()), f"{path}: record {hypothesis_id} missing required keys")
        _require(errors, record.get("context_key") == context_key, f"{path}: record {hypothesis_id} must match top-level context_key")
        _require(errors, record.get("world_model_id") == world_model_id, f"{path}: record {hypothesis_id} must match top-level world_model_id")
        _require(errors, _is_nonempty_string(record.get("slice_id")), f"{path}: record {hypothesis_id} must have a nonempty slice_id")
        scenario_id = record.get("scenario_id")
        _require(errors, scenario_id is None or _is_nonempty_string(scenario_id), f"{path}: record {hypothesis_id} has invalid scenario_id")
        _require(errors, record.get("axis") in ALLOWED_AXES, f"{path}: record {hypothesis_id} uses unsupported axis")
        _require(errors, record.get("negative_kind") in ALLOWED_NEGATIVE_KINDS, f"{path}: record {hypothesis_id} uses unsupported negative_kind")
        _require(errors, record.get("status") in ALLOWED_NEGATIVE_STATUSES, f"{path}: record {hypothesis_id} uses unsupported status")
        _require(errors, record.get("current_evidence_class") in ALLOWED_EVIDENCE_CLASSES, f"{path}: record {hypothesis_id} uses unsupported current_evidence_class")
        _require(errors, record.get("target_evidence_class") in ALLOWED_EVIDENCE_CLASSES, f"{path}: record {hypothesis_id} uses unsupported target_evidence_class")

        for key in (
            "improvement_target",
            "claim",
            "trigger",
            "evidence_or_falsifier",
            "replay_pointer",
        ):
            _require(errors, _is_nonempty_string(record.get(key)), f"{path}: record {hypothesis_id} field {key} must be a nonempty string")

        _require(errors, _is_nonempty_string_list(record.get("preconditions")), f"{path}: record {hypothesis_id} preconditions must be a nonempty string list")
        _require(errors, _is_nonempty_string_list(record.get("source_surfaces")), f"{path}: record {hypothesis_id} source_surfaces must be a nonempty string list")
        _require(
            errors,
            isinstance(record.get("related_invariants"), list)
            and all(_is_nonempty_string(item) for item in record["related_invariants"]),
            f"{path}: record {hypothesis_id} related_invariants must be a string list",
        )

        replacement_claim = record.get("replacement_claim")
        _require(errors, replacement_claim is None or _is_nonempty_string(replacement_claim), f"{path}: record {hypothesis_id} replacement_claim must be null or a nonempty string")

        if linked_world_model is not None:
            _require(
                errors,
                record.get("slice_id") in linked_slice_ids,
                f"{path}: record {hypothesis_id} references unknown slice_id in linked world model",
            )
            _require(
                errors,
                scenario_id is None or scenario_id in linked_scenario_ids,
                f"{path}: record {hypothesis_id} references unknown scenario_id in linked world model",
            )
            for invariant_id in record.get("related_invariants", []):
                _require(
                    errors,
                    invariant_id in linked_invariant_ids,
                    f"{path}: record {hypothesis_id} references unknown invariant {invariant_id}",
                )

    return errors


def validate_target_shapes_data(data: dict, path: Path) -> list[str]:
    errors: list[str] = []

    _require(errors, TARGET_TOP_LEVEL_KEYS.issubset(data.keys()), f"{path}: missing top-level keys")
    _require(
        errors,
        data.get("schema") == TARGET_SHAPES_SCHEMA,
        f"{path}: schema must equal {TARGET_SHAPES_SCHEMA}",
    )
    _require(errors, _is_nonempty_string(data.get("repo_root")), f"{path}: repo_root must be a nonempty string")
    _require(errors, _is_nonempty_string(data.get("world_model_id")), f"{path}: world_model_id must be a nonempty string")
    _require(errors, _is_nonempty_string(data.get("world_model_path")), f"{path}: world_model_path must be a nonempty string")
    _require(
        errors,
        _is_nonempty_string(data.get("negative_knowledge_path")),
        f"{path}: negative_knowledge_path must be a nonempty string",
    )
    _require(errors, _is_nonempty_string(data.get("description")), f"{path}: description must be a nonempty string")

    evidence_classes = data.get("evidence_classes")
    target_shapes = data.get("target_shapes")
    _require(errors, isinstance(evidence_classes, list) and evidence_classes, f"{path}: evidence_classes must be a nonempty list")
    _require(errors, isinstance(target_shapes, list) and target_shapes, f"{path}: target_shapes must be a nonempty list")
    if errors:
        return errors

    evidence_class_set = set(evidence_classes)
    _require(errors, evidence_class_set <= ALLOWED_EVIDENCE_CLASSES, f"{path}: evidence_classes contains unsupported values")
    _require(errors, _ids_unique(target_shapes, "target_shape_id"), f"{path}: target_shape ids must be unique and nonempty")

    world_model_path = _resolve_linked_path(path, str(data["world_model_path"]))
    negative_path = _resolve_linked_path(path, str(data["negative_knowledge_path"]))
    _require(errors, world_model_path is not None, f"{path}: linked world_model_path could not be resolved")
    _require(errors, negative_path is not None, f"{path}: linked negative_knowledge_path could not be resolved")
    if errors:
        return errors

    world_model_errors = validate_artifact(world_model_path)
    negative_errors = validate_artifact(negative_path)
    if world_model_errors:
        for err in world_model_errors:
            errors.append(f"{path}: linked world model invalid: {err}")
    if negative_errors:
        for err in negative_errors:
            errors.append(f"{path}: linked negative knowledge invalid: {err}")
    if errors:
        return errors

    world_model = json.loads(world_model_path.read_text())
    negative_knowledge = json.loads(negative_path.read_text())
    _require(
        errors,
        world_model.get("world_model_id") == data.get("world_model_id"),
        f"{path}: linked world model id must match top-level world_model_id",
    )
    _require(
        errors,
        negative_knowledge.get("world_model_id") == data.get("world_model_id"),
        f"{path}: linked negative knowledge world_model_id must match top-level world_model_id",
    )

    linked_slice_ids = {
        slice_obj["slice_id"]
        for slice_obj in world_model.get("slices", [])
        if isinstance(slice_obj, dict) and isinstance(slice_obj.get("slice_id"), str)
    }
    linked_invariant_ids = {
        invariant["id"]
        for invariant in world_model.get("cross_slice_invariants", [])
        if isinstance(invariant, dict) and isinstance(invariant.get("id"), str)
    }
    linked_hypothesis_ids = {
        record["hypothesis_id"]
        for record in negative_knowledge.get("records", [])
        if isinstance(record, dict) and isinstance(record.get("hypothesis_id"), str)
    }

    for target_shape in target_shapes:
        if not isinstance(target_shape, dict):
            errors.append(f"{path}: each target_shape must be an object")
            continue
        target_shape_id = target_shape.get("target_shape_id", "<missing>")
        _require(errors, TARGET_SHAPE_KEYS.issubset(target_shape.keys()), f"{path}: target_shape {target_shape_id} missing required keys")
        _require(errors, isinstance(target_shape.get("required"), bool), f"{path}: target_shape {target_shape_id} required must be a bool")
        _require(errors, isinstance(target_shape.get("clauses"), list) and target_shape["clauses"], f"{path}: target_shape {target_shape_id} clauses must be a nonempty list")
        _require(errors, _is_nonempty_string_list(target_shape.get("sources")), f"{path}: target_shape {target_shape_id} sources must be a nonempty string list")
        clauses = target_shape.get("clauses", [])
        if isinstance(clauses, list) and clauses:
            _require(errors, _ids_unique(clauses, "clause_id"), f"{path}: target_shape {target_shape_id} clause ids must be unique and nonempty")

        for clause in clauses:
            if not isinstance(clause, dict):
                errors.append(f"{path}: target_shape {target_shape_id} clause entries must be objects")
                continue
            clause_id = clause.get("clause_id", "<missing>")
            _require(errors, TARGET_CLAUSE_KEYS.issubset(clause.keys()), f"{path}: target_shape {target_shape_id} clause {clause_id} missing required keys")
            _require(
                errors,
                clause.get("target_evidence_class") in evidence_class_set,
                f"{path}: target_shape {target_shape_id} clause {clause_id} has unsupported target_evidence_class",
            )
            _require(
                errors,
                clause.get("support_mode") in ALLOWED_TARGET_SUPPORT_MODES,
                f"{path}: target_shape {target_shape_id} clause {clause_id} has unsupported support_mode",
            )
            _require(errors, isinstance(clause.get("notes"), str), f"{path}: target_shape {target_shape_id} clause {clause_id} notes must be a string")
            _require(
                errors,
                isinstance(clause.get("blocked_by_hypotheses"), list)
                and all(_is_nonempty_string(item) for item in clause["blocked_by_hypotheses"]),
                f"{path}: target_shape {target_shape_id} clause {clause_id} blocked_by_hypotheses must be a string list",
            )
            requirements = clause.get("requirements")
            _require(
                errors,
                isinstance(requirements, list) and requirements,
                f"{path}: target_shape {target_shape_id} clause {clause_id} requirements must be a nonempty list",
            )
            if not isinstance(requirements, list):
                continue
            for requirement in requirements:
                if not isinstance(requirement, dict):
                    errors.append(f"{path}: target_shape {target_shape_id} clause {clause_id} requirements must be objects")
                    continue
                _require(
                    errors,
                    TARGET_REQUIREMENT_KEYS.issuperset(requirement.keys()) and _is_nonempty_string(requirement.get("kind")),
                    f"{path}: target_shape {target_shape_id} clause {clause_id} has invalid requirement keys",
                )
                kind = requirement.get("kind")
                _require(
                    errors,
                    kind in ALLOWED_TARGET_REQUIREMENT_KINDS,
                    f"{path}: target_shape {target_shape_id} clause {clause_id} uses unsupported requirement kind",
                )
                if kind == "slice_status_at_least":
                    _require(
                        errors,
                        requirement.get("slice_id") in linked_slice_ids,
                        f"{path}: target_shape {target_shape_id} clause {clause_id} references unknown slice_id",
                    )
                    _require(
                        errors,
                        requirement.get("min_status") in evidence_class_set,
                        f"{path}: target_shape {target_shape_id} clause {clause_id} uses unsupported min_status",
                    )
                    _require(
                        errors,
                        requirement.get("invariant_id") in (None, ""),
                        f"{path}: target_shape {target_shape_id} clause {clause_id} slice_status_at_least must not set invariant_id",
                    )
                elif kind == "cross_invariant_present":
                    _require(
                        errors,
                        requirement.get("invariant_id") in linked_invariant_ids,
                        f"{path}: target_shape {target_shape_id} clause {clause_id} references unknown invariant_id",
                    )
                    _require(
                        errors,
                        requirement.get("slice_id") in (None, ""),
                        f"{path}: target_shape {target_shape_id} clause {clause_id} cross_invariant_present must not set slice_id",
                    )
                    _require(
                        errors,
                        requirement.get("min_status") in (None, ""),
                        f"{path}: target_shape {target_shape_id} clause {clause_id} cross_invariant_present must not set min_status",
                    )

            for hypothesis_id in clause.get("blocked_by_hypotheses", []):
                _require(
                    errors,
                    hypothesis_id in linked_hypothesis_ids,
                    f"{path}: target_shape {target_shape_id} clause {clause_id} references unknown hypothesis_id",
                )

    return errors


def validate_artifact(path: Path) -> list[str]:
    try:
        data = json.loads(path.read_text())
    except Exception as exc:  # pragma: no cover - surfaced directly in test
        return [f"{path}: failed to parse JSON: {exc}"]

    if not isinstance(data, dict):
        return [f"{path}: top-level JSON must be an object"]

    schema = data.get("schema")
    if schema == WORLD_MODEL_SCHEMA:
        return validate_world_model_data(data, path)
    if schema == NEGATIVE_KNOWLEDGE_SCHEMA:
        return validate_negative_knowledge_data(data, path)
    if schema == TARGET_SHAPES_SCHEMA:
        return validate_target_shapes_data(data, path)
    return [f"{path}: unsupported ShapeForge schema {schema!r}"]


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate a ShapeForge JSON artifact.")
    parser.add_argument("path", type=Path, help="Path to a ShapeForge JSON file")
    args = parser.parse_args()

    errors = validate_artifact(args.path)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print(f"OK {args.path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
