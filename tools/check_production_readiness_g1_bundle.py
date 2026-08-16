#!/usr/bin/env python3
"""Check cross-artifact integrity for the exact-subject G1 research bundle.

The individual G1 gates establish local source binding.  This gate verifies
that their published artifacts still describe one command registry, one set
of open profile decisions, one state/value-delta inventory, and one explicit
repair-descendant overlay.  It preserves the no-authority posture while
making cross-artifact drift fail closed.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_BUNDLE_V1.json"
SCHEMA = "zenodex/production-readiness-g1-bundle/v1"

sys.path.insert(0, str(REPO_ROOT))

from tools import check_production_readiness_g1_bdd as bdd  # noqa: E402
from tools import check_production_readiness_g1_entrypoints as entrypoints  # noqa: E402
from tools import check_production_readiness_g1_legacy_atdd_quarantine as quarantine  # noqa: E402
from tools import check_production_readiness_g1_profile_gate as profile_gate  # noqa: E402
from tools import check_production_readiness_g1_safe_hold as safe_hold  # noqa: E402
from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402
from tools import check_production_readiness_g1_state_delta_gate as state_delta  # noqa: E402

BASE_SOURCE_SUBJECT = semantics.SOURCE_SUBJECT
REPAIR_SOURCE_SUBJECT = entrypoints.SOURCE_SUBJECT
ARTIFACT_PATHS = {
    "semantics": "docs/research/PRODUCTION_READINESS_G1_SEMANTICS_V1.json",
    "bdd": "docs/research/PRODUCTION_READINESS_G1_BDD_V1.json",
    "entrypoints": "docs/research/PRODUCTION_READINESS_G1_ENTRYPOINTS_V1.json",
    "safe_hold": "docs/research/PRODUCTION_READINESS_G1_SAFE_HOLD_V1.json",
    "profile_gate": "docs/research/PRODUCTION_READINESS_G1_PROFILE_GATE_V1.json",
    "state_delta": "docs/research/PRODUCTION_READINESS_G1_STATE_DELTA_GATE_V1.json",
    "quarantine": "docs/research/PRODUCTION_READINESS_G1_LEGACY_ATDD_QUARANTINE_V1.json",
}


def _load(path: Path) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    with path.open(encoding="utf-8") as stream:
        value = json.load(stream, object_pairs_hook=hook)
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(value, dict):
        raise ValueError("artifact root must be an object")
    return value


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(_encoded(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _is_ancestor(repo_root: Path, ancestor: str, descendant: str) -> bool:
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", ancestor, descendant],
        cwd=repo_root,
        check=False,
    )
    return result.returncode == 0


def _generated_documents(repo_root: Path) -> dict[str, dict[str, Any]]:
    builders = {
        "semantics": semantics.build_document,
        "bdd": bdd.build_document,
        "entrypoints": entrypoints.build_document,
        "safe_hold": safe_hold.build_document,
        "profile_gate": profile_gate.build_document,
        "state_delta": state_delta.build_document,
        "quarantine": quarantine.build_document,
    }
    return {label: builder(repo_root) for label, builder in builders.items()}


def _load_and_verify_artifacts(
    repo_root: Path,
    generated: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    observed: dict[str, dict[str, Any]] = {}
    for label, relative_path in ARTIFACT_PATHS.items():
        path = repo_root / relative_path
        value = _load(path)
        if path.read_bytes() != _encoded(value):
            raise ValueError(f"{label} artifact is not canonically encoded JSON")
        if value != generated[label]:
            raise ValueError(f"{label} artifact differs from its exact-subject generated form")
        observed[label] = value
    return observed


def _check_source_subjects(documents: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    base_labels = ("semantics", "bdd", "safe_hold", "profile_gate", "state_delta", "quarantine")
    for label in base_labels:
        subject = documents[label].get("source_subject")
        if not isinstance(subject, Mapping):
            errors.append(f"{label} source_subject is missing")
            continue
        if subject.get("base_commit") != BASE_SOURCE_SUBJECT:
            errors.append(f"{label} does not bind the exact base source subject")
        if subject.get("current_head_must_descend_from_base") is not True:
            errors.append(f"{label} does not require current HEAD ancestry from base")
        if subject.get("source_authority") != "frozen source bytes at the exact base commit":
            errors.append(f"{label} has an unexpected source authority description")
        pins = documents[label].get("source_pins")
        if not isinstance(pins, list) or any(pin.get("subject") != BASE_SOURCE_SUBJECT for pin in pins if isinstance(pin, Mapping)):
            errors.append(f"{label} source pins are not base-subject bound")

    overlay = documents["entrypoints"].get("source_subject")
    if not isinstance(overlay, Mapping):
        errors.append("entrypoints source_subject is missing")
    else:
        expected_relation = {
            "base_is_ancestor_of_repair": True,
            "relation_scope": "ANCESTRY_ONLY_RESEARCH_OVERLAY",
            "semantic_equivalence": "NOT_PROVED",
        }
        if overlay.get("base_commit") != BASE_SOURCE_SUBJECT:
            errors.append("entrypoints overlay base subject differs from semantic artifacts")
        if overlay.get("repair_commit") != REPAIR_SOURCE_SUBJECT:
            errors.append("entrypoints overlay repair subject differs from frozen repair subject")
        if overlay.get("subject_role") != "RESEARCH_REPAIR_DESCENDANT_OVERLAY":
            errors.append("entrypoints overlay subject role is missing or overclaims authority")
        if overlay.get("base_to_repair_relation") != expected_relation:
            errors.append("entrypoints overlay relation is missing or overclaims semantic equivalence")
        if overlay.get("base_semantics_artifacts_remain_authoritative") is not True:
            errors.append("entrypoints overlay does not preserve base semantic artifact authority")
        pins = documents["entrypoints"].get("source_pins")
        if not isinstance(pins, list) or any(pin.get("subject") != REPAIR_SOURCE_SUBJECT for pin in pins if isinstance(pin, Mapping)):
            errors.append("entrypoints source pins are not repair-subject bound")
    return errors


def _check_registry_bindings(documents: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    semantic_entries = documents["semantics"].get("command_registry")
    if not isinstance(semantic_entries, list):
        return ["semantics command registry is missing"]
    command_ids = {entry.get("id") for entry in semantic_entries if isinstance(entry, Mapping)}
    expected_ids = {command.value for command in semantics.EXPECTED_COMMANDS}
    if command_ids != expected_ids or len(command_ids) != 33:
        errors.append("semantic command registry is not the exact 33-command set")

    bdd_binding = documents["bdd"].get("registry_binding")
    bdd_workflows = documents["bdd"].get("workflows")
    bdd_ids = {workflow.get("command_id") for workflow in bdd_workflows if isinstance(workflow, Mapping)} if isinstance(bdd_workflows, list) else set()
    if not isinstance(bdd_binding, Mapping) or set(bdd_binding.get("command_ids", [])) != command_ids or bdd_ids != command_ids:
        errors.append("BDD registry and workflows do not bind the semantic command set")

    for label in ("entrypoints", "safe_hold"):
        routes = documents[label].get("command_routes")
        route_ids = {route.get("id", route.get("command_id")) for route in routes if isinstance(route, Mapping)} if isinstance(routes, list) else set()
        if route_ids != command_ids:
            errors.append(f"{label} routes do not bind the semantic command set")

    disabled_ids = {command.value for command in semantics.EXPECTED_DISABLED}
    if isinstance(bdd_binding, Mapping) and set(bdd_binding.get("disabled_command_ids", [])) != disabled_ids:
        errors.append("BDD disabled command partition differs from the exact source partition")
    safe_routes = documents["safe_hold"].get("command_routes")
    safe_disabled = {
        route.get("command_id")
        for route in safe_routes
        if isinstance(route, Mapping) and route.get("source_enablement") == "RESEARCH_DISABLED_NO_PRODUCTION_WRITER"
    } if isinstance(safe_routes, list) else set()
    if safe_disabled != disabled_ids:
        errors.append("safe-hold disabled command partition differs from the exact source partition")
    return errors


def _check_decision_and_state_bindings(documents: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    semantic = documents["semantics"]
    decision_ids = {decision.get("id") for decision in semantic.get("profile_decisions", []) if isinstance(decision, Mapping)}
    profile_gates = documents["profile_gate"].get("decision_gates")
    profile_ids = {gate.get("id") for gate in profile_gates if isinstance(gate, Mapping)} if isinstance(profile_gates, list) else set()
    bdd_open = set(documents["bdd"].get("open_profile_decisions", []))
    safe_holds = documents["safe_hold"].get("profile_decision_holds")
    safe_ids = {hold.get("id") for hold in safe_holds if isinstance(hold, Mapping)} if isinstance(safe_holds, list) else set()
    if decision_ids != set(profile_ids) or decision_ids != bdd_open or decision_ids != safe_ids or len(decision_ids) != 9:
        errors.append("profile decision IDs drift across semantics, BDD, profile, or safe-hold artifacts")
    if any(
        gate.get("status") != "OPEN" or gate.get("selected_option_shape") is not None or gate.get("selected_profile") is not None or gate.get("production_authority") != "NONE"
        for gate in profile_gates
        if isinstance(gate, Mapping)
    ):
        errors.append("profile gate contains a selected or authoritative decision")

    semantic_state = semantic.get("global_state_projection", {})
    state_projection = documents["state_delta"].get("state_projection", {})
    semantic_fields = {field.get("name") for field in semantic_state.get("fields", []) if isinstance(field, Mapping)}
    state_fields = {field.get("name") for field in state_projection.get("fields", []) if isinstance(field, Mapping)}
    semantic_delta = semantic.get("value_delta_algebra", {})
    state_algebra = documents["state_delta"].get("value_delta_algebra", {})
    if semantic_fields != state_fields or len(semantic_fields) != 14:
        errors.append("state field names drift between semantics and state-delta artifacts")
    if set(semantic_delta.get("delta_classes", [])) != set(state_algebra.get("delta_classes", [])) or len(semantic_delta.get("delta_classes", [])) != 8:
        errors.append("value-delta classes drift between semantics and state-delta artifacts")
    mapping = documents["state_delta"].get("runtime_mapping_gap_ledger", {})
    global_effect_surface = mapping.get("global_effect_kind_surface", {}) if isinstance(mapping, Mapping) else {}
    m6_surface = mapping.get("m6_value_delta_surface", {}) if isinstance(mapping, Mapping) else {}
    m6_class_type_value = m6_surface.get("delta_class_type") if isinstance(m6_surface, Mapping) else None
    m6_entry_type_value = m6_surface.get("delta_entry_type") if isinstance(m6_surface, Mapping) else None
    m6_contract_shape_value = m6_surface.get("abstract_contract_shape") if isinstance(m6_surface, Mapping) else None
    m6_class_type = m6_class_type_value if isinstance(m6_class_type_value, Mapping) else {}
    m6_entry_type = m6_entry_type_value if isinstance(m6_entry_type_value, Mapping) else {}
    m6_contract_shape = m6_contract_shape_value if isinstance(m6_contract_shape_value, Mapping) else {}
    expected_required_fields: list[str] = []
    for contract in semantic_delta.get("class_contracts", []):
        if not isinstance(contract, Mapping):
            continue
        for field in contract.get("required_fields", []):
            if field not in expected_required_fields:
                expected_required_fields.append(field)
    expected_m6_missing_fields = [
        field
        for field in expected_required_fields
        if field not in m6_entry_type.get("declared_fields", [])
    ]
    m6_pins = m6_surface.get("source_pins") if isinstance(m6_surface, Mapping) else None
    if (
        not isinstance(mapping, Mapping)
        or mapping.get("source_subject") != BASE_SOURCE_SUBJECT
        or mapping.get("status") != "GAP_STRUCTURAL_CANDIDATES_ONLY"
        or mapping.get("semantic_mapping_status")
        != "GAP_ABSTRACT_14_FIELD_AND_8_DELTA_MAPPING_UNPROVED"
        or mapping.get("production_authority") != "NONE"
        or mapping.get("abstract_field_count") != 14
        or mapping.get("abstract_delta_class_count") != 8
        or set(mapping.get("unmapped_abstract_fields", [])) != {"lp_state", "auctions"}
        or set(mapping.get("runtime_effect_kinds_without_abstract_delta_candidate", []))
        != {"RESERVE", "FEE_ALLOCATION", "REWARD"}
        or global_effect_surface.get("runtime_class") != state_delta.RUNTIME_EFFECT_KIND_CLASS
        or global_effect_surface.get("runtime_effect_kind_count") != 9
        or global_effect_surface.get("runtime_effect_kinds")
        != documents["state_delta"]["runtime_projection"]["effect_kind_type"]["kinds"]
        or not isinstance(m6_surface, Mapping)
        or m6_surface.get("source_subject") != BASE_SOURCE_SUBJECT
        or m6_surface.get("status") != "M6_DELTA_SOURCE_SHAPE_RESEARCH_ONLY"
        or m6_surface.get("semantic_mapping_status")
        != "GAP_ENTRY_FIELDS_DO_NOT_CLOSE_ABSTRACT_DELTA_CONTRACTS"
        or m6_surface.get("production_authority") != "NONE"
        or not isinstance(m6_pins, list)
        or len(m6_pins) != 1
        or not isinstance(m6_pins[0], Mapping)
        or m6_pins[0].get("path") != state_delta.M6_DELTA_SOURCE_PATH
        or m6_pins[0].get("subject") != BASE_SOURCE_SUBJECT
        or m6_pins[0].get("sha256") != state_delta.M6_DELTA_SOURCE_SHA256
        or m6_class_type.get("runtime_delta_class_count") != 9
        or m6_class_type.get("runtime_delta_classes")
        != list(state_delta.M6_EXPECTED_RUNTIME_DELTA_CLASSES)
        or m6_class_type.get("abstract_delta_classes")
        != list(semantic_delta.get("delta_classes", []))
        or m6_class_type.get("abstract_delta_classes_without_runtime_kind") != []
        or m6_class_type.get("runtime_delta_classes_without_abstract_class") != ["noop"]
        or m6_entry_type.get("declared_field_count") != 5
        or m6_entry_type.get("declared_fields")
        != list(state_delta.M6_EXPECTED_DELTA_ENTRY_FIELDS)
        or m6_entry_type.get("literal_projection_key_order")
        != list(state_delta.M6_EXPECTED_DELTA_ENTRY_FIELDS)
        or m6_entry_type.get("declared_fields_match_literal_projection") is not True
        or m6_contract_shape.get("source_artifact")
        != state_delta.ABSTRACT_DELTA_CONTRACT_PROJECTION_PATH
        or m6_contract_shape.get("source_subject") != BASE_SOURCE_SUBJECT
        or m6_contract_shape.get("projection") != "value_delta_algebra"
        or m6_contract_shape.get("projection_digest_status")
        != "EXACT_SUBJECT_HELPER_BASELINE_RESEARCH_ONLY"
        or m6_contract_shape.get("projection_sha256")
        != state_delta.ABSTRACT_DELTA_CONTRACT_PROJECTION_SHA256
        or m6_contract_shape.get("required_fields_missing_from_runtime_entry")
        != expected_m6_missing_fields
    ):
        errors.append("runtime state/delta mapping gap ledger drifted or overclaims authority")
    return errors


def _check_safe_hold_and_quarantine(documents: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    safe = documents["safe_hold"]
    hold_policy = safe.get("hold_policy", {})
    exit_gate = safe.get("g1_exit_gate", {})
    routes = safe.get("command_routes", [])
    if (
        hold_policy.get("selected_profile_count") != 0
        or hold_policy.get("production_writer_count") != 0
        or hold_policy.get("authority") != "NONE"
        or exit_gate.get("held_command_count") != 33
        or any(route.get("safe_hold_status") != "UNMOUNTED_RESEARCH_ONLY" or route.get("production_writer_declared") is not False for route in routes if isinstance(route, Mapping))
    ):
        errors.append("safe-hold artifact does not preserve the no-launch posture")
    legacy = documents["quarantine"].get("quarantine", {})
    if legacy.get("quarantined") is not True or legacy.get("usable_as_exact_subject_g1_evidence") is not False or legacy.get("production_authority") != "NONE":
        errors.append("legacy ATDD quarantine does not remain fail-closed")
    return errors


def _check_research_only_posture(documents: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    for label, document in documents.items():
        if document.get("production_promotion") is not False:
            errors.append(f"{label} production_promotion is not false")
    entrypoint_capability = documents["entrypoints"].get("production_publication_capability", {})
    writer_inventory = documents["entrypoints"].get("writer_inventory", {})
    if entrypoint_capability.get("declared_production_entrypoint_count") != 0 or writer_inventory.get("declared_production_entrypoint_ids") != []:
        errors.append("entrypoint artifact declares a production writer")
    bdd_workflows = documents["bdd"].get("workflows", [])
    if any(
        workflow.get("production_mount") != "UNMOUNTED_RESEARCH_ONLY"
        or any(scenario.get("evidence_status") != "UNIMPLEMENTED_RESEARCH_SCENARIO" for scenario in workflow.get("scenarios", []))
        for workflow in bdd_workflows
        if isinstance(workflow, Mapping)
    ):
        errors.append("BDD artifact contains executable or mounted evidence")
    return errors


def _consistency_checks(documents: Mapping[str, Mapping[str, Any]], repo_root: Path) -> list[dict[str, Any]]:
    errors = [
        *_check_source_subjects(documents),
        *_check_registry_bindings(documents),
        *_check_decision_and_state_bindings(documents),
        *_check_safe_hold_and_quarantine(documents),
        *_check_research_only_posture(documents),
    ]
    if not _is_ancestor(repo_root, BASE_SOURCE_SUBJECT, "HEAD"):
        errors.append("current HEAD does not descend from the exact G1 base subject")
    if not _is_ancestor(repo_root, BASE_SOURCE_SUBJECT, REPAIR_SOURCE_SUBJECT):
        errors.append("repair subject does not descend from the exact G1 base subject")
    if not _is_ancestor(repo_root, REPAIR_SOURCE_SUBJECT, "HEAD"):
        errors.append("current HEAD does not descend from the exact G1 repair subject")
    if errors:
        raise ValueError("G1 bundle consistency failure: " + "; ".join(errors))
    return [
        {
            "id": check_id,
            "status": "PASS",
            "scope": scope,
        }
        for check_id, scope in (
            ("SOURCE_SUBJECT_CONTRACT", "base artifacts plus repair-descendant overlay"),
            ("COMMAND_REGISTRY_BINDING", "33 commands and exact 8-command disabled partition"),
            ("PROFILE_DECISION_BINDING", "9 open decisions with no selected authority"),
            ("STATE_DELTA_BINDING", "14 state fields and 8 abstract value-delta classes"),
            ("RUNTIME_MAPPING_GAP_BINDING", "global effect-kind candidates and explicit unmapped runtime kinds"),
            ("M6_DELTA_SURFACE_GAP_BINDING", "M6 ValueDeltaClassV1 and ValueDeltaEntryV1 shape and contract gap"),
            ("SAFE_HOLD_AND_QUARANTINE", "33 unmounted commands and stale ATDD fail-closed status"),
            ("RESEARCH_ONLY_POSTURE", "no production promotion, writer, or executable BDD evidence"),
            ("CURRENT_HEAD_ANCESTRY", "base and repair subjects are ancestors of current HEAD"),
        )
    ]


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    generated = _generated_documents(repo_root)
    documents = _load_and_verify_artifacts(repo_root, generated)
    checks = _consistency_checks(documents, repo_root)
    semantic = documents["semantics"]
    bdd_workflows = documents["bdd"]["workflows"]
    state_mapping = documents["state_delta"]["runtime_mapping_gap_ledger"]
    m6_surface = state_mapping["m6_value_delta_surface"]
    m6_class_type = m6_surface["delta_class_type"]
    m6_entry_type = m6_surface["delta_entry_type"]
    m6_contract_shape = m6_surface["abstract_contract_shape"]
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_CROSS_ARTIFACT_BUNDLE_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": {
            "base_commit": BASE_SOURCE_SUBJECT,
            "repair_commit": REPAIR_SOURCE_SUBJECT,
            "base_artifact_ids": ["bdd", "legacy_atdd_quarantine", "profile_gate", "safe_hold", "semantics", "state_delta"],
            "repair_overlay_artifact_ids": ["entrypoints"],
            "repair_relation": "ANCESTRY_ONLY_RESEARCH_OVERLAY",
            "semantic_equivalence": "NOT_PROVED",
        },
        "artifact_bindings": [
            {
                "id": label,
                "path": relative_path,
                "schema": documents[label]["schema"],
                "source_subject_role": "RESEARCH_REPAIR_DESCENDANT_OVERLAY" if label == "entrypoints" else "EXACT_BASE_SUBJECT",
            }
            for label, relative_path in ARTIFACT_PATHS.items()
        ],
        "registry_binding": {
            "command_count": len(semantic["command_registry"]),
            "disabled_command_count": len(semantics.EXPECTED_DISABLED),
            "command_ids": sorted(entry["id"] for entry in semantic["command_registry"]),
            "workflow_count": len(bdd_workflows),
            "entrypoint_route_count": len(documents["entrypoints"]["command_routes"]),
            "safe_hold_route_count": len(documents["safe_hold"]["command_routes"]),
        },
        "obligation_binding": {
            "profile_decision_count": len(semantic["profile_decisions"]),
            "open_profile_decision_count": len(documents["profile_gate"]["decision_gates"]),
            "state_field_count": len(semantic["global_state_projection"]["fields"]),
            "delta_class_count": len(semantic["value_delta_algebra"]["delta_classes"]),
            "open_state_obligation_count": len(documents["state_delta"]["closure_obligations"]),
            "runtime_mapping_unmapped_field_count": len(
                documents["state_delta"]["runtime_mapping_gap_ledger"]["unmapped_abstract_fields"]
            ),
            "runtime_mapping_unmapped_effect_kind_count": len(
                state_mapping[
                    "runtime_effect_kinds_without_abstract_delta_candidate"
                ]
            ),
            "m6_value_delta_surface": {
                "status": m6_surface["status"],
                "source_subject": m6_surface["source_subject"],
                "semantic_mapping_status": m6_surface["semantic_mapping_status"],
                "production_authority": m6_surface["production_authority"],
                "runtime_delta_classes_without_abstract_class": m6_class_type[
                    "runtime_delta_classes_without_abstract_class"
                ],
                "abstract_contract_projection_sha256": m6_contract_shape[
                    "projection_sha256"
                ],
                "abstract_contract_projection_digest_status": m6_contract_shape[
                    "projection_digest_status"
                ],
                "entry_declared_field_count": m6_entry_type["declared_field_count"],
                "entry_missing_required_field_count": len(
                    m6_contract_shape["required_fields_missing_from_runtime_entry"]
                ),
            },
            "bdd_scenario_count": sum(len(workflow["scenarios"]) for workflow in bdd_workflows),
        },
        "consistency_checks": checks,
        "g1_exit_gate": {
            "complete": False,
            "status": "BLOCKED_OPEN_PROFILE_DECISIONS_AND_STATE_DELTA_GAPS",
            "production_authority": "NONE",
            "production_ready": False,
            "declared_production_writer_count": 0,
            "all_commands_unmounted": True,
        },
        "nonclaims": [
            "A passing bundle proves cross-artifact consistency only; it does not prove economic laws, runtime reachability, or production safety.",
            "The repair-descendant relation is ancestry evidence and does not prove semantic equivalence to the base subject.",
            "The bundle preserves open profile decisions, state/delta gaps, and the legacy ATDD quarantine.",
            "No artifact in this bundle selects policy, mounts a command, settles value, or promotes production authority.",
        ],
    }


def check_artifact(path: Path, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    observed: dict[str, Any] = {}
    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if path.read_bytes() != _encoded(observed):
            errors.append("bundle artifact is not canonically encoded JSON")
        if observed != expected:
            errors.append("bundle artifact differs from the exact-subject cross-artifact G1 bundle")
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))
    registry = observed.get("registry_binding")
    obligations = observed.get("obligation_binding")
    m6_binding_value = (
        obligations.get("m6_value_delta_surface")
        if isinstance(obligations, Mapping)
        else None
    )
    m6_binding = m6_binding_value if isinstance(m6_binding_value, Mapping) else {}
    return {
        "schema": "zenodex/production-readiness-g1-bundle-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "artifact_count": len(observed.get("artifact_bindings", [])) if isinstance(observed.get("artifact_bindings"), list) else 0,
        "consistency_check_count": len(observed.get("consistency_checks", [])) if isinstance(observed.get("consistency_checks"), list) else 0,
        "command_count": registry.get("command_count", 0) if isinstance(registry, Mapping) else 0,
        "profile_decision_count": obligations.get("profile_decision_count", 0) if isinstance(obligations, Mapping) else 0,
        "open_state_obligation_count": obligations.get("open_state_obligation_count", 0) if isinstance(obligations, Mapping) else 0,
        "runtime_mapping_unmapped_field_count": obligations.get("runtime_mapping_unmapped_field_count", 0)
        if isinstance(obligations, Mapping)
        else 0,
        "runtime_mapping_unmapped_effect_kind_count": obligations.get(
            "runtime_mapping_unmapped_effect_kind_count", 0
        )
        if isinstance(obligations, Mapping)
        else 0,
        "m6_runtime_delta_surplus_count": len(
            m6_binding.get("runtime_delta_classes_without_abstract_class", [])
        )
        if isinstance(m6_binding.get("runtime_delta_classes_without_abstract_class"), list)
        else 0,
        "m6_entry_missing_required_field_count": m6_binding.get(
            "entry_missing_required_field_count", 0
        ),
        "errors": errors,
        "nonclaim": "PASS means only that the G1 research artifacts are mutually consistent and source-bound; it does not promote G1 or production readiness.",
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, build_document(args.repo_root))
    report = check_artifact(args.output, args.repo_root)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("PASS" if report["ok"] else "FAIL")
        for error in report["errors"]:
            print(f"error: {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
