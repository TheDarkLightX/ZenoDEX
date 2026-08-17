#!/usr/bin/env python3
"""Check the exact research-only V2 transactional-microkernel candidate.

The checker owns every accepted registry and keeps all qualification evidence
unverified.  Its assumption/guarantee token checks are structural only.  ESSO
with Z3 and CVC5 plus Lean remain mandatory, explicit open evidence lanes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import types
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

CONTRACT_SOURCE_PATH = REPO_ROOT / "tools/production_readiness_architecture_candidate_contract_v2.py"
CONTRACT_EXECUTION_SOURCE_BYTES = CONTRACT_SOURCE_PATH.read_bytes()
contract = types.ModuleType("tools.production_readiness_architecture_candidate_contract_v2_snapshot")
contract.__file__ = str(CONTRACT_SOURCE_PATH)
contract.__package__ = "tools"
exec(
    compile(CONTRACT_EXECUTION_SOURCE_BYTES, str(CONTRACT_SOURCE_PATH), "exec"),
    contract.__dict__,
)


DEFAULT_ARTIFACT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_ARCHITECTURE_CANDIDATE_V2.json"


@dataclass(frozen=True)
class SourceSnapshot:
    relative_path: str
    data: bytes
    sha256: str
    device: int
    inode: int
    size: int
    mtime_ns: int


def _decode_json(data: bytes, label: str) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=hook)
    except UnicodeDecodeError as exc:
        raise ValueError(f"{label} is not UTF-8") from exc
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(value, dict):
        raise ValueError(f"{label} root must be an object")
    return value


def _load(path: Path) -> dict[str, Any]:
    return _decode_json(path.read_bytes(), str(path))


def _open_source_descriptor(
    repo_root: Path,
    relative_path: str,
    parts: tuple[str, ...],
    errors: list[str],
) -> int | None:
    root = repo_root.resolve()
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    close_on_exec = getattr(os, "O_CLOEXEC", 0)
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | close_on_exec | nofollow
    source_flags = os.O_RDONLY | close_on_exec | nofollow
    directory_descriptors: list[int] = []
    try:
        directory_descriptors.append(os.open(root, directory_flags))
        for part in parts[:-1]:
            metadata = os.stat(
                part,
                dir_fd=directory_descriptors[-1],
                follow_symlinks=False,
            )
            if stat.S_ISLNK(metadata.st_mode):
                errors.append(
                    "SOURCE_SYMLINK_SUBSTITUTION: source path is symlinked: "
                    f"{relative_path}"
                )
                return None
            if not stat.S_ISDIR(metadata.st_mode):
                errors.append(f"source parent is not a directory: {relative_path}")
                return None
            directory_descriptors.append(
                os.open(part, directory_flags, dir_fd=directory_descriptors[-1])
            )
        metadata = os.stat(
            parts[-1],
            dir_fd=directory_descriptors[-1],
            follow_symlinks=False,
        )
        if stat.S_ISLNK(metadata.st_mode):
            errors.append(
                "SOURCE_SYMLINK_SUBSTITUTION: source path is symlinked: "
                f"{relative_path}"
            )
            return None
        return os.open(
            parts[-1],
            source_flags,
            dir_fd=directory_descriptors[-1],
        )
    except OSError as exc:
        errors.append(f"cannot open source path {relative_path}: {exc}")
        return None
    finally:
        for directory_descriptor in reversed(directory_descriptors):
            os.close(directory_descriptor)


def _read_one_source(
    repo_root: Path,
    relative_path: str,
    errors: list[str],
) -> SourceSnapshot | None:
    if not _is_relative_path(relative_path):
        errors.append(f"unsafe source path: {relative_path!r}")
        return None
    parts = PurePosixPath(relative_path).parts
    if not parts:
        errors.append(f"unsafe source path: {relative_path!r}")
        return None
    descriptor = _open_source_descriptor(repo_root, relative_path, parts, errors)
    if descriptor is None:
        return None
    try:
        try:
            before = os.fstat(descriptor)
            if not stat.S_ISREG(before.st_mode):
                errors.append(f"source path is not a regular file: {relative_path}")
                return None
            with os.fdopen(descriptor, "rb", closefd=False) as stream:
                data = stream.read()
            after = os.fstat(descriptor)
        except OSError as exc:
            errors.append(f"cannot read source path {relative_path}: {exc}")
            return None
    finally:
        os.close(descriptor)
    identity_before = (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
    )
    identity_after = (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    )
    if identity_before != identity_after or len(data) != after.st_size:
        errors.append(f"SOURCE_SPLIT_SNAPSHOT: source changed while read: {relative_path}")
        return None
    return SourceSnapshot(
        relative_path=relative_path,
        data=data,
        sha256=_sha256(data),
        device=after.st_dev,
        inode=after.st_ino,
        size=after.st_size,
        mtime_ns=after.st_mtime_ns,
    )


def _read_source_snapshot(repo_root: Path, errors: list[str]) -> dict[str, SourceSnapshot]:
    snapshots: dict[str, SourceSnapshot] = {}
    for relative_path in contract.EXPECTED_SOURCE_PATHS:
        snapshot = _read_one_source(repo_root, relative_path, errors)
        if snapshot is not None:
            snapshots[relative_path] = snapshot
    return snapshots


def _check_snapshot_unchanged(
    repo_root: Path,
    snapshots: Mapping[str, SourceSnapshot],
    errors: list[str],
) -> None:
    for relative_path, original in snapshots.items():
        reread_errors: list[str] = []
        current = _read_one_source(repo_root, relative_path, reread_errors)
        errors.extend(reread_errors)
        if current != original:
            errors.append(f"SOURCE_SPLIT_SNAPSHOT: source changed during check: {relative_path}")


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _is_sha256(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _is_relative_path(value: object) -> bool:
    if not isinstance(value, str) or not value:
        return False
    path = PurePosixPath(value)
    return not path.is_absolute() and ".." not in path.parts


def _exact_keys(
    value: object,
    expected: set[str] | frozenset[str],
    label: str,
    errors: list[str],
) -> Mapping[str, Any] | None:
    if not isinstance(value, Mapping):
        errors.append(f"{label} must be an object")
        return None
    actual = set(value)
    if actual != set(expected):
        errors.append(
            f"{label} keys differ: missing={sorted(set(expected) - actual)}, "
            f"extra={sorted(actual - set(expected))}"
        )
    return value


def _string_list(value: object, label: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        errors.append(f"{label} must be a string list")
        return []
    if len(value) != len(set(value)):
        errors.append(f"{label} must contain unique values")
    return value


def _rows_by_id(value: object, label: str, errors: list[str]) -> dict[str, Mapping[str, Any]]:
    if not isinstance(value, list):
        errors.append(f"{label} must be a list")
        return {}
    rows: dict[str, Mapping[str, Any]] = {}
    for index, row in enumerate(value):
        if not isinstance(row, Mapping):
            errors.append(f"{label}[{index}] must be an object")
            continue
        row_id = row.get("id")
        if not isinstance(row_id, str) or not row_id or row_id in rows:
            errors.append(f"{label}[{index}] has an invalid or duplicate id")
            continue
        rows[row_id] = row
    return rows


def _without_id(row: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in row.items() if key != "id"}


def _has_cycle(edges: Mapping[str, Sequence[str]]) -> bool:
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node: str) -> bool:
        if node in visiting:
            return True
        if node in visited:
            return False
        visiting.add(node)
        if any(dependency in edges and visit(dependency) for dependency in edges.get(node, ())):
            return True
        visiting.remove(node)
        visited.add(node)
        return False

    return any(visit(node) for node in edges)


def _check_subject(document: Mapping[str, Any], repo_root: Path, errors: list[str]) -> None:
    if document.get("reviewed_subject") != contract.REVIEWED_SUBJECT:
        errors.append("reviewed_subject differs from the checker-owned source subject")
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", contract.REVIEWED_SUBJECT, "HEAD"],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        errors.append("reviewed_subject is not an ancestor of HEAD")


def _check_source_pins(
    document: Mapping[str, Any],
    snapshots: Mapping[str, SourceSnapshot],
    errors: list[str],
) -> None:
    rows = _rows_by_id(document.get("source_pins"), "source_pins", errors)
    if set(rows) != set(contract.EXPECTED_SOURCE_PATHS):
        errors.append("source_pins differ from the checker-owned source paths")
    for path, row in rows.items():
        _exact_keys(row, {"id", "sha256"}, f"source_pins[{path}]", errors)
        snapshot = snapshots.get(path)
        if snapshot is None:
            errors.append(f"missing source snapshot: {path}")
            continue
        digest = row.get("sha256")
        if not _is_sha256(digest) or digest != snapshot.sha256:
            errors.append(f"source pin digest mismatch: {path}")


def _check_contract_execution_snapshot(
    snapshots: Mapping[str, SourceSnapshot], errors: list[str]
) -> None:
    relative_path = "tools/production_readiness_architecture_candidate_contract_v2.py"
    snapshot = snapshots.get(relative_path)
    if snapshot is None:
        errors.append("SOURCE_EXECUTION_SNAPSHOT_SPLIT: contract snapshot is missing")
    elif snapshot.data != CONTRACT_EXECUTION_SOURCE_BYTES:
        errors.append(
            "SOURCE_EXECUTION_SNAPSHOT_SPLIT: executed contract bytes differ from pinned bytes"
        )


def _check_verifier_bootstrap(document: Mapping[str, Any], errors: list[str]) -> None:
    if document.get("verifier_bootstrap") != contract.EXPECTED_VERIFIER_BOOTSTRAP:
        errors.append(
            "SOURCE_EXECUTION_SNAPSHOT_SPLIT: verifier bootstrap must remain an explicit "
            "unverified external premise"
        )


def _check_parent(
    document: Mapping[str, Any],
    snapshots: Mapping[str, SourceSnapshot],
    errors: list[str],
) -> None:
    parent = _exact_keys(
        document.get("parent_tournament"),
        {"path", "sha256", "candidate_id", "selection_status"},
        "parent_tournament",
        errors,
    )
    if parent is None:
        return
    path = parent.get("path")
    expected_path = "docs/research/PRODUCTION_READINESS_ARCHITECTURE_TOURNAMENT_V1.json"
    if path != expected_path:
        errors.append("parent tournament path differs")
        return
    source = snapshots.get(expected_path)
    if source is None:
        errors.append("parent tournament source snapshot is missing")
        return
    if parent.get("sha256") != source.sha256:
        errors.append("parent tournament digest differs")
    if parent.get("candidate_id") != contract.PARENT_CANDIDATE_ID:
        errors.append("parent candidate id differs")
    if parent.get("selection_status") != "RESEARCH_LEADER_UNSELECTED":
        errors.append("parent selection status differs")
    try:
        tournament = _decode_json(source.data, expected_path)
    except (json.JSONDecodeError, ValueError) as exc:
        errors.append(f"parent tournament is malformed: {exc}")
        return
    selection = tournament.get("selection")
    if not isinstance(selection, Mapping):
        errors.append("parent tournament selection is malformed")
        return
    if selection.get("research_leader_id") != contract.PARENT_CANDIDATE_ID:
        errors.append("parent candidate is not the research leader")
    if selection.get("selected_candidate_id") is not None:
        errors.append("parent tournament unexpectedly selected an architecture")


def _check_task_graph_summary(
    snapshots: Mapping[str, SourceSnapshot], errors: list[str]
) -> None:
    path = "docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json"
    source = snapshots.get(path)
    if source is None:
        errors.append("task graph source snapshot is missing")
        return
    try:
        graph = _decode_json(source.data, path)
    except (json.JSONDecodeError, ValueError) as exc:
        errors.append(f"task graph is malformed: {exc}")
        return
    tasks = graph.get("tasks")
    if not isinstance(tasks, list):
        errors.append("task graph tasks are malformed")
        return
    g1 = next(
        (row for row in tasks if isinstance(row, Mapping) and row.get("id") == "G1"),
        None,
    )
    if not isinstance(g1, Mapping) or contract.EXPECTED_TASK_GRAPH_SUMMARY not in g1.get(
        "failing_evidence", []
    ):
        errors.append("task graph architecture summary differs from the checker-owned counts")


def _check_commands(
    document: Mapping[str, Any],
    snapshots: Mapping[str, SourceSnapshot],
    errors: list[str],
) -> None:
    rows = _rows_by_id(document.get("command_registry"), "command_registry", errors)
    if set(rows) != set(contract.EXPECTED_COMMANDS) or len(rows) != 33:
        errors.append(
            "COMMAND_ROUTE_CLOSURE: command registry is not the exact 33-command language"
        )
    for command_id, row in rows.items():
        if dict(row) != {"id": command_id, "source_semantics_id": command_id}:
            errors.append(f"command_registry[{command_id}] differs from its exact source binding")

    path = "docs/research/PRODUCTION_READINESS_G1_SEMANTICS_V1.json"
    source = snapshots.get(path)
    if source is None:
        errors.append("pinned G1 semantics source snapshot is missing")
        return
    try:
        semantics = _decode_json(source.data, path)
    except (json.JSONDecodeError, ValueError) as exc:
        errors.append(f"pinned G1 semantics is malformed: {exc}")
        return
    source_commands = semantics.get("command_registry")
    if not isinstance(source_commands, list):
        errors.append("pinned G1 semantics command_registry is malformed")
        return
    source_ids = {
        row.get("id")
        for row in source_commands
        if isinstance(row, Mapping) and isinstance(row.get("id"), str)
    }
    if source_ids != set(contract.EXPECTED_COMMANDS) or len(source_commands) != 33:
        errors.append("checker-owned commands differ from the pinned G1 semantics source")


def _check_simple_exact_registries(document: Mapping[str, Any], errors: list[str]) -> None:
    command_schemas = _rows_by_id(
        document.get("command_payload_schemas"), "command_payload_schemas", errors
    )
    if set(command_schemas) != set(contract.EXPECTED_COMMAND_PAYLOAD_SCHEMAS):
        errors.append("command_payload_schemas differ from the checker-owned registry")
    for command_id, row in command_schemas.items():
        expected = {"id": command_id, **contract.EXPECTED_COMMAND_PAYLOAD_SCHEMAS[command_id]}
        if dict(row) != expected:
            errors.append(f"command_payload_schemas[{command_id}] differs")

    intents = _rows_by_id(document.get("intent_registry"), "intent_registry", errors)
    if set(intents) != set(contract.EXPECTED_INTENTS):
        errors.append("intent_registry differs from the checker-owned intent language")
    for intent_id, row in intents.items():
        expected = {
            "id": intent_id,
            "owner": "SETTLEMENT_KERNEL",
            "stage": "PROPOSED",
            "external_effect": intent_id == "OUTBOX_ENQUEUE",
        }
        if dict(row) != expected:
            errors.append(f"intent_registry[{intent_id}] differs from its exact contract")

    intent_schemas = _rows_by_id(
        document.get("intent_payload_schemas"), "intent_payload_schemas", errors
    )
    if set(intent_schemas) != set(contract.EXPECTED_INTENT_PAYLOAD_SCHEMAS):
        errors.append("intent_payload_schemas differ from the checker-owned registry")
    for intent_id, row in intent_schemas.items():
        expected = {"id": intent_id, **contract.EXPECTED_INTENT_PAYLOAD_SCHEMAS[intent_id]}
        if dict(row) != expected:
            errors.append(f"intent_payload_schemas[{intent_id}] differs")

    views = _rows_by_id(document.get("view_registry"), "view_registry", errors)
    if set(views) != set(contract.EXPECTED_VIEW_SPECS):
        errors.append("view_registry differs from the checker-owned view registry")
    for view_id, row in views.items():
        if _without_id(row) != contract.EXPECTED_VIEW_SPECS.get(view_id):
            errors.append(f"view_registry[{view_id}] differs from its exact contract")

    constraints = _rows_by_id(
        document.get("route_constraint_registry"), "route_constraint_registry", errors
    )
    if set(constraints) != set(contract.EXPECTED_ROUTE_CONSTRAINT_SPECS):
        errors.append("route_constraint_registry differs from its checker-owned registry")
    for constraint_id, row in constraints.items():
        expected = {
            "id": constraint_id,
            "meaning": contract.EXPECTED_ROUTE_CONSTRAINT_SPECS.get(constraint_id),
        }
        if dict(row) != expected:
            errors.append(f"route_constraint_registry[{constraint_id}] differs")

    types = _rows_by_id(document.get("type_registry"), "type_registry", errors)
    if set(types) != set(contract.EXPECTED_TYPE_SPECS):
        errors.append("type_registry differs from the checker-owned closed types")
    for type_id, row in types.items():
        if dict(row) != contract.EXPECTED_TYPE_SPECS.get(type_id):
            errors.append(f"type_registry[{type_id}] differs from its exact closed type contract")
    representation = types.get("ResolvedTauRepresentationV2")
    required_tau_fields = {
        "asset_decimals",
        "scale_numerator",
        "scale_denominator",
        "rounding_mode",
        "dust_policy_id",
        "external_network_profile_root",
        "ingress_verifier_profile_root",
        "destination_adapter_root",
        "migration_policy_root",
        "recovery_policy_root",
        "permanence_anchor_root",
    }
    if representation is not None:
        field_specs = representation.get("field_specs")
        field_ids = {
            field.get("id")
            for field in field_specs
            if isinstance(field_specs, list) and isinstance(field, Mapping)
        } if isinstance(field_specs, list) else set()
        if not required_tau_fields <= field_ids:
            errors.append("TAU_QUANTITY_CONTRACT_OMITTED: Tau representation fields are incomplete")


def _check_variant_field_contracts(document: Mapping[str, Any], errors: list[str]) -> None:
    rows = _rows_by_id(document.get("type_registry"), "type_registry", errors)
    for type_id, row in rows.items():
        variants = set(row.get("variant_ids", []))
        discriminator = row.get("variant_discriminator")
        contracts = row.get("variant_field_contracts")
        field_specs = row.get("field_specs")
        if not isinstance(contracts, Mapping) or not isinstance(field_specs, list):
            errors.append(f"VARIANT_FIELD_CONTRACT_MISSING: {type_id} contract is malformed")
            continue
        field_ids = {
            field.get("id")
            for field in field_specs
            if isinstance(field, Mapping) and isinstance(field.get("id"), str)
        }
        optional_ids = {
            field.get("id")
            for field in field_specs
            if isinstance(field, Mapping)
            and field.get("cardinality") != "EXACTLY_ONE"
            and isinstance(field.get("id"), str)
        }
        if not variants:
            if discriminator is not None or contracts:
                errors.append(
                    f"VARIANT_FIELD_CONTRACT_MISSING: {type_id} has contracts without variants"
                )
            continue
        if discriminator not in field_ids or set(contracts) != variants:
            errors.append(
                f"VARIANT_FIELD_CONTRACT_MISSING: {type_id} variants lack exact contracts"
            )
            continue
        for variant_id, contract_row in contracts.items():
            if not isinstance(contract_row, Mapping) or set(contract_row) != {
                "required_field_ids",
                "forbidden_field_ids",
            }:
                errors.append(
                    f"VARIANT_FIELD_CONTRACT_MISSING: {type_id}.{variant_id} is malformed"
                )
                continue
            required = set(contract_row.get("required_field_ids", []))
            forbidden = set(contract_row.get("forbidden_field_ids", []))
            if (
                not required <= field_ids
                or not forbidden <= optional_ids
                or required & forbidden
                or discriminator not in required
                or not optional_ids <= required | forbidden
            ):
                errors.append(
                    f"VARIANT_FIELD_CONTRACT_MISSING: {type_id}.{variant_id} is incomplete"
                )
            if type_id == "ExecutionAdmissionV2":
                if variant_id == "ZRPF_ROOT" and "verified_zrpf_journal" not in required:
                    errors.append("ZRPF_WITNESS_OMITTED: ZRPF admission lacks verified journal")
                if variant_id == "DIRECT_EXECUTION" and (
                    "verified_zrpf_journal" not in forbidden
                ):
                    errors.append(
                        "DIRECT_CARRIES_ZRPF_WITNESS: direct admission permits ZRPF witness"
                    )
            if type_id == "VerifierExecutionProfileV2" and variant_id == "NATIVE_BACKUP":
                if not {
                    "equivalence_receipt_root",
                    "governance_authorization_root",
                } <= required:
                    errors.append(
                        "NATIVE_BACKUP_WITHOUT_GOVERNANCE_OR_EQUIVALENCE: "
                        "native backup evidence is optional"
                    )


def _check_state_domains(document: Mapping[str, Any], errors: list[str]) -> None:
    rows = _rows_by_id(document.get("state_domains"), "state_domains", errors)
    if set(rows) != set(contract.EXPECTED_STATE_OWNERS):
        errors.append("STATE_OWNERSHIP: state domains differ from the checker-owned registry")
    for domain_id, owner in contract.EXPECTED_STATE_OWNERS.items():
        row = rows.get(domain_id)
        if row is None:
            continue
        expected = {"id": domain_id, "semantic_owner": owner, "durable_writers": ["ZENO_LEDGER"]}
        if dict(row) != expected:
            errors.append(
                f"SECOND_DURABLE_WRITER or ownership mismatch: state_domains[{domain_id}] differs"
            )


def _check_modules(document: Mapping[str, Any], errors: list[str]) -> dict[str, Mapping[str, Any]]:
    rows = _rows_by_id(document.get("module_descriptors"), "module_descriptors", errors)
    if set(rows) != set(contract.EXPECTED_MODULE_SPECS):
        errors.append("module_descriptors differ from the checker-owned module registry")
    edges: dict[str, list[str]] = {}
    for module_id, row in rows.items():
        expected = contract.EXPECTED_MODULE_SPECS.get(module_id)
        if expected is None:
            continue
        if _without_id(row) != expected:
            errors.append(f"module_descriptors[{module_id}] differs from its exact contract")
        dependencies = _string_list(
            row.get("build_depends_on"),
            f"module_descriptors[{module_id}].build_depends_on",
            errors,
        )
        if any(dependency not in rows for dependency in dependencies):
            errors.append(
                f"UNPORTED_DEPENDENCY: module_descriptors[{module_id}] has unknown build dependency"
            )
        edges[module_id] = dependencies
        owned = set(
            _string_list(
                row.get("owned_state_domains"),
                f"module_descriptors[{module_id}].owned_state_domains",
                errors,
            )
        )
        writes = set(
            _string_list(
                row.get("proposal_write_domains"),
                f"module_descriptors[{module_id}].proposal_write_domains",
                errors,
            )
        )
        if not writes <= owned:
            errors.append(
                f"FOREIGN_PROPOSAL_WRITE: module_descriptors[{module_id}] writes foreign state"
            )
        allowed_intents = set(
            _string_list(
                row.get("allowed_intent_ids"),
                f"module_descriptors[{module_id}].allowed_intent_ids",
                errors,
            )
        )
        if not allowed_intents <= set(contract.EXPECTED_INTENTS):
            errors.append(
                f"UNKNOWN_INTENT: module_descriptors[{module_id}] uses an unknown intent"
            )
    if _has_cycle(edges):
        errors.append("DEPENDENCY_CYCLE: module build dependency graph is cyclic")
    return rows


def _check_intent_capabilities(
    document: Mapping[str, Any],
    modules: Mapping[str, Mapping[str, Any]],
    errors: list[str],
) -> None:
    rows = _rows_by_id(document.get("intent_capabilities"), "intent_capabilities", errors)
    if set(rows) != set(contract.EXPECTED_INTENT_CAPABILITIES):
        errors.append("intent_capabilities differ from the checker-owned capability matrix")
    by_module: dict[str, set[str]] = {module_id: set() for module_id in modules}
    for capability_id, row in rows.items():
        expected = contract.EXPECTED_INTENT_CAPABILITIES.get(capability_id)
        if expected is None:
            continue
        if _without_id(row) != expected:
            errors.append(f"intent_capabilities[{capability_id}] differs from its exact scope")
        intent_id = row.get("intent_id")
        if row.get("asset_scope") != expected["asset_scope"]:
            if intent_id == "AUTHORIZED_ISSUE":
                errors.append(f"ISSUE_WRONG_ASSET: {capability_id} asset scope differs")
            elif intent_id == "AUTHORIZED_BURN":
                errors.append(f"BURN_WRONG_ASSET: {capability_id} asset scope differs")
        if (
            intent_id == "LEDGER_TRANSFER"
            and row.get("account_role_scope") != expected["account_role_scope"]
        ):
            errors.append(
                f"TRANSFER_WRONG_CUSTODY_ROLE: {capability_id} account-role scope differs"
            )
        module_id = row.get("module_id")
        if isinstance(module_id, str) and isinstance(intent_id, str):
            by_module.setdefault(module_id, set()).add(intent_id)
    for module_id, row in modules.items():
        declared = set(row.get("allowed_intent_ids", []))
        if declared != by_module.get(module_id, set()):
            errors.append(
                f"intent_capabilities for {module_id} do not exactly cover allowed_intent_ids"
            )


def _check_one_port(
    port_id: str,
    row: Mapping[str, Any],
    modules: Mapping[str, Mapping[str, Any]],
    participation: dict[str, set[str]],
    errors: list[str],
) -> None:
    if _without_id(row) != contract.EXPECTED_PORT_SPECS[port_id]:
        errors.append(f"port_contracts[{port_id}] differs from its exact checker-owned contract")
    caller, callee = row.get("caller"), row.get("callee")
    if caller not in modules or callee not in modules:
        errors.append(f"DEPENDENCIES_HAVE_TYPED_PORTS: {port_id} has an unknown endpoint")
    else:
        participation[str(caller)].add(port_id)
        participation[str(callee)].add(port_id)
    if row.get("request_type") not in contract.EXPECTED_TYPE_SPECS:
        errors.append(f"PORT_TYPE_ANY: {port_id} request type is outside the closed registry")
    if row.get("response_type") not in contract.EXPECTED_TYPE_SPECS:
        errors.append(f"PORT_TYPE_ANY: {port_id} response type is outside the closed registry")
    request_guarantees = set(
        _string_list(row.get("request_guarantees"), f"{port_id}.request_guarantees", errors)
    )
    request_assumptions = set(
        _string_list(
            row.get("callee_request_assumptions"), f"{port_id}.callee_request_assumptions", errors
        )
    )
    response_guarantees = set(
        _string_list(row.get("response_guarantees"), f"{port_id}.response_guarantees", errors)
    )
    response_assumptions = set(
        _string_list(
            row.get("caller_response_assumptions"), f"{port_id}.caller_response_assumptions", errors
        )
    )
    all_atoms = (
        request_guarantees | request_assumptions | response_guarantees | response_assumptions
    )
    if not all_atoms <= set(contract.CONTRACT_ATOMS):
        errors.append(f"ASSUMPTION_TOKEN_INVENTED: {port_id} uses an unknown contract atom")
    if not request_assumptions <= request_guarantees:
        errors.append(f"PORT_ASSUMPTION_NOT_GUARANTEED: {port_id} request implication fails")
    if not response_assumptions <= response_guarantees:
        errors.append(f"PORT_ASSUMPTION_NOT_GUARANTEED: {port_id} response implication fails")
    if row.get("caller_constructible_authority") is not False:
        errors.append(f"CALLER_CONSTRUCTED_AUTHORITY: {port_id} permits authority construction")
        if port_id == "P_GOVERNANCE_AUTHORIZATION":
            errors.append(
                "CALLER_CONSTRUCTED_GOVERNANCE_AUTHORITY: governance witness is caller-constructible"
            )
    if port_id == "P_RELEASE_CONTROL" and row.get("request_type") != (
        "AuthorizedReleaseControlRequestV2"
    ):
        errors.append(
            "GOVERNANCE_WITNESS_DROPPED_DOWNSTREAM: release control lacks opaque authorization"
        )
    if port_id == "P_POLICY_CONTROL" and row.get("request_type") != (
        "AuthorizedPolicyControlRequestV2"
    ):
        errors.append(
            "GOVERNANCE_WITNESS_DROPPED_DOWNSTREAM: policy control lacks opaque authorization"
        )
    if port_id == "P_OUTBOX_ACK_SUBMISSION" and (
        "WRITER_EPOCH_BOUND" not in request_guarantees
        or "WRITER_EPOCH_BOUND" not in request_assumptions
        or "WRITER_EPOCH_BOUND" not in response_guarantees
        or "WRITER_EPOCH_BOUND" not in response_assumptions
    ):
        errors.append("ACK_EPOCH_OMITTED: acknowledgment writer epoch is unbound")


def _check_runtime_port_participation(
    modules: Mapping[str, Mapping[str, Any]],
    participation: Mapping[str, set[str]],
    errors: list[str],
) -> None:
    for module_id, row in modules.items():
        declared = set(
            _string_list(
                row.get("runtime_port_ids"),
                f"module_descriptors[{module_id}].runtime_port_ids",
                errors,
            )
        )
        if declared != participation.get(module_id, set()):
            errors.append(
                f"UNPORTED_DEPENDENCY: module_descriptors[{module_id}] runtime ports differ from endpoints"
            )


def _check_ports(
    document: Mapping[str, Any], modules: Mapping[str, Mapping[str, Any]], errors: list[str]
) -> int:
    rows = _rows_by_id(document.get("port_contracts"), "port_contracts", errors)
    if set(rows) != set(contract.EXPECTED_PORT_SPECS):
        errors.append("DEPENDENCIES_HAVE_TYPED_PORTS: port registry differs")
    participation: dict[str, set[str]] = {module_id: set() for module_id in modules}
    for port_id, row in rows.items():
        if port_id in contract.EXPECTED_PORT_SPECS:
            _check_one_port(port_id, row, modules, participation, errors)
    _check_runtime_port_participation(modules, participation, errors)
    return 2 * len(rows)


def _route_step_cycle(steps: Sequence[Mapping[str, Any]]) -> bool:
    indexes = {step.get("step_index") for step in steps if isinstance(step.get("step_index"), int)}
    edges: dict[str, list[str]] = {}
    for step in steps:
        index = step.get("step_index")
        dependencies = step.get("depends_on_step_indexes")
        if not isinstance(index, int) or not isinstance(dependencies, list):
            return True
        if any(
            not isinstance(dependency, int) or dependency not in indexes
            for dependency in dependencies
        ):
            return True
        edges[str(index)] = [str(dependency) for dependency in dependencies]
    return _has_cycle(edges)


def _canonical_route_order(steps: Sequence[Mapping[str, Any]]) -> list[int]:
    pending = {int(step["step_index"]): step for step in steps}
    emitted: list[int] = []
    emitted_set: set[int] = set()
    while pending:
        ready = [
            (index, step)
            for index, step in pending.items()
            if set(step.get("depends_on_step_indexes", [])) <= emitted_set
        ]
        if not ready:
            return []
        index, _ = min(ready, key=lambda item: (str(item[1].get("module_id")), item[0]))
        emitted.append(index)
        emitted_set.add(index)
        pending.pop(index)
    return emitted


def _check_route_steps(
    command_id: str,
    row: Mapping[str, Any],
    modules: Mapping[str, Mapping[str, Any]],
    errors: list[str],
) -> tuple[set[str], set[str], set[str] | None, set[str], set[str]] | None:
    raw_steps = row.get("steps")
    if (
        not isinstance(raw_steps, list)
        or not raw_steps
        or not all(isinstance(step, Mapping) for step in raw_steps)
    ):
        errors.append(f"routes[{command_id}].steps must be a nonempty typed route")
        return None
    steps = list(raw_steps)
    indexes = [step.get("step_index") for step in steps]
    route_shape_valid = indexes == list(range(len(steps))) and not _route_step_cycle(steps)
    if not route_shape_valid:
        errors.append(f"routes[{command_id}] route-step DAG or canonical index order differs")
    elif _canonical_route_order(steps) != indexes:
        errors.append(f"routes[{command_id}] canonical topological/module order differs")
    route_modules: set[str] = set()
    allowed_intents: set[str] = set()
    accepted_views: set[str] | None = None
    assigned_required: set[str] = set()
    assigned_optional: set[str] = set()
    for step in steps:
        module_id = str(step.get("module_id"))
        route_modules.add(module_id)
        module = modules.get(module_id)
        if module is None:
            errors.append(f"routes[{command_id}] step references unknown module")
            continue
        if step.get("evaluation_port_id") != f"P_{module_id}_EVALUATION":
            errors.append(f"UNPORTED_DEPENDENCY: routes[{command_id}] step port differs")
        allowed_intents.update(module.get("allowed_intent_ids", []))
        step_required = set(
            _string_list(
                step.get("required_intent_ids"),
                f"routes[{command_id}].steps[{step.get('step_index')}].required_intent_ids",
                errors,
            )
        )
        step_optional = set(
            _string_list(
                step.get("optional_intent_ids"),
                f"routes[{command_id}].steps[{step.get('step_index')}].optional_intent_ids",
                errors,
            )
        )
        module_intents = set(module.get("allowed_intent_ids", []))
        if step_required & step_optional or not step_required | step_optional <= module_intents:
            errors.append(
                f"ROUTE_STEP_STEALS_INTENT: routes[{command_id}] assigns an intent to the wrong step"
            )
        assigned_required.update(step_required)
        assigned_optional.update(step_optional)
        module_views = set(module.get("accepted_view_ids", []))
        accepted_views = module_views if accepted_views is None else accepted_views & module_views
    return route_modules, allowed_intents, accepted_views, assigned_required, assigned_optional


def _check_route_capabilities(
    command_id: str,
    row: Mapping[str, Any],
    route_modules: set[str],
    allowed_intents: set[str],
    accepted_views: set[str] | None,
    assigned_required: set[str],
    assigned_optional: set[str],
    errors: list[str],
) -> None:
    required_views = set(
        _string_list(
            row.get("required_view_ids"), f"routes[{command_id}].required_view_ids", errors
        )
    )
    if not required_views <= set(contract.EXPECTED_VIEW_IDS):
        errors.append(f"routes[{command_id}] requires an unknown view")
    if accepted_views is not None and not required_views <= accepted_views:
        errors.append(f"routes[{command_id}] passes a view a participant did not accept")
    required_intents = set(
        _string_list(
            row.get("required_intent_ids"), f"routes[{command_id}].required_intent_ids", errors
        )
    )
    optional_intents = set(
        _string_list(
            row.get("optional_intent_ids"), f"routes[{command_id}].optional_intent_ids", errors
        )
    )
    if not required_intents | optional_intents <= set(contract.EXPECTED_INTENTS):
        errors.append(f"UNKNOWN_INTENT: routes[{command_id}] uses an unknown intent")
    if (
        required_intents & optional_intents
        or not required_intents | optional_intents <= allowed_intents
    ):
        errors.append(f"ROUTE_INTENT_EXCEEDS_CAPABILITY: routes[{command_id}] intent shape differs")
    if required_intents != assigned_required or optional_intents != assigned_optional:
        errors.append(
            f"ROUTE_STEP_STEALS_INTENT: routes[{command_id}] step intent assignment differs"
        )
    constraints = set(
        _string_list(row.get("constraint_ids"), f"routes[{command_id}].constraint_ids", errors)
    )
    if not constraints <= set(contract.EXPECTED_ROUTE_CONSTRAINT_IDS):
        errors.append(f"routes[{command_id}] uses an unknown constraint")
    release_participants = set(
        _string_list(
            row.get("release_participant_module_ids"),
            f"routes[{command_id}].release_participant_module_ids",
            errors,
        )
    )
    expected_release_participants = set(route_modules)
    if "AUTHENTICATED_ORACLE_VIEW" in required_views:
        expected_release_participants.add("ORACLE_MODULE")
    if release_participants != expected_release_participants:
        errors.append(f"OCCURRENCE_OMITS_RELEASE_SET: routes[{command_id}] release set differs")


def _check_one_route(
    command_id: str,
    row: Mapping[str, Any],
    modules: Mapping[str, Mapping[str, Any]],
    errors: list[str],
) -> None:
    expected_route = contract.EXPECTED_ROUTE_SPECS[command_id]
    if _without_id(row) != expected_route:
        errors.append(f"routes[{command_id}] differs from its exact checker-owned route")
    if row.get("steps") != expected_route.get("steps"):
        errors.append(
            f"ROUTE_STEP_STEALS_INTENT: routes[{command_id}] step contract differs"
        )
    expected_owner = next(
        module_id
        for module_id, command_ids in contract.EXPECTED_MODULE_COMMANDS.items()
        if command_id in command_ids
    )
    if row.get("primary_module_id") != expected_owner:
        errors.append(f"COMMAND_WRONG_MODULE: routes[{command_id}] primary owner differs")
    capabilities = _check_route_steps(command_id, row, modules, errors)
    if capabilities is not None:
        _check_route_capabilities(command_id, row, *capabilities, errors)


def _check_routes(
    document: Mapping[str, Any], modules: Mapping[str, Mapping[str, Any]], errors: list[str]
) -> None:
    rows = _rows_by_id(document.get("routes"), "routes", errors)
    if set(rows) != set(contract.EXPECTED_ROUTE_SPECS) or len(rows) != 33:
        errors.append("COMMAND_ROUTE_CLOSURE: routes do not cover the exact 33 commands")
    for command_id, row in rows.items():
        if command_id in contract.EXPECTED_ROUTE_SPECS:
            _check_one_route(command_id, row, modules, errors)

    tau_module = modules.get("TAU_ESCROW_MODULE", {})
    forbidden_control_intents = {
        "MODULE_RELEASE_LIFECYCLE_CHANGE",
        "POLICY_PROFILE_CHANGE",
    }
    if set(tau_module.get("allowed_intent_ids", [])) & forbidden_control_intents:
        errors.append("TAU_ESCALATES_TO_RELEASE_CONTROL: Tau module has governed control authority")
    for command_id in ("fallback_activate", "tau_rejoin"):
        row = rows.get(command_id, {})
        intents = set(row.get("required_intent_ids", [])) | set(
            row.get("optional_intent_ids", [])
        )
        if intents & forbidden_control_intents or "TAU_CONNECTIVITY_MODE_CHANGE" not in intents:
            errors.append(
                f"TAU_ESCALATES_TO_RELEASE_CONTROL: routes[{command_id}] control intent differs"
            )
    for command_id in ("tau_escrow_deposit", "tau_withdrawal", "tau_withdrawal_ack"):
        row = rows.get(command_id, {})
        if "RESOLVED_TAU_REPRESENTATION" not in row.get("required_view_ids", []):
            errors.append(
                f"TAU_REPRESENTATION_UNRESOLVED: routes[{command_id}] lacks resolved representation"
            )


def _check_composition_core(value: Mapping[str, Any], errors: list[str]) -> None:
    if value.get("batch_command_order") != "COMMAND_INDEX_ASCENDING":
        errors.append("COMMAND_ORDER_AFTER_MODULE_ORDER: batch order differs")
    if value.get("route_step_order") != "TOPOLOGICAL_THEN_MODULE_ID_ASCENDING":
        errors.append("PORT_ORDER_ARRIVAL: route-step order differs")
    if (
        value.get("value_delta_source") != "DERIVED_FROM_STAGED_PRE_POST"
        or value.get("module_delta_authoritative") is not False
    ):
        errors.append("TRUST_MODULE_DELTA: value delta authority differs")
    if value.get("drain_primary_object_creation_allowed") is not False:
        errors.append("DRAIN_CREATES_OBJECT: release drain contract differs")
    occurrence_fields = value.get("occurrence_identity_fields")
    if not isinstance(occurrence_fields, list) or set(occurrence_fields) != set(
        contract.REQUIRED_OCCURRENCE_FIELDS
    ):
        errors.append("OCCURRENCE_OMITS_RELEASE_SET: occurrence identity is incomplete")
    if value.get("epoch_control_commit_capability") != "ZENO_LEDGER_SUBMIT_V2":
        errors.append("RELEASE_CONTROL_BYPASS: epoch control bypasses ZenoLedger")
    authoritative_inputs = value.get("authoritative_input_sum")
    if not isinstance(authoritative_inputs, Mapping):
        errors.append("EPOCH_CONTROL_UNTYPED: authoritative input sum is absent")
    else:
        variants = authoritative_inputs.get("variants")
        ingress_ports = {
            row.get("ingress_port_id")
            for row in variants
            if isinstance(variants, list) and isinstance(row, Mapping)
        } if isinstance(variants, list) else set()
        if ingress_ports != {
            "P_SETTLEMENT_EXECUTION",
            "P_GOVERNED_CONTROL_INGRESS",
            "P_ZRPF_ROOT_INGRESS",
        } or authoritative_inputs.get("other_authoritative_inputs_allowed") is not False:
            errors.append("EPOCH_CONTROL_UNTYPED: authoritative input sum differs")
    control = value.get("epoch_control_contract")
    if not isinstance(control, Mapping):
        errors.append("EPOCH_CONTROL_UNTYPED: governed control contract is absent")
    else:
        if control.get("authorization_port_id") != "P_GOVERNANCE_AUTHORIZATION":
            errors.append(
                "CALLER_CONSTRUCTED_GOVERNANCE_AUTHORITY: governed control authorization differs"
            )
        if control.get("partial_commit_possible") is not False:
            errors.append("POLICY_RELEASE_PARTIAL_COMMIT: governed control can partially commit")
        if (
            control.get("publication_port_id") != "P_SETTLEMENT_PUBLICATION"
            or control.get("commit_capability") != "ZENO_LEDGER_SUBMIT_V2"
        ):
            errors.append("RELEASE_CONTROL_BYPASS: governed control publication differs")
        if control.get("tau_connectivity_change_forbidden") is not True:
            errors.append(
                "TAU_ESCALATES_TO_RELEASE_CONTROL: governed release/policy control includes Tau mode"
            )
        allowed_changes = control.get("allowed_changes")
        request_types = {
            row.get("request_type")
            for row in allowed_changes
            if isinstance(allowed_changes, list) and isinstance(row, Mapping)
        } if isinstance(allowed_changes, list) else set()
        if request_types != {
            "AuthorizedReleaseControlRequestV2",
            "AuthorizedPolicyControlRequestV2",
        }:
            errors.append(
                "GOVERNANCE_WITNESS_DROPPED_DOWNSTREAM: control request types differ"
            )


def _check_composition_verifier(value: Mapping[str, Any], errors: list[str]) -> None:
    verifier = value.get("verifier")
    if not isinstance(verifier, Mapping):
        return
    if verifier.get("mismatch_policy") != "REJECT":
        errors.append("VERIFIER_MISMATCH_FAILS_OPEN: verifier disagreement policy differs")
    if verifier.get("unknown_timeout_policy") != "REJECT":
        errors.append("SOLVER_UNKNOWN_ACCEPTED: verifier timeout policy differs")
    if verifier.get("profile_binding_required") is not True:
        errors.append("VERIFIER_PROFILE_SUBSTITUTION: verifier profile binding is optional")
    if verifier.get("self_attested_evidence_allowed") is not False:
        errors.append("SELF_ATTESTED_EVIDENCE: verifier accepts self-attestation")
    expected_profiles = [
        {
            "id": "NATIVE_ONLY",
            "required_backend_ids": ["NATIVE"],
            "fallback_backend_ids": [],
            "allowed_active_modes": ["NATIVE"],
            "equivalence_receipt_required": False,
        },
        {
            "id": "NATIVE_AND_TAU",
            "required_backend_ids": ["NATIVE", "TAU"],
            "fallback_backend_ids": [],
            "allowed_active_modes": ["NATIVE_AND_TAU"],
            "equivalence_receipt_required": True,
        },
        {
            "id": "TAU_PRIMARY_NATIVE_GOVERNED_FAILOVER",
            "normal_backend_ids": ["TAU"],
            "outage_backend_ids": ["NATIVE"],
            "allowed_active_modes": ["TAU_PRIMARY", "NATIVE_BACKUP"],
            "native_backup_activation_authority": "GOVERNED_POLICY_CONTROL_ONLY",
            "governed_mode_switch_required": True,
            "same_profile_equivalence_receipt_required": True,
            "silent_per_query_fallback_allowed": False,
        },
    ]
    if (
        verifier.get("execution_profiles") != expected_profiles
        or verifier.get("implicit_backend_fallback_allowed") is not False
        or verifier.get("required_receipt_set_exact") is not True
    ):
        errors.append("VERIFIER_MISMATCH_FAILS_OPEN: verifier execution cardinality differs")
    required_profile_binding = {
        "execution_profile_type": "VerifierExecutionProfileV2",
        "active_profile_state_domain": "POLICY_PROFILE_REGISTRY",
        "active_profile_owner": "POLICY_KERNEL",
        "profile_change_port_id": "P_POLICY_CONTROL",
        "backend_selection_source": "EPOCH_BOUND_VERIFIED_PROFILE",
        "per_query_backend_override_allowed": False,
    }
    if any(
        verifier.get(key) != expected for key, expected in required_profile_binding.items()
    ):
        errors.append(
            "TAU_FAILOVER_PER_QUERY_SWITCH: verifier execution profile is not epoch-bound"
        )
    failover = next(
        (
            row
            for row in verifier.get("execution_profiles", [])
            if isinstance(row, Mapping)
            and row.get("id") == "TAU_PRIMARY_NATIVE_GOVERNED_FAILOVER"
        ),
        None,
    )
    if not isinstance(failover, Mapping) or (
        failover.get("governed_mode_switch_required") is not True
        or failover.get("same_profile_equivalence_receipt_required") is not True
        or failover.get("silent_per_query_fallback_allowed") is not False
        or failover.get("native_backup_activation_authority")
        != "GOVERNED_POLICY_CONTROL_ONLY"
    ):
        errors.append("TAU_FAILOVER_UNGOVERNED: Tau/native failover contract differs")


def _check_composition_formal(value: Mapping[str, Any], errors: list[str]) -> None:
    formal = value.get("formal_verification")
    if not isinstance(formal, Mapping):
        return
    required = {
        "esso_status": "REQUIRED_NOT_IMPLEMENTED",
        "esso_solvers": ["Z3", "CVC5"],
        "esso_agreement_required": True,
        "esso_unknown_timeout_disagreement_policy": "REJECT",
        "port_implication_expected_result": "UNSAT_BOTH_SOLVERS",
        "lean_status": "REQUIRED_NOT_IMPLEMENTED",
    }
    for key, expected in required.items():
        if formal.get(key) != expected:
            errors.append(f"formal_verification.{key} differs from the mandatory fail-closed lane")


def _check_composition_effects(value: Mapping[str, Any], errors: list[str]) -> None:
    effects = value.get("effects")
    if not isinstance(effects, Mapping):
        return
    if effects.get("dispatch_stage") != "AFTER_HEAD_COMMIT":
        errors.append("EXTERNAL_EFFECT_BEFORE_COMMIT: dispatch stage differs")
    if effects.get("outbox_shell_economic_mutation_allowed") is not False:
        errors.append("ACK_MUTATES_FROM_SHELL: outbox shell has economic authority")
    fields = effects.get("idempotency_fields")
    if not isinstance(fields, list) or "PUBLICATION_ROOT" not in fields:
        errors.append("OUTBOX_ID_OMITS_PUBLICATION: effect identity is incomplete")
    if (
        effects.get("ack_command_id") != "tau_withdrawal_ack"
        or effects.get("ack_reentry_port_id") != "P_SETTLEMENT_EXECUTION"
    ):
        errors.append("ACK_BYPASSES_SETTLEMENT: acknowledgment re-entry differs")


def _schema_path_exists(path: object) -> bool:
    if not isinstance(path, str):
        return False
    parts = path.split(".")
    if len(parts) < 2:
        return False
    current_type = parts[0]
    for index, field_id in enumerate(parts[1:]):
        type_spec = contract.EXPECTED_TYPE_SPECS.get(current_type)
        if not isinstance(type_spec, Mapping):
            return False
        field_spec = next(
            (
                row
                for row in type_spec.get("field_specs", [])
                if isinstance(row, Mapping) and row.get("id") == field_id
            ),
            None,
        )
        if not isinstance(field_spec, Mapping):
            return False
        if index == len(parts[1:]) - 1:
            return True
        value_type = field_spec.get("value_type")
        if not isinstance(value_type, str):
            return False
        current_type = value_type
    return False


def _check_composition_zrpf(value: Mapping[str, Any], errors: list[str]) -> None:
    zrpf = value.get("zrpf_admission_contract")
    if not isinstance(zrpf, Mapping):
        errors.append("ZRPF_BYPASSES_SHARED_COMMIT: proof admission contract is absent")
        return
    required = {
        "ingress_port_id": "P_ZRPF_ROOT_INGRESS",
        "verification_port_id": "P_ZRPF_PROOF_VERIFICATION",
        "publication_port_id": "P_SETTLEMENT_PUBLICATION",
        "commit_capability": "ZENO_LEDGER_SUBMIT_V2",
        "separate_zrpf_writer_allowed": False,
        "current_head_recheck_required": True,
        "exact_journal_bytes_required": True,
        "release_selected_image_required": True,
        "execution_admission_type": "ExecutionAdmissionV2",
        "verified_witness_type": "VerifiedZRPFJournalV2",
    }
    if any(zrpf.get(key) != expected for key, expected in required.items()):
        errors.append("ZRPF_BYPASSES_SHARED_COMMIT: proof admission authority differs")
    fields = zrpf.get("witness_candidate_equality_fields")
    if not isinstance(fields, list) or set(fields) != set(
        contract.REQUIRED_ZRPF_ADMISSION_BINDING_FIELDS
    ):
        errors.append(
            "ZRPF_WITNESS_CANDIDATE_SUBSTITUTION: witness/candidate bindings are incomplete"
        )
    expected_paths = {
        token: list(paths)
        for token, paths in sorted(contract.EXPECTED_ZRPF_BINDING_SCHEMA_PATHS.items())
    }
    binding_paths = zrpf.get("binding_schema_paths")
    if binding_paths != expected_paths or any(
        len(paths) < 2 or any(not _schema_path_exists(path) for path in paths)
        for paths in expected_paths.values()
    ):
        errors.append(
            "ZRPF_BINDING_PATH_UNREALIZABLE: equality bindings do not resolve on both schemas"
        )


def _check_candidate_publication(value: Mapping[str, Any], errors: list[str]) -> None:
    publication = value.get("candidate_publication_contract")
    if not isinstance(publication, Mapping):
        errors.append("PUBLICATION_DUPLICATE_BINDING: candidate publication contract is absent")
        return
    required = {
        "execution_admission_constructor": "SETTLEMENT_KERNEL_ONLY",
        "execution_admission_required": True,
        "candidate_contains_admission_once": True,
        "publication_embeds_candidate_once": True,
        "duplicated_history_nullifier_proof_effect_fields": False,
        "value_delta_certificate_root_equals_commitment": True,
        "candidate_root_recomputed_by_writer": True,
        "publication_port_id": "P_SETTLEMENT_PUBLICATION",
    }
    if any(publication.get(key) != expected for key, expected in required.items()):
        errors.append("PUBLICATION_DUPLICATE_BINDING: candidate/publication storage differs")


def _check_composition_migration(value: Mapping[str, Any], errors: list[str]) -> None:
    migration = value.get("migration")
    if not isinstance(migration, Mapping):
        return
    classes = migration.get("classification_variants")
    if not isinstance(classes, list) or set(classes) != set(contract.REQUIRED_MIGRATION_CLASSES):
        errors.append("MIGRATION_CLASS_OMITTED: migration partition differs")
    kinds = migration.get("object_kind_registry")
    if not isinstance(kinds, list) or set(kinds) != set(contract.REQUIRED_MIGRATION_OBJECT_KINDS):
        errors.append("MIGRATION_OBJECT_KIND_OMITTED: migration object inventory differs")


def _check_composition(document: Mapping[str, Any], errors: list[str]) -> None:
    value = document.get("composition_contract")
    if value != contract.EXPECTED_COMPOSITION:
        errors.append("composition_contract differs from its exact checker-owned contract")
    if not isinstance(value, Mapping):
        return
    _check_composition_core(value, errors)
    _check_composition_verifier(value, errors)
    _check_composition_formal(value, errors)
    _check_composition_effects(value, errors)
    _check_composition_migration(value, errors)
    _check_composition_zrpf(value, errors)
    _check_candidate_publication(value, errors)

    if value.get("direct_core_id") != value.get("zrpf_core_id"):
        errors.append("DIRECT_GUEST_CORE_MISMATCH: direct and guest core identities differ")
    if value.get("mounted_writer_capabilities") != ["ZENO_LEDGER_SUBMIT_V2"]:
        errors.append("SECOND_DURABLE_WRITER: mounted writer capabilities differ")


def _check_evidence(document: Mapping[str, Any], errors: list[str]) -> None:
    rows = _rows_by_id(document.get("evidence_gates"), "evidence_gates", errors)
    if set(rows) != set(contract.EVIDENCE_GATES):
        errors.append("evidence_gates differ from the checker-owned evidence registry")
    for gate_id, row in rows.items():
        expected_gate = contract.EVIDENCE_GATES.get(gate_id)
        if expected_gate is None:
            continue
        minimum_grade, structural_status = expected_gate
        expected = {
            "id": gate_id,
            "minimum_grade": minimum_grade,
            "structural_status": structural_status,
            "evidence_status": "UNVERIFIED",
            "evidence_refs": [],
        }
        if dict(row) != expected:
            errors.append(
                f"SELF_ATTESTED_EVIDENCE: evidence_gates[{gate_id}] must remain unverified"
            )


def _check_mutants_and_nonclaims(document: Mapping[str, Any], errors: list[str]) -> None:
    rows = _rows_by_id(document.get("named_mutants"), "named_mutants", errors)
    if set(rows) != set(contract.EXPECTED_MUTANTS):
        errors.append("named_mutants differ from the checker-owned registry")
    for mutant_id, row in rows.items():
        _exact_keys(
            row,
            {"id", "description", "expected_detection"},
            f"named_mutants[{mutant_id}]",
            errors,
        )
        if not isinstance(row.get("description"), str) or not row["description"].strip():
            errors.append(f"named_mutants[{mutant_id}] description must be nonempty")
    if document.get("nonclaims") != list(contract.EXPECTED_NONCLAIMS):
        errors.append("nonclaims differ from the checker-owned claim ceiling")


def check_document(document: Mapping[str, Any], repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    snapshots = _read_source_snapshot(repo_root, errors)
    _exact_keys(document, contract.ROOT_KEYS, "artifact", errors)
    if document.get("schema") != contract.SCHEMA:
        errors.append("wrong schema")
    if document.get("status") != "STRUCTURALLY_SPECIFIED_RESEARCH_ONLY":
        errors.append("status must remain structurally specified research-only")
    if document.get("production_promotion") is not False:
        errors.append("production_promotion must remain false")
    if document.get("architecture_selected") is not False:
        errors.append("ADVISORY_SELECTION: architecture_selected must remain false")

    _check_subject(document, repo_root, errors)
    _check_source_pins(document, snapshots, errors)
    _check_contract_execution_snapshot(snapshots, errors)
    _check_verifier_bootstrap(document, errors)
    _check_task_graph_summary(snapshots, errors)
    _check_parent(document, snapshots, errors)
    _check_commands(document, snapshots, errors)
    _check_simple_exact_registries(document, errors)
    _check_variant_field_contracts(document, errors)
    _check_state_domains(document, errors)
    modules = _check_modules(document, errors)
    _check_intent_capabilities(document, modules, errors)
    implication_count = _check_ports(document, modules, errors)
    _check_routes(document, modules, errors)
    _check_composition(document, errors)
    _check_evidence(document, errors)
    _check_mutants_and_nonclaims(document, errors)
    _check_snapshot_unchanged(repo_root, snapshots, errors)

    return {
        "schema": contract.CHECK_SCHEMA,
        "ok": not errors,
        "error_count": len(errors),
        "errors": errors,
        "command_count": len(contract.EXPECTED_COMMANDS),
        "module_count": len(modules),
        "state_domain_count": len(contract.EXPECTED_STATE_OWNERS),
        "type_count": len(contract.EXPECTED_TYPE_SPECS),
        "intent_capability_count": len(contract.EXPECTED_INTENT_CAPABILITIES),
        "command_payload_schema_closed_count": 0,
        "authoritative_input_variant_count": 3,
        "governed_control_variant_count": 3,
        "nested_abi_complete": False,
        "port_count": len(contract.EXPECTED_PORT_IDS),
        "restricted_implication_direction_count": implication_count,
        "route_count": len(contract.EXPECTED_ROUTE_SPECS),
        "named_mutant_count": len(contract.EXPECTED_MUTANTS),
        "esso_required": True,
        "esso_verified": False,
        "lean_required": True,
        "lean_verified": False,
        "verifier_bootstrap_verified": False,
        "structurally_specified": not errors,
        "promotion_eligible": False,
        "architecture_selected": False,
        "production_ready": False,
    }


def check_artifact(path: Path = DEFAULT_ARTIFACT) -> dict[str, Any]:
    try:
        document = _load(path)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        return {
            "schema": contract.CHECK_SCHEMA,
            "ok": False,
            "error_count": 1,
            "errors": [str(exc)],
            "verifier_bootstrap_verified": False,
            "promotion_eligible": False,
            "architecture_selected": False,
            "production_ready": False,
        }
    return check_document(document, path.resolve().parents[2])


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--json", action="store_true", dest="as_json")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    report = check_artifact(args.artifact)
    if args.as_json:
        json.dump(report, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    elif report["ok"]:
        print(
            "architecture candidate V2: PASS "
            f"({report['command_count']} commands; {report['module_count']} modules; "
            f"{report['port_count']} ports; ESSO/Lean open; selected=false)"
        )
    else:
        print("architecture candidate V2: FAIL", file=sys.stderr)
        for error in report["errors"]:
            print(f"- {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
