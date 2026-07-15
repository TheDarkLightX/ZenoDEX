#!/usr/bin/env python3
"""Plan and verify a bounded, authority-neutral ZRPF remote reproof handoff.

The handoff is a content-addressed execution contract.  It contains no proof
bytes and runs no prover.  A worker must return every declared artifact, exact
program identities, literal C0 -> C1 -> C2 -> G ancestry, and content-bound
task-capture records before the return bundle is accepted.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import selectors
import signal
import stat
import subprocess
import sys
import time
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, NoReturn, Sequence

if __package__ in {None, ""}:  # pragma: no cover - direct script execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as identity
from tools import run_zrpf_remote_worker_prover_build_stage_v2 as worker_build
from tools import zrpf_remote_reproof_handoff_v2_catalog as catalog
from tools.zrpf_remote_reproof_handoff_v2_catalog import (
    ARTIFACT_SPECS,
    CPU_PROVER_COMPUTE_PROFILE_ID,
    IDENTITY_RUN_ROOT,
    MAX_ARTIFACT_BYTES,
    NO_PROVER_COMPUTE_PROFILE_ID,
    PROVER_COMPUTE_PROFILE_IDS,
    RISC0_COMPUTE_STAGE_IDS,
    TASK_SPECS,
    CommandSpec,
    TaskSpec,
)

CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID = (
    catalog.CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID
)
DEFAULT_ARTIFACT_BYTES = catalog.DEFAULT_ARTIFACT_BYTES
MAX_R0VM_EXECUTABLE_BYTES = catalog.MAX_R0VM_EXECUTABLE_BYTES

HANDOFF_SCHEMA = "zenodex/zrpf_remote_reproof_handoff/v4"
RETURN_SCHEMA = "zenodex/zrpf_remote_reproof_return/v4"
TASK_SCHEMA = "zenodex/zrpf_remote_reproof_task/v4"
EXECUTION_PACKET_SCHEMA = "zenodex/zrpf_remote_reproof_execution_packet/v4"
ARTIFACT_CONTRACT_SCHEMA = "zenodex/zrpf_remote_reproof_artifact_contract/v2"
ARTIFACT_RECORD_SCHEMA = "zenodex/zrpf_remote_reproof_artifact_record/v2"
PROVER_R0VM_EXPECTATION_SCHEMA = "zenodex/zrpf_remote_prover_r0vm_expectation/v1"
TASK_CAPTURE_SCHEMA = "zenodex/zrpf_remote_reproof_task_capture/v4"
SOURCE_BINDING_SCHEMA = "zenodex/zrpf_remote_reproof_source_binding/v2"
IDENTITY_BINDING_SCHEMA = "zenodex/zrpf_remote_reproof_identity_binding/v2"
SUCCINCT_PROFILE_ID = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
MAX_JSON_BYTES = 4 * 1024 * 1024
MAX_JSON_DEPTH = 48
MAX_JSON_NODES = 65_536
MAX_JSON_STRING_CHARS = 8_192
MAX_JSON_INTEGER_DIGITS = 20
MAX_TOTAL_ARTIFACT_BYTES = 1024 * 1024 * 1024
OFFICIAL_CPU_R0VM_BYTES = 108_998_816
OFFICIAL_CPU_R0VM_SHA256 = "36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b"
ZERO_SHA256 = "0" * 64

HANDOFF_DOMAIN = b"zenodex/zrpf_remote_reproof_handoff_id/v4\0"
TASK_DOMAIN = b"zenodex/zrpf_remote_reproof_task_id/v4\0"
ARTIFACT_CONTRACT_DOMAIN = b"zenodex/zrpf_remote_reproof_artifact_contract_id/v2\0"
ARTIFACT_RECORD_DOMAIN = b"zenodex/zrpf_remote_reproof_artifact_id/v2\0"
SOURCE_BINDING_DOMAIN = b"zenodex/zrpf_remote_reproof_source_binding_id/v2\0"
IDENTITY_BINDING_DOMAIN = b"zenodex/zrpf_remote_reproof_identity_binding_id/v2\0"
EXECUTION_PACKET_DOMAIN = b"zenodex/zrpf_remote_reproof_execution_packet_id/v4\0"
TASK_CAPTURE_DOMAIN = b"zenodex/zrpf_remote_reproof_task_capture_id/v4\0"
RETURN_DOMAIN = b"zenodex/zrpf_remote_reproof_return_id/v4\0"

AUTHORITY_FIELDS = (
    "data_availability_authority",
    "ledger_authority",
    "production_authority",
    "release_authority",
    "settlement_authority",
)

NON_CLAIMS = (
    "handoff_and_return_metadata_do_not_verify_any_proof",
    "task_capture_records_do_not_prove_historical_execution_provenance",
    "execution_packets_bind_inputs_but_do_not_prove_when_or_whether_a_command_ran",
    "execution_packets_do_not_authenticate_operator_authorization_or_freshness",
    "pre_packet_external_input_substitution_requires_initial_expected_digests_to_detect",
    "same_handoff_same_bytes_stale_replay_is_indistinguishable_without_an_external_anchor",
    "content_ids_do_not_protect_against_coherent_checker_catalog_or_policy_changes",
    "command_templates_do_not_implement_a_bounded_remote_worker_or_output_stager",
    "inherited_identity_planner_git_capture_is_post_hoc_bounded_and_not_lazy_fetch_hardened",
    "worker_reported_program_image_ids_require_separate_governed_recomputation",
    "prover_compute_profile_does_not_attest_accelerator_identity_or_performance",
    "prover_r0vm_expectation_does_not_establish_source_to_binary_provenance_or_gpu_use",
    "literal_ancestry_does_not_grant_release_authority",
    "no_data_availability_finality_ledger_settlement_release_or_production_authority",
)

RETURN_FIELDS = {
    "schema",
    "status",
    "bundle_id",
    "handoff_id",
    "source_binding_id",
    "proof_profile_id",
    "ancestry",
    "identity_binding",
    "execution_packets",
    "tasks",
    "artifacts",
    "authority",
    "non_claims",
}
IDENTITY_BINDING_FIELDS = {
    "schema",
    "identity_binding_id",
    "proof_profile_id",
    "programs",
    "program_image_ids_governed_recomputation_verified",
}
PROGRAM_IDENTITY_FIELDS = {"role", "artifact_id", "artifact_sha256", "image_id"}

TASK_ORDER = (
    "identity_rebuild",
    "ancestry_materialization",
    "worker_prover_build",
    "source_execution_profile",
    "source_spot_proof",
    "v2_adapter_receipt",
    "v6_leaf_receipt",
    "v6_l1_receipt",
    "v6_l2_receipt",
    "v6_settlement_receipt",
    "v7_execution_profile",
    "v7_receipt",
    "mutation_verification",
    "release_checks",
)

PROGRAM_ROLES = (
    "source_program",
    "v2_adapter_program",
    "v6_leaf_program",
    "v6_l1_program",
    "v6_l2_program",
    "v6_settlement_program",
    "v7_program",
)

IDENTITY_STAGE_ROLES = {
    "source_spot": "source_program",
    "v2_adapter": "v2_adapter_program",
    "v6_leaf": "v6_leaf_program",
    "v6_l1": "v6_l1_program",
    "v6_l2": "v6_l2_program",
    "v6_settlement": "v6_settlement_program",
}
IDENTITY_DOCUMENT_ROLES = {
    "identity_plan",
    "identity_observations",
    "identity_candidate_report",
}
VALIDATED_ARTIFACT_ROLES = IDENTITY_DOCUMENT_ROLES | {
    "post_pin_governance_result",
    *worker_build.BUILD_OUTPUT_ROLES,
    "worker_build_report",
}


class HandoffError(ValueError):
    """Stable fail-closed handoff rejection."""


def false_authority() -> dict[str, bool]:
    return {field: False for field in AUTHORITY_FIELDS}


def canonical_json_bytes(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("ascii")


def _canonical_values_equal(actual: object, expected: object) -> bool:
    """Compare JSON values without Python's bool/int equality aliasing."""

    try:
        return canonical_json_bytes(actual) == canonical_json_bytes(expected)
    except (TypeError, ValueError, OverflowError):
        return False


def _require_false_authority(value: object, label: str) -> None:
    authority = _object(value, label)
    _require_exact_fields(authority, set(AUTHORITY_FIELDS), label)
    if any(authority[field] is not False for field in AUTHORITY_FIELDS):
        raise HandoffError(f"{label} must contain exact Boolean false values")


def _digest(domain: bytes, value: object) -> str:
    return hashlib.sha256(domain + canonical_json_bytes(value)).hexdigest()


def derive_task_id(task: Mapping[str, object]) -> str:
    value = copy.deepcopy(dict(task))
    value["task_id"] = ZERO_SHA256
    return _digest(TASK_DOMAIN, value)


def derive_handoff_id(document: Mapping[str, object]) -> str:
    value = copy.deepcopy(dict(document))
    value["handoff_id"] = ZERO_SHA256
    return _digest(HANDOFF_DOMAIN, value)


def derive_bundle_id(document: Mapping[str, object]) -> str:
    value = copy.deepcopy(dict(document))
    value["bundle_id"] = ZERO_SHA256
    return _digest(RETURN_DOMAIN, value)


def derive_execution_packet_id(document: Mapping[str, object]) -> str:
    value = copy.deepcopy(dict(document))
    value["execution_packet_id"] = ZERO_SHA256
    return _digest(EXECUTION_PACKET_DOMAIN, value)


def _derive_source_binding_id(value: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(value))
    candidate["source_binding_id"] = ZERO_SHA256
    return _digest(SOURCE_BINDING_DOMAIN, candidate)


def _derive_artifact_contract_id(value: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(value))
    candidate["contract_id"] = ZERO_SHA256
    return _digest(ARTIFACT_CONTRACT_DOMAIN, candidate)


def _derive_artifact_id(value: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(value))
    candidate["artifact_id"] = ZERO_SHA256
    return _digest(ARTIFACT_RECORD_DOMAIN, candidate)


def _derive_identity_binding_id(value: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(value))
    candidate["identity_binding_id"] = ZERO_SHA256
    return _digest(IDENTITY_BINDING_DOMAIN, candidate)


def _reject_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise HandoffError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def _reject_float(value: str) -> NoReturn:
    raise HandoffError(f"floating-point JSON value is forbidden: {value}")


def _bounded_int(value: str) -> int:
    digits = value[1:] if value.startswith("-") else value
    if not digits or len(digits) > MAX_JSON_INTEGER_DIGITS:
        raise HandoffError("JSON integer exceeds its digit bound")
    return int(value, 10)


def _require_json_depth(raw: bytes) -> None:
    depth = 0
    quoted = False
    escaped = False
    for byte in raw:
        if quoted:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                quoted = False
            continue
        if byte == 0x22:
            quoted = True
        elif byte in (0x5B, 0x7B):
            depth += 1
            if depth > MAX_JSON_DEPTH:
                raise HandoffError("JSON nesting exceeds limit")
        elif byte in (0x5D, 0x7D):
            depth -= 1
            if depth < 0:
                raise HandoffError("JSON nesting is malformed")
    if quoted or depth != 0:
        raise HandoffError("JSON framing is incomplete")


def strict_json_loads(raw: bytes) -> object:
    if type(raw) is not bytes or not raw or len(raw) > MAX_JSON_BYTES:
        raise HandoffError("JSON input must be nonempty bounded bytes")
    _require_json_depth(raw)
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_pairs,
            parse_int=_bounded_int,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except HandoffError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise HandoffError("JSON input is invalid") from exc
    if canonical_json_bytes(value) != raw:
        raise HandoffError("JSON input is not canonical")
    _require_json_shape(value)
    return value


def _require_json_shape(value: object) -> None:
    stack = [value]
    nodes = 0
    while stack:
        current = stack.pop()
        nodes += 1
        if nodes > MAX_JSON_NODES:
            raise HandoffError("JSON node count exceeds limit")
        if isinstance(current, dict):
            stack.extend(current.values())
            stack.extend(current.keys())
        elif isinstance(current, list):
            stack.extend(current)
        elif isinstance(current, str) and len(current) > MAX_JSON_STRING_CHARS:
            raise HandoffError("JSON string exceeds limit")


def load_canonical_json(path: Path, label: str) -> object:
    return strict_json_loads(_stable_read(path, label, MAX_JSON_BYTES))


def build_handoff(
    repo_root: Path,
    c0_commit: str,
    worker_commit: str,
    *,
    prover_compute_profile_id: str = CPU_PROVER_COMPUTE_PROFILE_ID,
    prover_r0vm_sha256: str | None = None,
    prover_r0vm_bytes: int | None = None,
) -> dict[str, object]:
    root = repo_root.resolve(strict=True)
    c0 = _commit_id(c0_commit, "C0")
    worker = _commit_id(worker_commit, "worker commit")
    compute_profile = _prover_compute_profile_id(prover_compute_profile_id)
    prover_r0vm_expectation = _prover_r0vm_expectation(
        compute_profile,
        prover_r0vm_sha256,
        prover_r0vm_bytes,
    )
    rebuild = identity.build_plan(c0, IDENTITY_RUN_ROOT, repo_root=root)
    source = {
        "schema": SOURCE_BINDING_SCHEMA,
        "source_binding_id": ZERO_SHA256,
        "c0_commit": c0,
        "c0_tree": _commit_tree(root, c0),
        "worker_commit": worker,
        "worker_tree": _commit_tree(root, worker),
        "identity_rebuild_plan_sha256": identity.canonical_sha256(rebuild),
        "tracked_workspace_inventory_root_sha256": rebuild["tracked_workspace_source_coverage"][
            "inventory_root_sha256"
        ],
        "tracked_workspace_file_count": rebuild["tracked_workspace_source_coverage"][
            "tracked_file_count"
        ],
        "tracked_workspace_bytes": rebuild["tracked_workspace_source_coverage"]["tracked_bytes"],
        "source_guest_inventory_root_sha256": rebuild["source_guest_source_coverage"][
            "inventory_root_sha256"
        ],
        "source_guest_file_count": rebuild["source_guest_source_coverage"]["tracked_file_count"],
        "source_guest_bytes": rebuild["source_guest_source_coverage"]["tracked_bytes"],
        "toolchain_sha256": _digest(
            b"zenodex/zrpf_remote_reproof_toolchain/v2\0", rebuild["toolchain"]
        ),
        "build_image": rebuild["resource_policy"]["build_image"],
        "build_image_parent": rebuild["resource_policy"]["build_image_parent"],
        "complete_build_input_closure_verified": False,
    }
    source["source_binding_id"] = _derive_source_binding_id(source)
    contracts = _artifact_contracts()
    by_role: dict[str, Mapping[str, object]] = {str(row["role"]): row for row in contracts}
    tasks = [
        _task(index, spec, source["source_binding_id"], by_role, compute_profile)
        for index, spec in enumerate(TASK_SPECS)
    ]
    document: dict[str, object] = {
        "schema": HANDOFF_SCHEMA,
        "status": "authority_neutral_remote_reproof_handoff_planned",
        "handoff_id": ZERO_SHA256,
        "source": source,
        "proof_profile_id": SUCCINCT_PROFILE_ID,
        "prover_compute_profile_id": compute_profile,
        "prover_r0vm_expectation": prover_r0vm_expectation,
        "required_literal_ancestry": ["C0", "C1", "C2", "G"],
        "artifact_contracts": contracts,
        "tasks": tasks,
        "authority": false_authority(),
        "non_claims": list(NON_CLAIMS),
    }
    document["handoff_id"] = derive_handoff_id(document)
    return document


def _artifact_contracts() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for spec in ARTIFACT_SPECS:
        row: dict[str, object] = {
            "schema": ARTIFACT_CONTRACT_SCHEMA,
            "contract_id": ZERO_SHA256,
            "role": spec.role,
            "path": spec.path,
            "kind": spec.kind,
            "producer_stage": spec.producer_stage,
            "maximum_bytes": spec.maximum_bytes,
        }
        row["contract_id"] = _derive_artifact_contract_id(row)
        rows.append(row)
    return rows


def _task(
    ordinal: int,
    spec: TaskSpec,
    source_binding_id: object,
    contracts: Mapping[str, Mapping[str, object]],
    prover_compute_profile_id: str,
) -> dict[str, object]:
    execution_adapter_status = spec.execution_adapter_status
    if (
        spec.stage_id == "source_spot_proof"
        and prover_compute_profile_id == CPU_PROVER_COMPUTE_PROFILE_ID
    ):
        execution_adapter_status = "blocked_cpu_source_proof_disqualified"
    command_specs = (
        *spec.pre_commands,
        CommandSpec(
            spec.runner,
            spec.command,
            spec.stdin_artifact_role,
            spec.stdout_artifact_role,
        ),
    )
    for command in command_specs:
        if (
            command.stdin_artifact_role is not None
            and command.stdin_artifact_role not in spec.inputs
        ):
            raise HandoffError("command stdin must be one declared task input")
        if (
            command.stdout_artifact_role is not None
            and command.stdout_artifact_role not in spec.outputs
        ):
            raise HandoffError("command stdout must be one declared task output")
    commands = [_command_record(command) for command in command_specs]
    row: dict[str, object] = {
        "schema": TASK_SCHEMA,
        "task_id": ZERO_SHA256,
        "stage_id": spec.stage_id,
        "ordinal": ordinal,
        "depends_on": list(spec.depends_on),
        "source_binding_id": source_binding_id,
        "proof_profile_id": SUCCINCT_PROFILE_ID,
        "prover_compute_profile_id": (
            prover_compute_profile_id
            if spec.stage_id in RISC0_COMPUTE_STAGE_IDS
            else NO_PROVER_COMPUTE_PROFILE_ID
        ),
        "input_artifact_contract_ids": [contracts[role]["contract_id"] for role in spec.inputs],
        "output_artifact_contract_ids": [contracts[role]["contract_id"] for role in spec.outputs],
        "commands": commands,
        "success_predicates": list(spec.success_predicates),
        "resource_class": spec.resource_class,
        "command_status": spec.command_status,
        "execution_adapter_status": execution_adapter_status,
        "authority": false_authority(),
        "non_claims": list(NON_CLAIMS),
    }
    row["task_id"] = derive_task_id(row)
    return row


def _command_record(spec: CommandSpec) -> dict[str, object]:
    return {
        "runner": spec.runner,
        "argv": list(spec.argv),
        "stdin_artifact_role": spec.stdin_artifact_role,
        "stdout_artifact_role": spec.stdout_artifact_role,
    }


def validate_handoff(document: Mapping[str, object], repo_root: Path) -> None:
    if document.get("schema") != HANDOFF_SCHEMA:
        raise HandoffError("handoff schema mismatch")
    if document.get("handoff_id") != derive_handoff_id(document):
        raise HandoffError("handoff ID mismatch")
    if document.get("proof_profile_id") != SUCCINCT_PROFILE_ID:
        raise HandoffError("proof profile mismatch")
    _require_false_authority(document.get("authority"), "handoff authority")
    if not _canonical_values_equal(document.get("non_claims"), list(NON_CLAIMS)):
        raise HandoffError("handoff authority boundary mismatch")
    source = _object(document.get("source"), "source")
    if source.get("schema") != SOURCE_BINDING_SCHEMA or source.get(
        "source_binding_id"
    ) != _derive_source_binding_id(source):
        raise HandoffError("source binding mismatch")
    root = repo_root.resolve(strict=True)
    if _commit_tree(root, _commit_id(source.get("c0_commit"), "C0")) != source.get("c0_tree"):
        raise HandoffError("C0 source tree mismatch")
    if _commit_tree(root, _commit_id(source.get("worker_commit"), "worker commit")) != source.get(
        "worker_tree"
    ):
        raise HandoffError("worker source tree mismatch")
    compute_profile = _prover_compute_profile_id(document.get("prover_compute_profile_id"))
    prover_r0vm_expectation = _validated_prover_r0vm_expectation(
        document.get("prover_r0vm_expectation")
    )
    expected = build_handoff(
        root,
        str(source["c0_commit"]),
        str(source["worker_commit"]),
        prover_compute_profile_id=compute_profile,
        prover_r0vm_sha256=_hex(
            prover_r0vm_expectation["sha256"], 64, "prover r0vm expectation SHA-256"
        ),
        prover_r0vm_bytes=_positive_int(
            prover_r0vm_expectation["size_bytes"], "prover r0vm expectation bytes"
        ),
    )
    if not _canonical_values_equal(document, expected):
        tasks = document.get("tasks")
        if not isinstance(tasks, list) or [
            row.get("stage_id") for row in tasks if isinstance(row, dict)
        ] != list(TASK_ORDER):
            raise HandoffError("task order mismatch")
        raise HandoffError("handoff differs from the governed source-derived plan")


def task_states(
    document: Mapping[str, object], completed_artifacts: Sequence[Mapping[str, object]]
) -> list[dict[str, Any]]:
    roles = [row.get("role") for row in completed_artifacts]
    if any(type(role) is not str for role in roles) or len(roles) != len(set(roles)):
        raise HandoffError("completed artifact roles must be unique strings")
    completed_roles = set(roles)
    artifact_contracts = _object_list(document.get("artifact_contracts"), "artifact contracts")
    task_rows = _object_list(document.get("tasks"), "tasks")
    contracts = {str(row["contract_id"]): row for row in artifact_contracts}
    completed_stages: set[str] = set()
    states: list[dict[str, Any]] = []
    for task in task_rows:
        stage_id = _nonempty_string(task.get("stage_id"), "task stage ID")
        input_contract_ids = _string_list(
            task.get("input_artifact_contract_ids"), "task input contract IDs"
        )
        output_contract_ids = _string_list(
            task.get("output_artifact_contract_ids"), "task output contract IDs"
        )
        input_roles = [str(contracts[item]["role"]) for item in input_contract_ids]
        output_roles = [str(contracts[item]["role"]) for item in output_contract_ids]
        missing_inputs = sorted(set(input_roles) - completed_roles)
        missing_dependencies = sorted(
            set(_string_list(task.get("depends_on"), "task dependencies")) - completed_stages
        )
        outputs_complete = set(output_roles).issubset(completed_roles)
        if outputs_complete and not missing_dependencies:
            status = "artifacts_observed"
            completed_stages.add(stage_id)
        elif (
            not missing_inputs
            and not missing_dependencies
            and task["execution_adapter_status"] == "implemented"
        ):
            status = "ready"
        else:
            status = "blocked"
        states.append(
            {
                "stage_id": stage_id,
                "status": status,
                "missing_dependency_stages": missing_dependencies,
                "missing_input_artifacts": missing_inputs,
                "command_template_available": task["command_status"] == "template_available",
                "execution_adapter_available": task["execution_adapter_status"] == "implemented",
            }
        )
    return states


def build_execution_packet(
    handoff: Mapping[str, object],
    stage_id: str,
    artifact_root: Path,
    repo_root: Path,
    *,
    c0_commit: str,
    c1_commit: str,
    c2_commit: str,
    governance_commit: str,
) -> dict[str, object]:
    """Bind one task to its exact current input artifact bytes."""

    validate_handoff(handoff, repo_root)
    ancestry = validate_literal_ancestry(
        repo_root, c0_commit, c1_commit, c2_commit, governance_commit
    )
    source = _object(handoff.get("source"), "source")
    if ancestry.get("c0_commit") != source.get("c0_commit"):
        raise HandoffError("execution packet C0 differs from handoff C0")
    _require_ancestry_matches_source(source, ancestry)
    tasks = _object_list(handoff.get("tasks"), "tasks")
    matching = [task for task in tasks if task.get("stage_id") == stage_id]
    if len(matching) != 1:
        raise HandoffError("execution packet stage is not one governed task")
    contracts = _object_list(handoff.get("artifact_contracts"), "artifact contracts")
    contract_by_id = {str(row["contract_id"]): row for row in contracts}
    root = artifact_root.resolve(strict=True)
    inputs = [
        _artifact_record(contract_by_id[contract_id], root)
        for contract_id in _string_list(
            matching[0].get("input_artifact_contract_ids"), "task input contract IDs"
        )
    ]
    _require_aggregate_artifact_bound(inputs)
    _require_task_prover_r0vm_expectation(handoff, matching[0], inputs)
    row = _execution_packet(matching[0], source, ancestry, inputs)
    row["handoff_id"] = handoff["handoff_id"]
    row["execution_packet_id"] = derive_execution_packet_id(row)
    return row


def _execution_packet(
    task: Mapping[str, object],
    source: Mapping[str, object],
    ancestry: Mapping[str, object],
    inputs: Sequence[Mapping[str, object]],
) -> dict[str, object]:
    row: dict[str, object] = {
        "schema": EXECUTION_PACKET_SCHEMA,
        "status": "exact_inputs_bound_without_execution_provenance",
        "execution_packet_id": ZERO_SHA256,
        "handoff_id": ZERO_SHA256,
        "source_binding_id": source["source_binding_id"],
        "task_id": task["task_id"],
        "stage_id": task["stage_id"],
        "ordinal": task["ordinal"],
        "worker_commit": ancestry["governance_commit"],
        "worker_tree": ancestry["governance_tree"],
        "proof_profile_id": SUCCINCT_PROFILE_ID,
        "input_artifact_ids": [item["artifact_id"] for item in inputs],
        "authority": false_authority(),
        "non_claims": list(NON_CLAIMS),
    }
    # The caller replaces the handoff sentinel before deriving the packet ID.
    return row


def _execution_packets_from_records(
    handoff: Mapping[str, object],
    ancestry: Mapping[str, object],
    records: Mapping[str, Mapping[str, object]],
) -> list[dict[str, object]]:
    source = _object(handoff.get("source"), "source")
    contracts = _object_list(handoff.get("artifact_contracts"), "artifact contracts")
    contract_by_id = {str(row["contract_id"]): row for row in contracts}
    rows: list[dict[str, object]] = []
    for task in _object_list(handoff.get("tasks"), "tasks"):
        inputs = [
            records[str(contract_by_id[contract_id]["role"])]
            for contract_id in _string_list(
                task.get("input_artifact_contract_ids"), "task input contract IDs"
            )
        ]
        _require_task_prover_r0vm_expectation(handoff, task, inputs)
        row = _execution_packet(task, source, ancestry, inputs)
        row["handoff_id"] = handoff["handoff_id"]
        row["execution_packet_id"] = derive_execution_packet_id(row)
        rows.append(row)
    return rows


def _execution_packet_filename(ordinal: int, stage_id: str) -> str:
    return f"{ordinal:02d}-{stage_id}.json"


def _load_execution_packets(
    directory: Path,
    expected: Sequence[Mapping[str, object]],
) -> list[dict[str, object]]:
    root = directory.resolve(strict=True)
    try:
        facts = directory.lstat()
        names = sorted(item.name for item in directory.iterdir())
    except OSError as exc:
        raise HandoffError("execution packet directory is unavailable") from exc
    if not stat.S_ISDIR(facts.st_mode) or root != directory:
        raise HandoffError("execution packet directory must be one real canonical directory")
    expected_names = [
        _execution_packet_filename(
            _positive_ordinal(row.get("ordinal"), "execution packet ordinal"),
            _nonempty_string(row.get("stage_id"), "execution packet stage"),
        )
        for row in expected
    ]
    if names != sorted(expected_names):
        raise HandoffError("execution packet inventory mismatch")
    observed = [
        _object(
            strict_json_loads(
                _stable_read_beneath(root, name, f"execution packet {name}", MAX_JSON_BYTES)
            ),
            f"execution packet {name}",
        )
        for name in expected_names
    ]
    if not _canonical_values_equal(observed, list(expected)):
        raise HandoffError("execution packet differs from exact current input artifacts")
    return observed


def capture_return_bundle(
    handoff: Mapping[str, object],
    artifact_root: Path,
    repo_root: Path,
    *,
    execution_packet_directory: Path,
    c0_commit: str,
    c1_commit: str,
    c2_commit: str,
    governance_commit: str,
    program_image_ids: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    validate_handoff(handoff, repo_root)
    root = artifact_root.resolve(strict=True)
    ancestry = validate_literal_ancestry(
        repo_root, c0_commit, c1_commit, c2_commit, governance_commit
    )
    source = _object(handoff.get("source"), "source")
    if ancestry["c0_commit"] != source.get("c0_commit"):
        raise HandoffError("return ancestry C0 differs from handoff C0")
    _require_ancestry_matches_source(source, ancestry)
    contracts = _object_list(handoff.get("artifact_contracts"), "artifact contracts")
    records, artifact_bytes = _artifact_records(contracts, root)
    _require_aggregate_artifact_bound(records)
    by_role: dict[str, Mapping[str, object]] = {str(row["role"]): row for row in records}
    _require_source_artifact_bindings(source, by_role)
    identity_images = _validate_identity_artifacts(handoff, repo_root, by_role, artifact_bytes)
    images = dict(program_image_ids or {})
    if set(images) != set(PROGRAM_ROLES):
        raise HandoffError("program image ID inventory mismatch")
    _validate_worker_build_artifacts(
        handoff,
        artifact_bytes,
        ancestry,
        images,
    )
    programs = []
    for role in PROGRAM_ROLES:
        image_id = _hex(images[role], 64, f"{role} image ID")
        if image_id == ZERO_SHA256:
            raise HandoffError("program image ID cannot use the zero sentinel")
        if role in identity_images and image_id != identity_images[role]:
            raise HandoffError("program image ID differs from validated identity rebuild")
        programs.append(
            {
                "role": role,
                "artifact_id": by_role[role]["artifact_id"],
                "artifact_sha256": by_role[role]["sha256"],
                "image_id": image_id,
            }
        )
    identity_binding: dict[str, object] = {
        "schema": IDENTITY_BINDING_SCHEMA,
        "identity_binding_id": ZERO_SHA256,
        "proof_profile_id": SUCCINCT_PROFILE_ID,
        "programs": programs,
        "program_image_ids_governed_recomputation_verified": False,
    }
    identity_binding["identity_binding_id"] = _derive_identity_binding_id(identity_binding)
    expected_packets = _execution_packets_from_records(handoff, ancestry, by_role)
    execution_packets = _load_execution_packets(execution_packet_directory, expected_packets)
    captures = _task_captures(handoff, execution_packets, identity_binding, by_role)
    document: dict[str, object] = {
        "schema": RETURN_SCHEMA,
        "status": "authority_neutral_remote_reproof_return_captured",
        "bundle_id": ZERO_SHA256,
        "handoff_id": handoff["handoff_id"],
        "source_binding_id": source["source_binding_id"],
        "proof_profile_id": SUCCINCT_PROFILE_ID,
        "ancestry": ancestry,
        "identity_binding": identity_binding,
        "execution_packets": execution_packets,
        "tasks": captures,
        "artifacts": records,
        "authority": false_authority(),
        "non_claims": list(NON_CLAIMS),
    }
    document["bundle_id"] = derive_bundle_id(document)
    return document


def _artifact_record(contract: Mapping[str, object], root: Path) -> dict[str, object]:
    path = _safe_relative_path(contract.get("path"), "artifact path")
    maximum_bytes = _positive_int(contract.get("maximum_bytes"), "maximum bytes")
    raw = _stable_read_beneath(root, path, str(contract["role"]), maximum_bytes)
    return _artifact_record_from_bytes(contract, path, raw)


def _artifact_records(
    contracts: Sequence[Mapping[str, object]], root: Path
) -> tuple[list[dict[str, object]], dict[str, bytes]]:
    records: list[dict[str, object]] = []
    raw_by_role: dict[str, bytes] = {}
    total_bytes = 0
    for contract in contracts:
        path = _safe_relative_path(contract.get("path"), "artifact path")
        role = _nonempty_string(contract.get("role"), "artifact role")
        raw = _stable_read_beneath(
            root,
            path,
            role,
            _positive_int(contract.get("maximum_bytes"), "maximum bytes"),
        )
        total_bytes += len(raw)
        if total_bytes > MAX_TOTAL_ARTIFACT_BYTES:
            raise HandoffError("aggregate artifact bytes exceed the governed bound")
        records.append(_artifact_record_from_bytes(contract, path, raw))
        if role in VALIDATED_ARTIFACT_ROLES:
            raw_by_role[role] = raw
    return records, raw_by_role


def _artifact_record_from_bytes(
    contract: Mapping[str, object], path: str, raw: bytes
) -> dict[str, object]:
    row: dict[str, object] = {
        "schema": ARTIFACT_RECORD_SCHEMA,
        "artifact_id": ZERO_SHA256,
        "contract_id": contract["contract_id"],
        "role": contract["role"],
        "path": path,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "size_bytes": len(raw),
        "producer_stage": contract["producer_stage"],
    }
    row["artifact_id"] = _derive_artifact_id(row)
    return row


def _task_captures(
    handoff: Mapping[str, object],
    execution_packets: Sequence[Mapping[str, object]],
    identity_binding: Mapping[str, object],
    records: Mapping[str, Mapping[str, object]],
) -> list[dict[str, object]]:
    contracts = _object_list(handoff.get("artifact_contracts"), "artifact contracts")
    tasks = _object_list(handoff.get("tasks"), "tasks")
    contract_by_id = {str(row["contract_id"]): row for row in contracts}
    rows: list[dict[str, object]] = []
    packet_by_stage = {str(row["stage_id"]): row for row in execution_packets}
    if len(packet_by_stage) != len(tasks):
        raise HandoffError("execution packet stage inventory mismatch")
    for task in tasks:
        output_records = [
            records[str(contract_by_id[item]["role"])]
            for item in _string_list(
                task.get("output_artifact_contract_ids"), "task output contract IDs"
            )
        ]
        packet = packet_by_stage[str(task["stage_id"])]
        row: dict[str, object] = {
            "schema": TASK_CAPTURE_SCHEMA,
            "task_capture_id": ZERO_SHA256,
            "stage_id": task["stage_id"],
            "task_id": task["task_id"],
            "execution_packet_id": packet["execution_packet_id"],
            "identity_binding_id": identity_binding["identity_binding_id"],
            "output_artifact_ids": [record["artifact_id"] for record in output_records],
            "status": "artifacts_captured_without_execution_provenance",
        }
        candidate = copy.deepcopy(row)
        candidate["task_capture_id"] = ZERO_SHA256
        row["task_capture_id"] = _digest(TASK_CAPTURE_DOMAIN, candidate)
        rows.append(row)
    return rows


def validate_return_bundle(
    handoff: Mapping[str, object],
    bundle: Mapping[str, object],
    artifact_root: Path,
    repo_root: Path,
) -> Mapping[str, object]:
    validate_handoff(handoff, repo_root)
    _require_exact_fields(bundle, RETURN_FIELDS, "return bundle")
    if bundle.get("schema") != RETURN_SCHEMA:
        raise HandoffError("return schema mismatch")
    if bundle.get("status") != "authority_neutral_remote_reproof_return_captured":
        raise HandoffError("return status mismatch")
    if bundle.get("proof_profile_id") != SUCCINCT_PROFILE_ID:
        raise HandoffError("return proof profile mismatch")
    if bundle.get("handoff_id") != handoff.get("handoff_id"):
        raise HandoffError("return handoff ID mismatch")
    if bundle.get("source_binding_id") != _object(handoff.get("source"), "source").get(
        "source_binding_id"
    ):
        raise HandoffError("return source binding mismatch")
    if bundle.get("bundle_id") != derive_bundle_id(bundle):
        raise HandoffError("return bundle ID mismatch")
    _require_false_authority(bundle.get("authority"), "return authority")
    if not _canonical_values_equal(bundle.get("non_claims"), list(NON_CLAIMS)):
        raise HandoffError("return authority boundary mismatch")
    ancestry = _object(bundle.get("ancestry"), "ancestry")
    expected_ancestry = validate_literal_ancestry(
        repo_root,
        str(ancestry.get("c0_commit")),
        str(ancestry.get("c1_commit")),
        str(ancestry.get("c2_commit")),
        str(ancestry.get("governance_commit")),
    )
    if not _canonical_values_equal(ancestry, expected_ancestry) or ancestry.get(
        "c0_commit"
    ) != _object(handoff.get("source"), "source").get("c0_commit"):
        raise HandoffError("return literal ancestry mismatch")
    source = _object(handoff.get("source"), "source")
    _require_ancestry_matches_source(source, ancestry)
    contracts = _object_list(handoff.get("artifact_contracts"), "artifact contracts")
    records = bundle.get("artifacts")
    if not isinstance(records, list) or [
        row.get("contract_id") for row in records if isinstance(row, dict)
    ] != [row["contract_id"] for row in contracts]:
        raise HandoffError("return artifact inventory mismatch")
    root = artifact_root.resolve(strict=True)
    observed, artifact_bytes = _artifact_records(contracts, root)
    _require_aggregate_artifact_bound(observed)
    if not _canonical_values_equal(records, observed):
        for expected, actual in zip(records, observed, strict=True):
            if isinstance(expected, dict) and expected.get("sha256") != actual.get("sha256"):
                raise HandoffError("artifact SHA-256 mismatch")
        raise HandoffError("return artifact record mismatch")
    identity_binding = _object(bundle.get("identity_binding"), "identity binding")
    _require_exact_fields(identity_binding, IDENTITY_BINDING_FIELDS, "identity binding")
    if identity_binding.get("schema") != IDENTITY_BINDING_SCHEMA:
        raise HandoffError("identity binding schema mismatch")
    if identity_binding.get("identity_binding_id") != _derive_identity_binding_id(identity_binding):
        raise HandoffError("identity binding ID mismatch")
    if (
        identity_binding.get("proof_profile_id") != SUCCINCT_PROFILE_ID
        or identity_binding.get("program_image_ids_governed_recomputation_verified") is not False
    ):
        raise HandoffError("identity binding policy mismatch")
    by_role: dict[str, Mapping[str, object]] = {str(row["role"]): row for row in observed}
    _require_source_artifact_bindings(source, by_role)
    identity_images = _validate_identity_artifacts(handoff, repo_root, by_role, artifact_bytes)
    programs = _object_list(identity_binding.get("programs"), "program identities")
    if [row.get("role") for row in programs] != list(PROGRAM_ROLES):
        raise HandoffError("program identity inventory mismatch")
    for row in programs:
        _require_exact_fields(row, PROGRAM_IDENTITY_FIELDS, "program identity")
        role = _nonempty_string(row.get("role"), "program identity role")
        if (
            row.get("artifact_id") != by_role[role]["artifact_id"]
            or row.get("artifact_sha256") != by_role[role]["sha256"]
        ):
            raise HandoffError("program identity artifact binding mismatch")
        image_id = _hex(row.get("image_id"), 64, "program image ID")
        if image_id == ZERO_SHA256:
            raise HandoffError("program image ID cannot use the zero sentinel")
        if role in identity_images and image_id != identity_images[role]:
            raise HandoffError("program image ID differs from validated identity rebuild")
    program_images = {str(row["role"]): str(row["image_id"]) for row in programs}
    _validate_worker_build_artifacts(
        handoff,
        artifact_bytes,
        ancestry,
        program_images,
    )
    expected_packets = _execution_packets_from_records(handoff, ancestry, by_role)
    if not _canonical_values_equal(bundle.get("execution_packets"), expected_packets):
        raise HandoffError("return execution packet inventory mismatch")
    captures = _task_captures(handoff, expected_packets, identity_binding, by_role)
    if not _canonical_values_equal(bundle.get("tasks"), captures):
        raise HandoffError("return task capture inventory mismatch")
    return bundle


def _require_ancestry_matches_source(
    source: Mapping[str, object], ancestry: Mapping[str, object]
) -> None:
    if ancestry.get("governance_commit") != source.get("worker_commit") or ancestry.get(
        "governance_tree"
    ) != source.get("worker_tree"):
        raise HandoffError("return governance worker differs from handoff worker")


def _require_source_artifact_bindings(
    source: Mapping[str, object], records: Mapping[str, Mapping[str, object]]
) -> None:
    identity_plan = records.get("identity_plan")
    if identity_plan is None or identity_plan.get("sha256") != source.get(
        "identity_rebuild_plan_sha256"
    ):
        raise HandoffError("identity rebuild plan artifact differs from source binding")


def _validate_identity_artifacts(
    handoff: Mapping[str, object],
    repo_root: Path,
    records: Mapping[str, Mapping[str, object]],
    artifact_bytes: Mapping[str, bytes],
) -> dict[str, str]:
    source = _object(handoff.get("source"), "source")
    try:
        plan = _load_identity_json_bytes(artifact_bytes["identity_plan"], "identity rebuild plan")
        expected_plan = identity.build_plan(
            str(source["c0_commit"]), IDENTITY_RUN_ROOT, repo_root=repo_root
        )
        if not _canonical_values_equal(plan, expected_plan):
            raise HandoffError("identity rebuild plan differs from exact C0 plan")
        observations = _load_identity_json_bytes(
            artifact_bytes["identity_observations"], "identity rebuild observations"
        )
        report = _load_identity_json_bytes(
            artifact_bytes["identity_candidate_report"],
            "identity rebuild candidate report",
        )
        recomposed = identity.check_observations(plan, observations, repo_root=repo_root)
    except identity.RebuildPlanError as exc:
        raise HandoffError("identity rebuild artifacts failed governed validation") from exc
    if not _canonical_values_equal(report, recomposed):
        raise HandoffError("identity candidate report differs from recomposition")

    programs = _object_list(report.get("programs"), "identity programs")
    images: dict[str, str] = {}
    if [row.get("stage_id") for row in programs] != list(IDENTITY_STAGE_ROLES):
        raise HandoffError("identity program stage inventory mismatch")
    for program in programs:
        stage_id = _nonempty_string(program.get("stage_id"), "identity program stage")
        role = IDENTITY_STAGE_ROLES[stage_id]
        record = records[role]
        program_sha256 = _hex(
            program.get("program_binary_sha256"), 64, "identity program binary SHA-256"
        )
        program_bytes = _positive_int(
            program.get("program_binary_bytes"), "identity program binary bytes"
        )
        record_bytes = _positive_int(record.get("size_bytes"), "identity program artifact bytes")
        if program_sha256 != record.get("sha256") or program_bytes != record_bytes:
            raise HandoffError("identity program artifact differs from candidate report")
        images[role] = _hex(program.get("image_id"), 64, "identity program image ID")
    source_cli = _object(report.get("source_spot_cli"), "source Spot CLI")
    source_cli_record = records["source_cli"]
    source_cli_sha256 = _hex(source_cli.get("binary_sha256"), 64, "source CLI binary SHA-256")
    source_cli_bytes = _positive_int(source_cli.get("binary_bytes"), "source CLI binary bytes")
    source_cli_record_bytes = _positive_int(
        source_cli_record.get("size_bytes"), "source CLI artifact bytes"
    )
    if (
        source_cli_sha256 != source_cli_record.get("sha256")
        or source_cli_bytes != source_cli_record_bytes
    ):
        raise HandoffError("source CLI artifact differs from candidate report")
    return images


def _validate_worker_build_artifacts(
    handoff: Mapping[str, object],
    artifact_bytes: Mapping[str, bytes],
    ancestry: Mapping[str, object],
    program_images: Mapping[str, str],
) -> None:
    source = _object(handoff.get("source"), "source")
    try:
        expected_source_commit = str(source["worker_commit"])
        governed = worker_build._validate_governance_result(
            artifact_bytes["post_pin_governance_result"],
            expected_source_commit,
        )
        for field in ("c0_commit", "c1_commit", "c2_commit", "governance_commit"):
            if governed[field] != ancestry.get(field):
                raise HandoffError("worker governance ancestry binding mismatch")
        if governed["v6_settlement_image_id"] != program_images.get("v6_settlement_program"):
            raise HandoffError("worker governance V6 image binding mismatch")
        observed = {role: artifact_bytes[role] for role in worker_build.BUILD_OUTPUT_ROLES}
        worker_build.validate_worker_build_report(
            artifact_bytes["worker_build_report"],
            observed,
            artifact_bytes["post_pin_governance_result"],
            expected_source_commit=expected_source_commit,
            expected_v7_image_id=program_images["v7_program"],
        )
    except (KeyError, worker_build.WorkerBuildError) as exc:
        raise HandoffError("worker build artifacts failed governed validation") from exc


def _load_identity_json_bytes(raw: bytes, label: str) -> dict[str, Any]:
    try:
        document = json.loads(
            raw.decode("utf-8", errors="strict"),
            object_pairs_hook=identity._unique_object,
            parse_float=identity._reject_float,
            parse_int=identity._bounded_int,
        )
        identity._validate_json_shape(document)
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        identity.RebuildPlanError,
    ) as exc:
        raise HandoffError(f"{label} JSON rejected") from exc
    if type(document) is not dict or raw != identity.canonical_bytes(document):
        raise HandoffError(f"{label} must use canonical governed JSON bytes")
    return document


def validate_literal_ancestry(
    repo_root: Path,
    c0_commit: str,
    c1_commit: str,
    c2_commit: str,
    governance_commit: str,
) -> dict[str, object]:
    root = repo_root.resolve(strict=True)
    _require_unmodified_object_graph(root)
    c0 = _commit_id(c0_commit, "C0")
    c1 = _commit_id(c1_commit, "C1")
    c2 = _commit_id(c2_commit, "C2")
    governance = _commit_id(governance_commit, "G")
    _require_literal_parent(root, c1, c0, "C1")
    _require_literal_parent(root, c2, c1, "C2")
    _require_literal_parent(root, governance, c2, "G")
    return {
        "c0_commit": c0,
        "c0_tree": _commit_tree(root, c0),
        "c1_commit": c1,
        "c1_tree": _commit_tree(root, c1),
        "c2_commit": c2,
        "c2_tree": _commit_tree(root, c2),
        "governance_commit": governance,
        "governance_tree": _commit_tree(root, governance),
        "literal_direct_parent_chain_verified": True,
    }


def _require_literal_parent(root: Path, child: str, parent: str, label: str) -> None:
    raw = _git(root, ["cat-file", "commit", child], 64 * 1024)
    headers, separator, _message = raw.partition(b"\n\n")
    if not separator:
        raise HandoffError(f"{label} commit object is malformed")
    parents = [
        line[7:].decode("ascii") for line in headers.splitlines() if line.startswith(b"parent ")
    ]
    if len(parents) != 1:
        raise HandoffError(f"{label} must have exactly one literal parent")
    if parents[0] != parent:
        raise HandoffError(f"{label} literal parent mismatch")


def _require_unmodified_object_graph(root: Path) -> None:
    common_dir = _git(root, ["rev-parse", "--git-common-dir"], 4 * 1024).decode("utf-8").strip()
    common_path = Path(common_dir)
    if not common_path.is_absolute():
        common_path = root / common_path
    grafts = common_path / "info/grafts"
    if grafts.exists() and grafts.stat().st_size:
        raise HandoffError("Git grafts are forbidden")
    if _git(root, ["for-each-ref", "--format=%(refname)", "refs/replace"], 64 * 1024):
        raise HandoffError("Git replacement refs are forbidden")


def _commit_tree(root: Path, commit: str) -> str:
    value = _git(root, ["rev-parse", f"{commit}^{{tree}}"], 128).decode("ascii").strip()
    return _hex(value, 40, "commit tree")


def _git(root: Path, arguments: Sequence[str], maximum_stdout: int) -> bytes:
    environment = {
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_TERMINAL_PROMPT": "0",
        "HOME": "/nonexistent",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    try:
        process = subprocess.Popen(
            [
                "/usr/bin/git",
                "--no-lazy-fetch",
                "-c",
                "protocol.allow=never",
                "-C",
                str(root),
                *arguments,
            ],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            start_new_session=True,
        )
    except OSError as exc:
        raise HandoffError("bounded Git command failed") from exc
    try:
        stdout, stderr = _capture_bounded_process(
            process,
            maximum_stdout=maximum_stdout,
            maximum_stderr=64 * 1024,
            timeout_seconds=30,
        )
    except HandoffError:
        _terminate_process_group(process)
        raise
    except (OSError, TimeoutError, subprocess.TimeoutExpired) as exc:
        _terminate_process_group(process)
        raise HandoffError("bounded Git command failed") from exc
    _terminate_process_group(process)
    if process.returncode != 0 or stderr:
        raise HandoffError("bounded Git command rejected")
    return stdout


def _capture_bounded_process(
    process: subprocess.Popen[bytes],
    *,
    maximum_stdout: int,
    maximum_stderr: int,
    timeout_seconds: int,
) -> tuple[bytes, bytes]:
    if process.stdout is None or process.stderr is None:
        raise HandoffError("bounded process pipes are unavailable")
    streams = {
        process.stdout.fileno(): ("stdout", maximum_stdout),
        process.stderr.fileno(): ("stderr", maximum_stderr),
    }
    buffers = {"stdout": bytearray(), "stderr": bytearray()}
    selector = selectors.DefaultSelector()
    try:
        for descriptor in streams:
            os.set_blocking(descriptor, False)
            selector.register(descriptor, selectors.EVENT_READ)
        deadline = time.monotonic() + timeout_seconds
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("bounded process timed out")
            events = selector.select(min(remaining, 1.0))
            if not events:
                continue
            for key, _mask in events:
                descriptor = int(key.fd)
                label, maximum = streams[descriptor]
                try:
                    chunk = os.read(descriptor, 64 * 1024)
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(descriptor)
                    continue
                if len(buffers[label]) + len(chunk) > maximum:
                    raise HandoffError(f"bounded Git {label} exceeds its cap")
                buffers[label].extend(chunk)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("bounded process timed out")
        process.wait(timeout=remaining)
    finally:
        selector.close()
        process.stdout.close()
        process.stderr.close()
    return bytes(buffers["stdout"]), bytes(buffers["stderr"])


def _terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def _stable_read(path: Path, label: str, maximum: int) -> bytes:
    try:
        before = path.lstat()
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_nlink != 1
            or not 0 < before.st_size <= maximum
        ):
            raise HandoffError(f"{label} must be one bounded regular file")
        with path.open("rb") as handle:
            opened = os.fstat(handle.fileno())
            raw = handle.read(maximum + 1)
            after = os.fstat(handle.fileno())
    except OSError as exc:
        raise HandoffError(f"{label} could not be read") from exc

    def identity_tuple(value: os.stat_result) -> tuple[int, int, int, int, int, int]:
        return (
            value.st_dev,
            value.st_ino,
            value.st_mode,
            value.st_size,
            value.st_mtime_ns,
            value.st_ctime_ns,
        )

    if identity_tuple(before) != identity_tuple(opened) or identity_tuple(opened) != identity_tuple(
        after
    ):
        raise HandoffError(f"{label} changed during read")
    if len(raw) != before.st_size:
        raise HandoffError(f"{label} read length mismatch")
    return raw


def _stable_read_beneath(root: Path, relative: str, label: str, maximum: int) -> bytes:
    """Read one file through a no-symlink descriptor walk beneath root."""

    parts = PurePosixPath(_safe_relative_path(relative, "artifact path")).parts
    directory_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    file_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    descriptors: list[int] = []
    try:
        root_before = root.lstat()
        descriptor = os.open(root, directory_flags)
        descriptors.append(descriptor)
        root_opened = os.fstat(descriptor)
        if not stat.S_ISDIR(root_before.st_mode) or _file_identity(root_before) != _file_identity(
            root_opened
        ):
            raise HandoffError("artifact root changed before descriptor capture")
        for part in parts[:-1]:
            descriptor = os.open(part, directory_flags, dir_fd=descriptor)
            descriptors.append(descriptor)
        file_descriptor = os.open(parts[-1], file_flags, dir_fd=descriptor)
        descriptors.append(file_descriptor)
        before = os.fstat(file_descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_nlink != 1
            or not 0 < before.st_size <= maximum
        ):
            raise HandoffError(f"{label} must be one bounded regular file")
        chunks: list[bytes] = []
        remaining = maximum + 1
        while remaining:
            chunk = os.read(file_descriptor, min(1024 * 1024, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
        after = os.fstat(file_descriptor)
    except HandoffError:
        raise
    except OSError as exc:
        if exc.errno in {getattr(os, "ELOOP", 40), getattr(os, "ENOTDIR", 20)}:
            raise HandoffError(
                f"{label} path contains a symlink or non-directory component"
            ) from exc
        raise HandoffError(f"{label} could not be read beneath artifact root") from exc
    finally:
        for descriptor in reversed(descriptors):
            os.close(descriptor)
    if _file_identity(before) != _file_identity(after):
        raise HandoffError(f"{label} changed during read")
    if len(raw) != before.st_size:
        raise HandoffError(f"{label} read length mismatch")
    return raw


def _file_identity(value: os.stat_result) -> tuple[int, int, int, int, int, int]:
    return (
        value.st_dev,
        value.st_ino,
        value.st_mode,
        value.st_size,
        value.st_mtime_ns,
        value.st_ctime_ns,
    )


def _require_aggregate_artifact_bound(records: Sequence[Mapping[str, object]]) -> None:
    total = 0
    for record in records:
        total += _positive_int(record.get("size_bytes"), "artifact size")
        if total > MAX_TOTAL_ARTIFACT_BYTES:
            raise HandoffError("aggregate artifact bytes exceed the governed bound")


def _safe_relative_path(value: object, label: str) -> str:
    if type(value) is not str or not value or len(value) > 512 or "\\" in value or "\0" in value:
        raise HandoffError(f"{label} is invalid")
    pure = PurePosixPath(value)
    if (
        pure.is_absolute()
        or pure.as_posix() != value
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise HandoffError(f"{label} is not a canonical relative path")
    return value


def _object(value: object, label: str) -> dict[str, object]:
    if type(value) is not dict:
        raise HandoffError(f"{label} must be an object")
    return value


def _require_exact_fields(value: Mapping[str, object], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual != expected:
        missing = ",".join(sorted(expected - actual)) or "none"
        extra = ",".join(sorted(actual - expected)) or "none"
        raise HandoffError(f"{label} fields mismatch; missing={missing}; extra={extra}")


def _object_list(value: object, label: str) -> list[dict[str, object]]:
    if not isinstance(value, list) or any(type(item) is not dict for item in value):
        raise HandoffError(f"{label} must be a list of objects")
    return value


def _string_list(value: object, label: str) -> list[str]:
    if not isinstance(value, list) or any(type(item) is not str for item in value):
        raise HandoffError(f"{label} must be a string list")
    if len(value) != len(set(value)):
        raise HandoffError(f"{label} must be unique")
    return value


def _positive_int(value: object, label: str) -> int:
    if type(value) is not int or not 0 < value <= MAX_ARTIFACT_BYTES:
        raise HandoffError(f"{label} is outside its positive bound")
    return value


def _positive_ordinal(value: object, label: str) -> int:
    if type(value) is not int or not 0 <= value < len(TASK_ORDER):
        raise HandoffError(f"{label} is outside its bounded range")
    return value


def _nonempty_string(value: object, label: str) -> str:
    if type(value) is not str or not value or len(value) > 512:
        raise HandoffError(f"{label} must be a bounded nonempty string")
    return value


def _commit_id(value: object, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise HandoffError(f"{label} must be one exact SHA-1 commit ID")
    return value


def _hex(value: object, length: int, label: str) -> str:
    if type(value) is not str or re.fullmatch(rf"[0-9a-f]{{{length}}}", value) is None:
        raise HandoffError(f"{label} must be {length} lowercase hexadecimal characters")
    return value


def _prover_compute_profile_id(value: object) -> str:
    if type(value) is not str or value not in PROVER_COMPUTE_PROFILE_IDS:
        raise HandoffError("prover compute profile is not governed")
    return value


def _prover_r0vm_expectation(
    compute_profile_id: str,
    sha256: str | None,
    size_bytes: int | None,
) -> dict[str, object]:
    if sha256 is None and size_bytes is None:
        if compute_profile_id != CPU_PROVER_COMPUTE_PROFILE_ID:
            raise HandoffError("CUDA compute profile requires one explicit prover r0vm identity")
        sha256 = OFFICIAL_CPU_R0VM_SHA256
        size_bytes = OFFICIAL_CPU_R0VM_BYTES
    elif sha256 is None or size_bytes is None:
        raise HandoffError("prover r0vm identity requires SHA-256 and byte length together")
    digest = _hex(sha256, 64, "prover r0vm SHA-256")
    bounded_size = _positive_int(size_bytes, "prover r0vm bytes")
    if (
        compute_profile_id == CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID
        and digest == OFFICIAL_CPU_R0VM_SHA256
        and bounded_size == OFFICIAL_CPU_R0VM_BYTES
    ):
        raise HandoffError("CUDA compute profile cannot select the known official CPU r0vm")
    return {
        "schema": PROVER_R0VM_EXPECTATION_SCHEMA,
        "compute_profile_id": compute_profile_id,
        "sha256": digest,
        "size_bytes": bounded_size,
        "source_to_binary_provenance_verified": False,
        "live_accelerator_execution_verified": False,
    }


def _validated_prover_r0vm_expectation(value: object) -> Mapping[str, object]:
    row = _object(value, "prover r0vm expectation")
    _require_exact_fields(
        row,
        {
            "schema",
            "compute_profile_id",
            "sha256",
            "size_bytes",
            "source_to_binary_provenance_verified",
            "live_accelerator_execution_verified",
        },
        "prover r0vm expectation",
    )
    if row.get("schema") != PROVER_R0VM_EXPECTATION_SCHEMA:
        raise HandoffError("prover r0vm expectation schema mismatch")
    profile_id = _prover_compute_profile_id(row.get("compute_profile_id"))
    expected = _prover_r0vm_expectation(
        profile_id,
        _hex(row.get("sha256"), 64, "prover r0vm expectation SHA-256"),
        _positive_int(row.get("size_bytes"), "prover r0vm expectation bytes"),
    )
    if not _canonical_values_equal(row, expected):
        raise HandoffError("prover r0vm expectation is not canonical and authority-false")
    return row


def _require_task_prover_r0vm_expectation(
    document: Mapping[str, object],
    task: Mapping[str, object],
    inputs: Sequence[Mapping[str, object]],
) -> None:
    stage_id = _nonempty_string(task.get("stage_id"), "task stage ID")
    if stage_id not in RISC0_COMPUTE_STAGE_IDS:
        return
    expectation = _validated_prover_r0vm_expectation(document.get("prover_r0vm_expectation"))
    matches = [row for row in inputs if row.get("role") == "prover_r0vm"]
    if len(matches) != 1:
        raise HandoffError("proving task lacks one exact prover r0vm record")
    observed = matches[0]
    if observed.get("sha256") != expectation.get("sha256") or observed.get(
        "size_bytes"
    ) != expectation.get("size_bytes"):
        raise HandoffError("prover r0vm expectation differs from exact task input bytes")


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    plan = subparsers.add_parser("plan")
    plan.add_argument("--repository", type=Path, required=True)
    plan.add_argument("--c0-commit", required=True)
    plan.add_argument("--worker-commit", required=True)
    plan.add_argument(
        "--prover-compute-profile",
        choices=PROVER_COMPUTE_PROFILE_IDS,
        default=CPU_PROVER_COMPUTE_PROFILE_ID,
    )
    plan.add_argument("--prover-r0vm-sha256")
    plan.add_argument("--prover-r0vm-bytes", type=int)
    plan.add_argument("--output", type=Path, required=True)
    prepare = subparsers.add_parser("prepare-task")
    prepare.add_argument("--repository", type=Path, required=True)
    prepare.add_argument("--handoff", type=Path, required=True)
    prepare.add_argument("--artifact-root", type=Path, required=True)
    prepare.add_argument("--stage", choices=TASK_ORDER, required=True)
    prepare.add_argument("--c0-commit", required=True)
    prepare.add_argument("--c1-commit", required=True)
    prepare.add_argument("--c2-commit", required=True)
    prepare.add_argument("--governance-commit", required=True)
    prepare.add_argument("--output", type=Path, required=True)
    capture = subparsers.add_parser("capture-return")
    capture.add_argument("--repository", type=Path, required=True)
    capture.add_argument("--handoff", type=Path, required=True)
    capture.add_argument("--artifact-root", type=Path, required=True)
    capture.add_argument("--execution-packet-directory", type=Path, required=True)
    capture.add_argument("--program-image-ids", type=Path, required=True)
    capture.add_argument("--c0-commit", required=True)
    capture.add_argument("--c1-commit", required=True)
    capture.add_argument("--c2-commit", required=True)
    capture.add_argument("--governance-commit", required=True)
    capture.add_argument("--output", type=Path, required=True)
    check = subparsers.add_parser("check-return")
    check.add_argument("--repository", type=Path, required=True)
    check.add_argument("--handoff", type=Path, required=True)
    check.add_argument("--bundle", type=Path, required=True)
    check.add_argument("--artifact-root", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.command == "plan":
            document = build_handoff(
                args.repository,
                args.c0_commit,
                args.worker_commit,
                prover_compute_profile_id=args.prover_compute_profile,
                prover_r0vm_sha256=args.prover_r0vm_sha256,
                prover_r0vm_bytes=args.prover_r0vm_bytes,
            )
            _write_new(args.output, canonical_json_bytes(document), "handoff output")
        elif args.command == "prepare-task":
            handoff = _object(load_canonical_json(args.handoff, "handoff"), "handoff")
            packet = build_execution_packet(
                handoff,
                args.stage,
                args.artifact_root,
                args.repository,
                c0_commit=args.c0_commit,
                c1_commit=args.c1_commit,
                c2_commit=args.c2_commit,
                governance_commit=args.governance_commit,
            )
            expected_name = _execution_packet_filename(
                _positive_ordinal(packet["ordinal"], "execution packet ordinal"),
                args.stage,
            )
            if args.output.name != expected_name:
                raise HandoffError("execution packet output filename mismatch")
            _write_new(
                args.output,
                canonical_json_bytes(packet),
                "execution packet output",
            )
        elif args.command == "capture-return":
            handoff = _object(load_canonical_json(args.handoff, "handoff"), "handoff")
            images = _object(
                load_canonical_json(args.program_image_ids, "program image IDs"),
                "program image IDs",
            )
            if set(images) != set(PROGRAM_ROLES):
                raise HandoffError("program image ID inventory mismatch")
            bundle = capture_return_bundle(
                handoff,
                args.artifact_root,
                args.repository,
                execution_packet_directory=args.execution_packet_directory,
                c0_commit=args.c0_commit,
                c1_commit=args.c1_commit,
                c2_commit=args.c2_commit,
                governance_commit=args.governance_commit,
                program_image_ids={
                    key: _hex(value, 64, f"{key} image ID") for key, value in images.items()
                },
            )
            _write_new(args.output, canonical_json_bytes(bundle), "return bundle output")
        else:
            handoff = _object(load_canonical_json(args.handoff, "handoff"), "handoff")
            bundle = _object(load_canonical_json(args.bundle, "return bundle"), "return bundle")
            validate_return_bundle(handoff, bundle, args.artifact_root, args.repository)
            sys.stdout.buffer.write(
                canonical_json_bytes(
                    {
                        "accepted": True,
                        "bundle_id": bundle["bundle_id"],
                        "authority": false_authority(),
                    }
                )
            )
    except (HandoffError, OSError, identity.RebuildPlanError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


def _write_new(path: Path, raw: bytes, label: str) -> None:
    descriptor: int | None = None
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        written = 0
        while written < len(raw):
            count = os.write(descriptor, raw[written:])
            if count <= 0:
                raise HandoffError(f"{label} write made no progress")
            written += count
        os.fsync(descriptor)
    except FileExistsError as exc:
        raise HandoffError(f"{label} must begin absent") from exc
    except OSError as exc:
        raise HandoffError(f"{label} write failed") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


if __name__ == "__main__":
    raise SystemExit(main())
