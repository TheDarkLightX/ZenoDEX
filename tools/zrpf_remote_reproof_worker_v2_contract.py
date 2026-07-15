"""Typed contract validation for the authority-neutral ZRPF reproof worker V2."""

from __future__ import annotations

import copy
import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Sequence

from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools.zrpf_remote_reproof_handoff_v2_catalog import (
    CPU_PROVER_COMPUTE_PROFILE_ID,
    CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID,
    NO_PROVER_COMPUTE_PROFILE_ID,
    RISC0_COMPUTE_STAGE_IDS,
)

CAPTURE_SCHEMA = "zenodex/zrpf_remote_reproof_worker_capture/v3"
RESOURCE_POLICY_SCHEMA = "zenodex/zrpf_remote_reproof_worker_resource_policy/v2"
PROVER_COMPUTE_PROFILE_SCHEMA = "zenodex/zrpf_remote_prover_compute_profile/v1"
CAPTURE_DOMAIN = b"zenodex/zrpf_remote_reproof_worker_capture_id/v3\0"
RESOURCE_POLICY_DOMAIN = b"zenodex/zrpf_remote_reproof_worker_resource_policy_id/v2\0"
PROVER_COMPUTE_PROFILE_DOMAIN = b"zenodex/zrpf_remote_prover_compute_profile_id/v1\0"
COMMAND_TEMPLATE_DOMAIN = b"zenodex/zrpf_remote_reproof_worker_command_template/v2\0"
RESOLVED_ARGV_DOMAIN = b"zenodex/zrpf_remote_reproof_worker_resolved_argv/v2\0"
ZERO_SHA256 = "0" * 64

WORKER_AUTHORITY_FIELDS = (
    "data_availability_authority",
    "ledger_authority",
    "production_authority",
    "proof_authority",
    "release_authority",
    "settlement_authority",
)

WORKER_NON_CLAIMS = (
    "worker_capture_does_not_verify_proof_validity_or_semantic_correctness",
    "worker_capture_does_not_authenticate_operator_authorization_or_packet_freshness",
    "worker_capture_is_an_unkeyed_local_process_observation",
    "worker_does_not_establish_source_to_binary_or_host_release_provenance",
    "worker_does_not_provide_a_network_mount_or_hardware_sandbox",
    "worker_does_not_resist_a_malicious_same_uid_host_process",
    "worker_does_not_install_a_kernel_cgroup_or_process_count_limit",
    "prover_compute_profile_does_not_attest_accelerator_identity_or_performance",
    "worker_does_not_grant_data_availability_finality_ledger_settlement_release_or_production_authority",
    "worker_does_not_atomically_publish_a_multi_stage_reproof_chain",
)

EXECUTION_PACKET_FIELDS = {
    "schema",
    "status",
    "execution_packet_id",
    "handoff_id",
    "source_binding_id",
    "task_id",
    "stage_id",
    "ordinal",
    "worker_commit",
    "worker_tree",
    "proof_profile_id",
    "input_artifact_ids",
    "authority",
    "non_claims",
}

ARTIFACT_CONTRACT_FIELDS = {
    "schema",
    "contract_id",
    "role",
    "path",
    "kind",
    "producer_stage",
    "maximum_bytes",
}

COMMAND_FIELDS = {
    "runner",
    "argv",
    "stdin_artifact_role",
    "stdout_artifact_role",
}

CAPTURE_FIELDS = {
    "schema",
    "status",
    "capture_id",
    "handoff_id",
    "execution_packet_id",
    "task_id",
    "stage_id",
    "ordinal",
    "resource_policy",
    "prover_compute_profile",
    "commands",
    "outputs",
    "authority",
    "non_claims",
}

COMMAND_CAPTURE_FIELDS = {
    "ordinal",
    "command_template_sha256",
    "resolved_argv_sha256",
    "runner_sha256",
    "runner_bytes",
    "stdout_sha256",
    "stdout_bytes",
    "stderr_sha256",
    "stderr_bytes",
    "exit_status",
    "duration_milliseconds",
}


class WorkerError(ValueError):
    """Stable fail-closed worker rejection."""


@dataclass(frozen=True, slots=True)
class ResourcePolicy:
    resource_class: str
    timeout_seconds: int
    maximum_stdout_bytes: int
    maximum_stderr_bytes: int
    maximum_output_file_bytes: int
    maximum_open_files: int
    maximum_address_space_bytes: int

    def record(self) -> dict[str, object]:
        value: dict[str, object] = {
            "schema": RESOURCE_POLICY_SCHEMA,
            "policy_id": ZERO_SHA256,
            "resource_class": self.resource_class,
            "timeout_seconds": self.timeout_seconds,
            "maximum_stdout_bytes": self.maximum_stdout_bytes,
            "maximum_stderr_bytes": self.maximum_stderr_bytes,
            "maximum_output_file_bytes": self.maximum_output_file_bytes,
            "maximum_open_files": self.maximum_open_files,
            "maximum_address_space_bytes": self.maximum_address_space_bytes,
        }
        value["policy_id"] = _domain_digest(RESOURCE_POLICY_DOMAIN, value)
        return value


@dataclass(frozen=True, slots=True)
class ProverComputeProfile:
    profile_id: str
    risc0_prover: str | None
    risc0_executor: str | None
    cuda_visible_devices: str | None

    def record(self) -> dict[str, object]:
        value: dict[str, object] = {
            "schema": PROVER_COMPUTE_PROFILE_SCHEMA,
            "policy_id": ZERO_SHA256,
            "profile_id": self.profile_id,
            "risc0_prover": self.risc0_prover,
            "risc0_executor": self.risc0_executor,
            "cuda_visible_devices": self.cuda_visible_devices,
        }
        value["policy_id"] = _domain_digest(PROVER_COMPUTE_PROFILE_DOMAIN, value)
        return value


RESOURCE_POLICIES = {
    "light": ResourcePolicy(
        "light",
        timeout_seconds=10 * 60,
        maximum_stdout_bytes=16 * 1024 * 1024,
        maximum_stderr_bytes=1024 * 1024,
        maximum_output_file_bytes=64 * 1024 * 1024,
        maximum_open_files=128,
        maximum_address_space_bytes=8 * 1024 * 1024 * 1024,
    ),
    "cargo": ResourcePolicy(
        "cargo",
        timeout_seconds=4 * 60 * 60,
        maximum_stdout_bytes=16 * 1024 * 1024,
        maximum_stderr_bytes=4 * 1024 * 1024,
        maximum_output_file_bytes=64 * 1024 * 1024,
        maximum_open_files=256,
        maximum_address_space_bytes=128 * 1024 * 1024 * 1024,
    ),
    "cpu_high_memory": ResourcePolicy(
        "cpu_high_memory",
        timeout_seconds=12 * 60 * 60,
        maximum_stdout_bytes=16 * 1024 * 1024,
        maximum_stderr_bytes=4 * 1024 * 1024,
        maximum_output_file_bytes=64 * 1024 * 1024,
        maximum_open_files=256,
        maximum_address_space_bytes=256 * 1024 * 1024 * 1024,
    ),
    "prover_heavy": ResourcePolicy(
        "prover_heavy",
        timeout_seconds=24 * 60 * 60,
        maximum_stdout_bytes=64 * 1024 * 1024,
        maximum_stderr_bytes=4 * 1024 * 1024,
        maximum_output_file_bytes=64 * 1024 * 1024,
        maximum_open_files=256,
        maximum_address_space_bytes=256 * 1024 * 1024 * 1024,
    ),
    "prover_light": ResourcePolicy(
        "prover_light",
        timeout_seconds=4 * 60 * 60,
        maximum_stdout_bytes=64 * 1024 * 1024,
        maximum_stderr_bytes=4 * 1024 * 1024,
        maximum_output_file_bytes=64 * 1024 * 1024,
        maximum_open_files=256,
        maximum_address_space_bytes=128 * 1024 * 1024 * 1024,
    ),
}

PROVER_COMPUTE_PROFILES = {
    NO_PROVER_COMPUTE_PROFILE_ID: ProverComputeProfile(
        NO_PROVER_COMPUTE_PROFILE_ID,
        risc0_prover=None,
        risc0_executor=None,
        cuda_visible_devices=None,
    ),
    CPU_PROVER_COMPUTE_PROFILE_ID: ProverComputeProfile(
        CPU_PROVER_COMPUTE_PROFILE_ID,
        risc0_prover="ipc",
        risc0_executor="ipc",
        cuda_visible_devices="-1",
    ),
    CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID: ProverComputeProfile(
        CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID,
        risc0_prover="ipc",
        risc0_executor="ipc",
        cuda_visible_devices="0",
    ),
}


@dataclass(frozen=True, slots=True)
class ArtifactContract:
    contract_id: str
    role: str
    path: str
    kind: str
    producer_stage: str
    maximum_bytes: int
    raw: Mapping[str, object]


@dataclass(frozen=True, slots=True)
class CommandTemplate:
    runner: str
    argv: tuple[str, ...]
    stdin_artifact_role: str | None
    stdout_artifact_role: str | None
    raw: Mapping[str, object]

    @property
    def template_sha256(self) -> str:
        return _domain_digest(COMMAND_TEMPLATE_DOMAIN, self.raw)


@dataclass(frozen=True, slots=True)
class ValidatedStage:
    handoff_id: str
    execution_packet_id: str
    task_id: str
    stage_id: str
    ordinal: int
    worker_commit: str
    worker_tree: str
    c0_commit: str
    resource_policy: ResourcePolicy
    prover_compute_profile: ProverComputeProfile
    commands: tuple[CommandTemplate, ...]
    inputs: tuple[ArtifactContract, ...]
    input_records: tuple[Mapping[str, object], ...]
    outputs: tuple[ArtifactContract, ...]


def false_authority() -> dict[str, bool]:
    return {field: False for field in WORKER_AUTHORITY_FIELDS}


def derive_capture_id(document: Mapping[str, object]) -> str:
    value = copy.deepcopy(dict(document))
    value["capture_id"] = ZERO_SHA256
    return _domain_digest(CAPTURE_DOMAIN, value)


def resolved_argv_sha256(argv: Sequence[str]) -> str:
    framed = bytearray(RESOLVED_ARGV_DOMAIN)
    for item in argv:
        encoded = item.encode("utf-8", errors="strict")
        framed.extend(len(encoded).to_bytes(4, "big"))
        framed.extend(encoded)
    return hashlib.sha256(framed).hexdigest()


def validate_stage_packet(
    document: Mapping[str, object],
    packet: Mapping[str, object],
    repo_root: Path,
    artifact_root: Path,
) -> ValidatedStage:
    """Authenticate one existing packet against the closed handoff catalog and bytes."""

    handoff.validate_handoff(document, repo_root)
    _require_exact_fields(packet, EXECUTION_PACKET_FIELDS, "execution packet")
    if packet.get("schema") != handoff.EXECUTION_PACKET_SCHEMA:
        raise WorkerError("execution packet schema mismatch")
    if packet.get("status") != "exact_inputs_bound_without_execution_provenance":
        raise WorkerError("execution packet status mismatch")
    packet_id = _hex(packet.get("execution_packet_id"), "execution packet ID")
    if packet_id != handoff.derive_execution_packet_id(packet):
        raise WorkerError("execution packet ID mismatch")

    source = _object(document.get("source"), "handoff source")
    tasks = _object_list(document.get("tasks"), "handoff tasks")
    stage_id = _bounded_string(packet.get("stage_id"), "execution packet stage")
    matching = [task for task in tasks if task.get("stage_id") == stage_id]
    if len(matching) != 1:
        raise WorkerError("execution packet stage is not one governed task")
    task = matching[0]

    contracts = _object_list(document.get("artifact_contracts"), "artifact contracts")
    contracts_by_id = {
        _hex(row.get("contract_id"), "artifact contract ID"): _artifact_contract(row)
        for row in contracts
    }
    inputs = tuple(
        contracts_by_id[item]
        for item in _string_list(
            task.get("input_artifact_contract_ids"), "task input artifact contract IDs"
        )
    )
    outputs = tuple(
        contracts_by_id[item]
        for item in _string_list(
            task.get("output_artifact_contract_ids"), "task output artifact contract IDs"
        )
    )
    root = _canonical_directory(artifact_root, "input artifact root")
    input_records = tuple(handoff._artifact_record(item.raw, root) for item in inputs)
    handoff._require_aggregate_artifact_bound(input_records)
    handoff._require_task_prover_r0vm_expectation(document, task, input_records)
    expected_packet = handoff._execution_packet(
        task,
        source,
        {
            "governance_commit": source["worker_commit"],
            "governance_tree": source["worker_tree"],
        },
        input_records,
    )
    expected_packet["handoff_id"] = document["handoff_id"]
    expected_packet["execution_packet_id"] = handoff.derive_execution_packet_id(expected_packet)
    if not handoff._canonical_values_equal(packet, expected_packet):
        raise WorkerError("execution packet differs from exact current input artifacts")

    if task.get("command_status") != "template_available":
        raise WorkerError("task command template is not executable")
    if task.get("execution_adapter_status") != "implemented":
        raise WorkerError("task execution adapter is not implemented")
    resource_class = _bounded_string(task.get("resource_class"), "task resource class")
    try:
        resource_policy = RESOURCE_POLICIES[resource_class]
    except KeyError as exc:
        raise WorkerError("task resource class is not governed") from exc
    compute_profile_id = _bounded_string(
        task.get("prover_compute_profile_id"),
        "task prover compute profile",
    )
    try:
        compute_profile = PROVER_COMPUTE_PROFILES[compute_profile_id]
    except KeyError as exc:
        raise WorkerError("task prover compute profile is not governed") from exc
    expected_compute_profile_id = (
        _bounded_string(
            document.get("prover_compute_profile_id"),
            "handoff prover compute profile",
        )
        if stage_id in RISC0_COMPUTE_STAGE_IDS
        else NO_PROVER_COMPUTE_PROFILE_ID
    )
    if compute_profile_id != expected_compute_profile_id:
        raise WorkerError("task prover compute profile binding mismatch")
    if compute_profile.risc0_prover is not None and not any(
        contract.role == "prover_r0vm" and contract.kind == "executable" for contract in inputs
    ):
        raise WorkerError("prover task lacks the packet-bound prover r0vm executable")
    commands = tuple(
        _command_template(row)
        for row in _object_list(task.get("commands"), "task command templates")
    )
    if not commands:
        raise WorkerError("task must contain at least one command template")
    return ValidatedStage(
        handoff_id=_hex(document.get("handoff_id"), "handoff ID"),
        execution_packet_id=packet_id,
        task_id=_hex(task.get("task_id"), "task ID"),
        stage_id=stage_id,
        ordinal=_bounded_nonnegative_int(task.get("ordinal"), "task ordinal"),
        worker_commit=_commit_id(source.get("worker_commit"), "worker commit"),
        worker_tree=_commit_id(source.get("worker_tree"), "worker tree"),
        c0_commit=_commit_id(source.get("c0_commit"), "C0 commit"),
        resource_policy=resource_policy,
        prover_compute_profile=compute_profile,
        commands=commands,
        inputs=inputs,
        input_records=input_records,
        outputs=outputs,
    )


def validate_worker_checkout(stage: ValidatedStage, repo_root: Path) -> Path:
    root = _canonical_directory(repo_root, "worker repository")
    head = handoff._git(root, ["rev-parse", "HEAD"], 128).decode("ascii").strip()
    if head != stage.worker_commit:
        raise WorkerError("worker repository HEAD differs from packet worker commit")
    tree = handoff._git(root, ["rev-parse", "HEAD^{tree}"], 128).decode("ascii").strip()
    if tree != stage.worker_tree:
        raise WorkerError("worker repository tree differs from packet worker tree")
    status = handoff._git(
        root,
        ["status", "--porcelain=v1", "--untracked-files=all"],
        1024 * 1024,
    )
    if status:
        raise WorkerError("worker repository must be clean including untracked files")
    return root


def validate_capture_shape(
    capture: Mapping[str, object], stage: ValidatedStage
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    _require_exact_fields(capture, CAPTURE_FIELDS, "worker capture")
    if capture.get("schema") != CAPTURE_SCHEMA:
        raise WorkerError("worker capture schema mismatch")
    if capture.get("status") != "outputs_captured_without_proof_or_release_authority":
        raise WorkerError("worker capture status mismatch")
    if _hex(capture.get("capture_id"), "worker capture ID") != derive_capture_id(capture):
        raise WorkerError("worker capture ID mismatch")
    for field, expected in (
        ("handoff_id", stage.handoff_id),
        ("execution_packet_id", stage.execution_packet_id),
        ("task_id", stage.task_id),
        ("stage_id", stage.stage_id),
    ):
        if capture.get(field) != expected:
            raise WorkerError(f"worker capture {field} mismatch")
    if type(capture.get("ordinal")) is not int or capture.get("ordinal") != stage.ordinal:
        raise WorkerError("worker capture ordinal mismatch")
    if not handoff._canonical_values_equal(
        capture.get("resource_policy"), stage.resource_policy.record()
    ):
        raise WorkerError("worker capture resource policy mismatch")
    if not handoff._canonical_values_equal(
        capture.get("prover_compute_profile"),
        stage.prover_compute_profile.record(),
    ):
        raise WorkerError("worker capture prover compute profile mismatch")
    _require_false_authority(capture.get("authority"), "worker capture authority")
    if not handoff._canonical_values_equal(capture.get("non_claims"), list(WORKER_NON_CLAIMS)):
        raise WorkerError("worker capture non-claims mismatch")
    commands = _object_list(capture.get("commands"), "worker command captures")
    if len(commands) != len(stage.commands):
        raise WorkerError("worker command capture inventory mismatch")
    for index, (command, template) in enumerate(zip(commands, stage.commands, strict=True)):
        _require_exact_fields(command, COMMAND_CAPTURE_FIELDS, "worker command capture")
        if type(command.get("ordinal")) is not int or command.get("ordinal") != index:
            raise WorkerError("worker command capture ordinal mismatch")
        if command.get("command_template_sha256") != template.template_sha256:
            raise WorkerError("worker command template digest mismatch")
        for name in (
            "resolved_argv_sha256",
            "runner_sha256",
            "stdout_sha256",
            "stderr_sha256",
        ):
            _hex(command.get(name), f"worker command {name}")
        for name in (
            "runner_bytes",
            "stdout_bytes",
            "stderr_bytes",
            "duration_milliseconds",
        ):
            _bounded_nonnegative_int(command.get(name), f"worker command {name}")
        if type(command.get("exit_status")) is not int or command.get("exit_status") != 0:
            raise WorkerError("worker command exit status must be exact integer zero")
    outputs = _object_list(capture.get("outputs"), "worker output artifacts")
    return commands, outputs


def _artifact_contract(value: Mapping[str, object]) -> ArtifactContract:
    _require_exact_fields(value, ARTIFACT_CONTRACT_FIELDS, "artifact contract")
    return ArtifactContract(
        contract_id=_hex(value.get("contract_id"), "artifact contract ID"),
        role=_bounded_string(value.get("role"), "artifact role"),
        path=handoff._safe_relative_path(value.get("path"), "artifact path"),
        kind=_bounded_string(value.get("kind"), "artifact kind"),
        producer_stage=_bounded_string(value.get("producer_stage"), "artifact producer stage"),
        maximum_bytes=handoff._positive_int(value.get("maximum_bytes"), "artifact maximum bytes"),
        raw=value,
    )


def _command_template(value: Mapping[str, object]) -> CommandTemplate:
    _require_exact_fields(value, COMMAND_FIELDS, "command template")
    runner = _bounded_string(value.get("runner"), "command runner")
    argv = tuple(_string_list(value.get("argv"), "command argv"))
    stdin_role = value.get("stdin_artifact_role")
    stdout_role = value.get("stdout_artifact_role")
    if stdin_role is not None:
        stdin_role = _bounded_string(stdin_role, "command stdin artifact role")
    if stdout_role is not None:
        stdout_role = _bounded_string(stdout_role, "command stdout artifact role")
    return CommandTemplate(runner, argv, stdin_role, stdout_role, value)


def _require_false_authority(value: object, label: str) -> None:
    authority = _object(value, label)
    _require_exact_fields(authority, set(WORKER_AUTHORITY_FIELDS), label)
    if any(authority[field] is not False for field in WORKER_AUTHORITY_FIELDS):
        raise WorkerError(f"{label} must contain exact Boolean false values")


def _canonical_directory(path: Path, label: str) -> Path:
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise WorkerError(f"{label} is unavailable") from exc
    if resolved != path or not resolved.is_dir():
        raise WorkerError(f"{label} must be one real canonical directory")
    return resolved


def _domain_digest(domain: bytes, value: object) -> str:
    return hashlib.sha256(domain + handoff.canonical_json_bytes(value)).hexdigest()


def _object(value: object, label: str) -> dict[str, object]:
    if type(value) is not dict:
        raise WorkerError(f"{label} must be an object")
    return value


def _object_list(value: object, label: str) -> list[dict[str, object]]:
    if not isinstance(value, list) or any(type(item) is not dict for item in value):
        raise WorkerError(f"{label} must be a list of objects")
    return value


def _string_list(value: object, label: str) -> list[str]:
    if not isinstance(value, list) or any(type(item) is not str for item in value):
        raise WorkerError(f"{label} must be a string list")
    if len(value) != len(set(value)):
        raise WorkerError(f"{label} must be unique")
    return value


def _require_exact_fields(value: Mapping[str, object], expected: set[str], label: str) -> None:
    if set(value) != expected:
        raise WorkerError(f"{label} fields mismatch")


def _bounded_string(value: object, label: str) -> str:
    if type(value) is not str or not value or len(value) > 512:
        raise WorkerError(f"{label} must be one bounded nonempty string")
    return value


def _bounded_nonnegative_int(value: object, label: str) -> int:
    if type(value) is not int or not 0 <= value <= (1 << 63) - 1:
        raise WorkerError(f"{label} must be one bounded nonnegative integer")
    return value


def _hex(value: object, label: str) -> str:
    try:
        return handoff._hex(value, 64, label)
    except handoff.HandoffError as exc:
        raise WorkerError(str(exc)) from exc


def _commit_id(value: object, label: str) -> str:
    try:
        return handoff._commit_id(value, label)
    except handoff.HandoffError as exc:
        raise WorkerError(str(exc)) from exc
