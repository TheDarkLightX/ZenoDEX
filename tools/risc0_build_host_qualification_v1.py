"""Pure schema, canonical JSON, and classification rules for O-008A.

This module has no filesystem, subprocess, network, Cargo, Rust, or proof
effects. The builder supplies committed-object observations and the checker
replays them. A blocked artifact is research evidence only: it never grants
build-host, proof, release, settlement, or value-moving authority.
"""

from __future__ import annotations

import ast
import hashlib
import json
import re
from dataclasses import dataclass
from typing import Final, NoReturn, cast

SCHEMA_V1: Final = "zenodex/risc0_build_host_qualification/v1"
CHECK_SCHEMA_V1: Final = "zenodex/risc0_build_host_qualification_check/v1"
CANONICAL_ENCODING_V1: Final = "json/sort-keys-utf8/v1"
EXPECTED_PARENT_SHA256_V1: Final = "59a3565b77d993a374631c2554734ce152438e15"
OBLIGATION_ID_V1: Final = "O-008A"
REQUIRED_RISC0_VERSION_V1: Final = "3.0.6"
REQUIRED_RISC0_REQUIREMENT_V1: Final = "=3.0.6"
PLAN_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
DEPENDENCY_POLICY_PATH_V1: Final = "tools/risc0_dependency_policy_v1.py"
DEPENDENCY_INVENTORY_PATH_V1: Final = "tools/risc0_dependency_inventory_v1.py"
DEPENDENCY_AUDIT_CHECKER_PATH_V1: Final = "tools/check_risc0_dependency_audit.py"
CORE_PATH_V1: Final = "tools/risc0_build_host_qualification_v1.py"
BUILDER_PATH_V1: Final = "tools/build_risc0_build_host_qualification_v1.py"
CHECKER_PATH_V1: Final = "tools/check_risc0_build_host_qualification_v1.py"
TEST_PATH_V1: Final = "tests/test_check_risc0_build_host_qualification_v1.py"
ARTIFACT_PATH_V1: Final = "docs/research/ZENODEX_RISC0_BUILD_HOST_QUALIFICATION_V1.json"
LEGACY_WORKSPACE_V1: Final = "zk/state_proof_risc0"
LEGACY_LOCK_PATH_V1: Final = f"{LEGACY_WORKSPACE_V1}/Cargo.lock"
LEGACY_ROOT_MANIFEST_PATH_V1: Final = f"{LEGACY_WORKSPACE_V1}/Cargo.toml"
REQUIRED_LOCKED_PACKAGES_V1: Final = ("risc0-build", "risc0-zkvm")
REQUIRED_TMPDIR_V1: Final = "/dev/shm"
EXACT_EVIDENCE_REPLAY_SCOPE_V1: Final = "EXACT_EVIDENCE_COMMIT_E_ONLY"
IMMUTABLE_BOOTSTRAP_PREREQUISITE_V1: Final = "EXTERNAL_PINNED_EXECUTABLE_CLOSURE_REQUIRED"
IMMUTABLE_BOOTSTRAP_MINIMUM_SUBJECTS_V1: Final = (
    "checker_source_bytes_and_sha256",
    "core_source_bytes_and_sha256",
    "builder_source_bytes_and_sha256",
    "tools_package_initializer_source_bytes_and_sha256",
    "dependency_policy_source_bytes_and_sha256",
    "dependency_inventory_source_bytes_and_sha256",
    "dependency_audit_source_bytes_and_sha256",
    "python_interpreter_absolute_path_mode_size_and_sha256",
    "git_executable_absolute_path_mode_size_and_sha256",
    "repository_git_metadata_and_object_store_integrity",
    "expected_implementation_commit_c_oid",
    "expected_evidence_commit_e_oid",
)
IMMUTABLE_BOOTSTRAP_CLOSURE_RULE_V1: Final = (
    "EXTERNAL_LAUNCHER_MUST_BIND_ALL_TRANSITIVELY_EXECUTED_CODE_RUNTIME_"
    "LIBRARIES_STARTUP_CUSTOMIZATION_IMPORT_PATHS_ENVIRONMENT_AND_ARGV"
)
MINIMUM_TMP_FREE_BYTES_V1: Final = 50 * 1024 * 1024
MINIMUM_AVAILABLE_MEMORY_BYTES_V1: Final = 128 * 1024 * 1024

MAX_ARTIFACT_BYTES_V1: Final = 512 * 1024
MAX_JSON_DEPTH_V1: Final = 64
MAX_JSON_NODES_V1: Final = 16_384
MAX_JSON_STRING_CHARS_V1: Final = 131_072
MAX_JSON_INTEGER_DIGITS_V1: Final = 128
MAX_JSON_INTEGER_BITS_V1: Final = 424

_OID_RE: Final = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
_SHA256_RE: Final = re.compile(r"^sha256:[0-9a-f]{64}$")
_VERSION_RE: Final = re.compile(r"^[0-9]+\.[0-9]+\.[0-9]+$")

IMPLEMENTATION_PATHS_V1: Final = (
    BUILDER_PATH_V1,
    CHECKER_PATH_V1,
    CORE_PATH_V1,
    TEST_PATH_V1,
)
STATIC_SOURCE_PATHS_V1: Final = tuple(
    sorted(
        (
            CORE_PATH_V1,
            BUILDER_PATH_V1,
            CHECKER_PATH_V1,
            TEST_PATH_V1,
            PLAN_PATH_V1,
            DEPENDENCY_POLICY_PATH_V1,
            DEPENDENCY_INVENTORY_PATH_V1,
            DEPENDENCY_AUDIT_CHECKER_PATH_V1,
        )
    )
)

EXACT_O008A_PLAN_ROW_V1: Final[dict[str, object]] = {
    "obligation_id": "O-008A",
    "phase": "P3",
    "priority": "P1",
    "title": "Qualify a reproducible Rust and RISC0 build host before parity or proof claims",
    "depends_on": ["O-001"],
    "closes": ["build_host_qualification_gap"],
    "required_evidence": [
        "exact toolchain locks",
        "disk and memory budget",
        "clean build receipt",
        "RISC0 3.0.6 image rebuild receipt",
        "artifact hashes",
        "no production authority",
    ],
}


@dataclass(frozen=True)
class QualificationRejectV1(ValueError):
    """Stable malformed-input rejection for O-008A boundary data."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


@dataclass(frozen=True)
class SourceEntryV1:
    """One Git-tree source object bound into the closed O-008A inventory."""

    path: str
    git_mode: str
    size_bytes: int
    blob_oid: str
    sha256: str

    def to_json(self) -> dict[str, object]:
        return {
            "path": self.path,
            "git_mode": self.git_mode,
            "size_bytes": self.size_bytes,
            "blob_oid": self.blob_oid,
            "sha256": self.sha256,
        }


@dataclass(frozen=True)
class ResourceObservationV1:
    """Bounded staging facts, explicitly insufficient for a capacity claim."""

    tmpdir_matches_required: bool
    free_tmp_bytes: int | None
    available_memory_bytes: int | None


@dataclass(frozen=True)
class QualificationSourceSnapshotV1:
    """Committed-object inputs used to render an O-008A artifact."""

    base_commit: str
    implementation_commit: str
    implementation_tree: str
    source_entries: tuple[SourceEntryV1, ...]
    exact_plan_row: dict[str, object]
    required_version_source: str
    dependency_policy_report: dict[str, object]
    legacy_manifest_requirements: tuple[dict[str, object], ...]
    legacy_lock_versions: tuple[dict[str, object], ...]


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise QualificationRejectV1(code, path, detail)


def _validate_scalar_string_v1(value: str, label: str) -> None:
    if len(value) > MAX_JSON_STRING_CHARS_V1:
        _reject("JSON_STRING_LIMIT", label, "string exceeds the bounded character limit")
    if any(0xD800 <= ord(character) <= 0xDFFF for character in value):
        _reject("JSON_STRING_SURROGATE", label, "lone or mixed surrogate escape is forbidden")


def _validate_json_value_v1(value: object, *, label: str) -> None:
    node_count = 0

    def visit(item: object, depth: int, item_label: str) -> None:
        nonlocal node_count
        if depth > MAX_JSON_DEPTH_V1:
            _reject("JSON_DEPTH", item_label, "maximum nesting depth exceeded")
        node_count += 1
        if node_count > MAX_JSON_NODES_V1:
            _reject("JSON_NODE_LIMIT", item_label, "maximum JSON node count exceeded")
        item_type = type(item)
        if item is None or item_type is bool:
            return
        if item_type is int:
            integer = cast(int, item)
            if integer.bit_length() > MAX_JSON_INTEGER_BITS_V1:
                _reject("JSON_INTEGER_LIMIT", item_label, "integer exceeds the bounded digit limit")
            return
        if item_type is str:
            _validate_scalar_string_v1(cast(str, item), item_label)
            return
        if item_type is list:
            children = cast(list[object], item)
            for index, child in enumerate(children):
                visit(child, depth + 1, f"{item_label}[{index}]")
            return
        if item_type is dict:
            object_items = cast(dict[object, object], item)
            for key, child in object_items.items():
                if type(key) is not str:
                    _reject("JSON_KEY_TYPE", item_label, "object keys must be exact strings")
                _validate_scalar_string_v1(key, f"{item_label}.<key>")
                visit(child, depth + 1, f"{item_label}.{key}")
            return
        _reject("JSON_VALUE_TYPE", item_label, f"unsupported JSON type {item_type.__name__}")

    visit(value, 0, label)


def canonical_json_bytes_v1(value: object) -> bytes:
    """Encode exact JSON primitives with one UTF-8, duplicate-free representation."""

    _validate_json_value_v1(value, label="json")
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
    except (OverflowError, TypeError, UnicodeEncodeError, ValueError) as exc:
        _reject("JSON_CANONICALIZE", "json", type(exc).__name__)


def decode_json_object_v1(
    raw: bytes,
    label: str,
    *,
    max_bytes: int = MAX_ARTIFACT_BYTES_V1,
) -> dict[str, object]:
    """Decode bounded, scalar-valid, duplicate-free JSON into an exact object."""

    if type(raw) is not bytes:
        _reject("JSON_RAW_TYPE", label, "raw JSON input must be bytes")
    if type(max_bytes) is not int or max_bytes <= 0:
        _reject("JSON_BOUND", label, "maximum byte bound must be a positive exact integer")
    if len(raw) > max_bytes:
        _reject("JSON_SIZE_LIMIT", label, "input exceeds the bounded byte limit")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        _reject("JSON_UTF8", label, type(exc).__name__)

    def reject_float(_value: str) -> NoReturn:
        _reject("JSON_FLOAT", label, "floating-point values and constants are forbidden")

    def parse_integer(value: str) -> int:
        digits = value[1:] if value.startswith("-") else value
        if not digits or len(digits) > MAX_JSON_INTEGER_DIGITS_V1:
            _reject("JSON_INTEGER_LIMIT", label, "integer exceeds the bounded digit limit")
        try:
            return int(value)
        except ValueError as exc:
            _reject("JSON_INTEGER", label, type(exc).__name__)

    def exact_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            _validate_scalar_string_v1(key, f"{label}.<key>")
            if key in result:
                _reject("JSON_DUPLICATE_KEY", label, key)
            result[key] = value
        return result

    try:
        decoded: object = json.loads(
            text,
            parse_float=reject_float,
            parse_constant=reject_float,
            parse_int=parse_integer,
            object_pairs_hook=exact_object,
        )
    except QualificationRejectV1:
        raise
    except (json.JSONDecodeError, OverflowError, RecursionError, ValueError) as exc:
        code = "JSON_DEPTH" if isinstance(exc, RecursionError) else "JSON_DECODE"
        _reject(code, label, type(exc).__name__)
    if type(decoded) is not dict:
        _reject("JSON_ROOT_TYPE", label, "root must be an exact object")
    _validate_json_value_v1(decoded, label=label)
    return decoded


def sha256_prefixed_v1(raw: bytes) -> str:
    if type(raw) is not bytes:
        _reject("SHA256_INPUT_TYPE", "sha256", "hash input must be bytes")
    return "sha256:" + hashlib.sha256(raw).hexdigest()


def is_git_oid_v1(value: object) -> bool:
    return type(value) is str and _OID_RE.fullmatch(value) is not None


def is_sha256_v1(value: object) -> bool:
    return type(value) is str and _SHA256_RE.fullmatch(value) is not None


def validate_exact_o008a_plan_row_v1(plan: object) -> dict[str, object]:
    """Require exactly one, field-for-field O-008A plan row."""

    if type(plan) is not dict:
        _reject("PLAN_ROOT_TYPE", PLAN_PATH_V1, "plan root must be an exact object")
    obligations = plan.get("next_obligations")
    if type(obligations) is not list:
        _reject("PLAN_SHAPE", PLAN_PATH_V1, "next_obligations must be an exact list")
    matches = [
        row
        for row in obligations
        if type(row) is dict and row.get("obligation_id") == OBLIGATION_ID_V1
    ]
    if len(matches) != 1:
        _reject("PLAN_O008A_CARDINALITY", PLAN_PATH_V1, "exactly one O-008A row is required")
    row = matches[0]
    if row != EXACT_O008A_PLAN_ROW_V1:
        _reject("PLAN_O008A_ROW_DRIFT", PLAN_PATH_V1, "O-008A row differs from the full expected row")
    return dict(row)


def required_version_from_inventory_source_v1(raw: bytes) -> str:
    """Extract the sole literal GOVERNED_RISC0_VERSION from committed source."""

    try:
        source = raw.decode("utf-8")
        tree = ast.parse(source, filename=DEPENDENCY_INVENTORY_PATH_V1, mode="exec")
    except (SyntaxError, UnicodeDecodeError) as exc:
        _reject("REQUIRED_VERSION_SOURCE_PARSE", DEPENDENCY_INVENTORY_PATH_V1, type(exc).__name__)
    values: list[str] = []
    for statement in tree.body:
        if not isinstance(statement, ast.Assign):
            continue
        target_names = [target.id for target in statement.targets if isinstance(target, ast.Name)]
        if "GOVERNED_RISC0_VERSION" not in target_names:
            continue
        if isinstance(statement.value, ast.Constant) and type(statement.value.value) is str:
            values.append(statement.value.value)
        else:
            _reject(
                "REQUIRED_VERSION_SOURCE_SHAPE",
                DEPENDENCY_INVENTORY_PATH_V1,
                "GOVERNED_RISC0_VERSION must be one literal string assignment",
            )
    if len(values) != 1 or _VERSION_RE.fullmatch(values[0]) is None:
        _reject(
            "REQUIRED_VERSION_SOURCE_SHAPE",
            DEPENDENCY_INVENTORY_PATH_V1,
            "one exact semantic-version assignment is required",
        )
    return values[0]


def _claim_scope_v1() -> dict[str, object]:
    return {
        "build_host_qualified": False,
        "parity": "NOT_CLAIMED",
        "production": "NOT_CLAIMED",
        "production_authority": "NONE",
        "proof_validity": "NOT_CLAIMED",
        "receipt_replay": "NOT_CLAIMED",
        "release": "NOT_CLAIMED",
        "release_authority": "NONE",
        "settlement": "NOT_CLAIMED",
        "settlement_authority": "NONE",
        "value_movement": "NOT_CLAIMED",
        "value_movement_authority": "NONE",
    }


def _immutable_bootstrap_nonclaim_v1() -> dict[str, object]:
    """Describe a minimum TCB floor without claiming self-authentication."""

    return {
        "closure_rule": IMMUTABLE_BOOTSTRAP_CLOSURE_RULE_V1,
        "minimum_subjects": list(IMMUTABLE_BOOTSTRAP_MINIMUM_SUBJECTS_V1),
        "process_isolation": (
            "EXTERNAL_SANDBOX_REQUIRED_FOR_DESCENDANTS_ESCAPING_THE_GIT_PROCESS_GROUP"
        ),
        "self_bootstrap": "NOT_CLAIMED",
        "status": IMMUTABLE_BOOTSTRAP_PREREQUISITE_V1,
    }


def _toolchain_gate_status_v1(snapshot: QualificationSourceSnapshotV1) -> str:
    if snapshot.required_version_source != REQUIRED_RISC0_VERSION_V1:
        return "BLOCKED_REQUIRED_TOOLCHAIN_PIN_DRIFT"
    requirements_by_package: dict[str, list[object]] = {}
    for row in snapshot.legacy_manifest_requirements:
        package = row.get("package") if type(row) is dict else None
        requirement = row.get("requirement") if type(row) is dict else None
        if type(package) is str:
            requirements_by_package.setdefault(package, []).append(requirement)
    for package in REQUIRED_LOCKED_PACKAGES_V1:
        requirements = requirements_by_package.get(package, [])
        if not requirements or any(requirement != REQUIRED_RISC0_REQUIREMENT_V1 for requirement in requirements):
            return "BLOCKED_TOOLCHAIN_VERSION_MISMATCH"
    versions_by_package: dict[str, list[object]] = {}
    for row in snapshot.legacy_lock_versions:
        package = row.get("package") if type(row) is dict else None
        versions = row.get("versions") if type(row) is dict else None
        if type(package) is str and type(versions) is list:
            versions_by_package[package] = list(versions)
    for package in REQUIRED_LOCKED_PACKAGES_V1:
        versions = versions_by_package.get(package, [])
        if versions != [REQUIRED_RISC0_VERSION_V1]:
            return "BLOCKED_TOOLCHAIN_VERSION_MISMATCH"
    if snapshot.dependency_policy_report.get("ok") is not True:
        return "BLOCKED_DEPENDENCY_POLICY_REJECTED"
    return "TOOLCHAIN_GATES_PASSED"


def _resource_status_v1(resource: ResourceObservationV1 | None) -> str:
    if resource is None or not resource.tmpdir_matches_required:
        return "BLOCKED_RESOURCE_EVIDENCE_INSUFFICIENT"
    if resource.free_tmp_bytes is None or resource.available_memory_bytes is None:
        return "BLOCKED_RESOURCE_EVIDENCE_INSUFFICIENT"
    if (
        resource.free_tmp_bytes < MINIMUM_TMP_FREE_BYTES_V1
        or resource.available_memory_bytes < MINIMUM_AVAILABLE_MEMORY_BYTES_V1
    ):
        return "BLOCKED_RESOURCE_BUDGET"
    return "BLOCKED_BUILD_EVIDENCE_REQUIRED"


def _resource_projection_v1(
    toolchain_status: str,
    resource: ResourceObservationV1 | None,
) -> dict[str, object]:
    common: dict[str, object] = {
        "does_not_claim_risc0_build_capacity": True,
        "minimum_available_memory_bytes": MINIMUM_AVAILABLE_MEMORY_BYTES_V1,
        "minimum_tmp_free_bytes": MINIMUM_TMP_FREE_BYTES_V1,
        "required_tmpdir": REQUIRED_TMPDIR_V1,
    }
    if toolchain_status != "TOOLCHAIN_GATES_PASSED":
        return {"capture_state": "DEFERRED_UNTIL_TOOLCHAIN_GATES_PASS", **common}
    if (
        resource is None
        or not resource.tmpdir_matches_required
        or resource.free_tmp_bytes is None
        or resource.available_memory_bytes is None
    ):
        return {"capture_state": "INSUFFICIENT_AFTER_TOOLCHAIN_GATES_PASS", **common}
    return {
        "capture_state": "OBSERVED_AFTER_TOOLCHAIN_GATES_PASS",
        "observed_available_memory_bytes": resource.available_memory_bytes,
        "observed_tmp_free_bytes": resource.free_tmp_bytes,
        "tmpdir_matches_required": resource.tmpdir_matches_required,
        **common,
    }


def with_artifact_payload_digest_v1(artifact: dict[str, object]) -> dict[str, object]:
    """Add the hash of all artifact fields except the self-excluding digest."""

    payload = {key: value for key, value in artifact.items() if key != "artifact_payload_sha256"}
    result = dict(payload)
    result["artifact_payload_sha256"] = sha256_prefixed_v1(canonical_json_bytes_v1(payload))
    return result


def build_qualification_artifact_v1(
    snapshot: QualificationSourceSnapshotV1,
    *,
    resource: ResourceObservationV1 | None,
) -> dict[str, object]:
    """Render the deterministic, non-promoting artifact projection for C."""

    toolchain_status = _toolchain_gate_status_v1(snapshot)
    status = (
        _resource_status_v1(resource)
        if toolchain_status == "TOOLCHAIN_GATES_PASSED"
        else toolchain_status
    )
    artifact: dict[str, object] = {
        "schema": SCHEMA_V1,
        "version": 1,
        "canonical_encoding": CANONICAL_ENCODING_V1,
        "artifact_state": "REPLAY_READY_QUALIFICATION_BLOCKED",
        "result": {
            "blocked": True,
            "build_host_qualification_gap_closed": False,
            "qualification_eligible": False,
            "status": status,
        },
        "replay": {
            "artifact_commit_oid": "CHECKER_DERIVED_FROM_EXACT_HEAD_E",
            "artifact_commit_shape": {
                "artifact_path": ARTIFACT_PATH_V1,
                "change_kind": "ADD",
                "direct_parent": "implementation_commit",
                "permitted_paths": [ARTIFACT_PATH_V1],
            },
            "base_commit": snapshot.base_commit,
            "verification_scope": EXACT_EVIDENCE_REPLAY_SCOPE_V1,
            "implementation_commit": snapshot.implementation_commit,
            "implementation_tree": snapshot.implementation_tree,
        },
        "source_inventory": {
            "entries": [entry.to_json() for entry in snapshot.source_entries],
            "selection": "o008a/committed-core-policy-cargo/v1",
        },
        "plan": {
            "exact_o008a_row": snapshot.exact_plan_row,
            "path": PLAN_PATH_V1,
        },
        "toolchain": {
            "dependency_policy_audit": snapshot.dependency_policy_report,
            "legacy_lock_versions": list(snapshot.legacy_lock_versions),
            "legacy_manifest_risc0_requirements": list(snapshot.legacy_manifest_requirements),
            "required_risc0_requirement": REQUIRED_RISC0_REQUIREMENT_V1,
            "required_risc0_version": REQUIRED_RISC0_VERSION_V1,
            "required_version_source_observed": snapshot.required_version_source,
        },
        "resource_preflight": _resource_projection_v1(toolchain_status, resource),
        "execution": {
            "clean_build_receipt": "NOT_REQUESTED_BY_PREFLIGHT",
            "network": "NETWORK_NOT_REQUESTED",
            "risc0_image_rebuild": "NOT_REQUESTED_BY_PREFLIGHT",
            "rust_build": "NOT_REQUESTED_BY_PREFLIGHT",
        },
        "trust_nonclaims": {
            "executable_trust": "NOT_CLAIMED",
            "git_object_store_trust": "NOT_CLAIMED",
            "immutable_checker_bootstrap": _immutable_bootstrap_nonclaim_v1(),
            "python_interpreter_trust": "NOT_CLAIMED",
        },
        "claim_scope": _claim_scope_v1(),
    }
    return with_artifact_payload_digest_v1(artifact)


def build_stale_placeholder_artifact_v1(
    *,
    base_commit: str,
    observed_head: str | None,
    rejection_code: str,
) -> dict[str, object]:
    """Render a conspicuous placeholder when C and E cannot yet exist."""

    artifact: dict[str, object] = {
        "schema": SCHEMA_V1,
        "version": 1,
        "canonical_encoding": CANONICAL_ENCODING_V1,
        "artifact_state": "STALE_UNTRUSTED_IMPLEMENTATION_AND_ARTIFACT_COMMITS_REQUIRED",
        "result": {
            "blocked": True,
            "build_host_qualification_gap_closed": False,
            "qualification_eligible": False,
            "status": "BLOCKED_IMPLEMENTATION_COMMIT_REQUIRED",
        },
        "replay": {
            "artifact_commit_oid": "ABSENT",
            "base_commit": base_commit,
            "implementation_commit": None,
            "implementation_tree": None,
            "observed_head": observed_head,
        },
        "generation_rejection": {"code": rejection_code},
        "execution": {"network": "NETWORK_NOT_REQUESTED"},
        "trust_nonclaims": {
            "executable_trust": "NOT_CLAIMED",
            "git_object_store_trust": "NOT_CLAIMED",
            "immutable_checker_bootstrap": _immutable_bootstrap_nonclaim_v1(),
            "python_interpreter_trust": "NOT_CLAIMED",
        },
        "claim_scope": _claim_scope_v1(),
    }
    return with_artifact_payload_digest_v1(artifact)


def replay_binding_from_artifact_v1(
    artifact: object,
    *,
    expected_parent: str = EXPECTED_PARENT_SHA256_V1,
) -> tuple[str, str, str]:
    """Extract the minimal binding needed to locate C from an E blob."""

    if type(artifact) is not dict:
        _reject("ARTIFACT_ROOT_TYPE", "artifact", "artifact must be an exact object")
    if artifact.get("schema") != SCHEMA_V1 or artifact.get("version") != 1:
        _reject("ARTIFACT_SCHEMA", "artifact", "schema or version mismatch")
    replay = artifact.get("replay")
    if type(replay) is not dict:
        _reject("ARTIFACT_REPLAY", "artifact.replay", "replay binding must be an exact object")
    base_commit = replay.get("base_commit")
    implementation_commit = replay.get("implementation_commit")
    implementation_tree = replay.get("implementation_tree")
    if replay.get("artifact_commit_oid") != "CHECKER_DERIVED_FROM_EXACT_HEAD_E":
        _reject("ARTIFACT_EVIDENCE_SCOPE", "artifact.replay.artifact_commit_oid", "exact E marker required")
    if replay.get("verification_scope") != EXACT_EVIDENCE_REPLAY_SCOPE_V1:
        _reject("ARTIFACT_EVIDENCE_SCOPE", "artifact.replay.verification_scope", "descendant replay is forbidden")
    if base_commit != expected_parent:
        _reject("ARTIFACT_PARENT_BINDING", "artifact.replay.base_commit", "base commit mismatch")
    if not is_git_oid_v1(implementation_commit):
        _reject("ARTIFACT_IMPLEMENTATION_COMMIT", "artifact.replay.implementation_commit", "invalid Git OID")
    if not is_git_oid_v1(implementation_tree):
        _reject("ARTIFACT_IMPLEMENTATION_TREE", "artifact.replay.implementation_tree", "invalid Git OID")
    digest = artifact.get("artifact_payload_sha256")
    if not is_sha256_v1(digest):
        _reject("ARTIFACT_PAYLOAD_DIGEST", "artifact.artifact_payload_sha256", "invalid SHA-256")
    payload = {key: value for key, value in artifact.items() if key != "artifact_payload_sha256"}
    if digest != sha256_prefixed_v1(canonical_json_bytes_v1(payload)):
        _reject("ARTIFACT_PAYLOAD_DIGEST", "artifact.artifact_payload_sha256", "payload digest mismatch")
    return cast(str, base_commit), cast(str, implementation_commit), cast(str, implementation_tree)


def blocked_check_report_v1(
    *,
    status: str,
    artifact_valid: bool,
    findings: list[dict[str, str]],
) -> dict[str, object]:
    """Render a stable report that never promotes a qualification claim."""

    return {
        "schema": CHECK_SCHEMA_V1,
        "ok": False,
        "artifact_valid": artifact_valid,
        "qualification_eligible": False,
        "status": status,
        "findings": findings,
        "replay_scope": EXACT_EVIDENCE_REPLAY_SCOPE_V1,
        "trust_nonclaims": {
            "immutable_checker_bootstrap": _immutable_bootstrap_nonclaim_v1(),
            "python_interpreter_trust": "NOT_CLAIMED",
        },
        "claim_scope": _claim_scope_v1(),
    }
