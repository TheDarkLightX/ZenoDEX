"""Deterministic, authority-NONE O-008A dependency-resolution admission."""

from __future__ import annotations

import hashlib
import json
import stat
import subprocess
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NoReturn

SCHEMA = "zenodex/o008a-dependency-resolution-admission/v2"
CHECK_SCHEMA = "zenodex/o008a-dependency-resolution-admission-check/v2"
STATUS = "ADMITTED_SOURCE_PINNED_DEPENDENCY_RESOLUTION_RESEARCH_EXECUTION"
BASE_COMMIT = "74c09f2a83dd8ea11e89bd4f3c8a5ed17ec96931"

PLAN_PATH = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
ADMISSION_PATH = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
REGISTRY_PATH = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
BLOCKER_PATH = "docs/research/ZENODEX_O008A_DEPENDENCY_POLICY_BLOCKER_V1.json"
ARTIFACT_PATH = "docs/research/ZENODEX_O008A_DEPENDENCY_RESOLUTION_ADMISSION_V2.json"
MODEL_PATH = "tools/o008a_dependency_resolution_admission_v2.py"
BUILDER_PATH = "tools/build_o008a_dependency_resolution_admission_v2.py"
CHECKER_PATH = "tools/check_o008a_dependency_resolution_admission_v2.py"
TEST_PATH = "tests/test_check_o008a_dependency_resolution_admission_v2.py"
HYGIENE_PATH = (
    "tests/evidence/test_hygiene/"
    "THV1-20260831-o008a-dependency-resolution-admission-v2.json"
)

STAGE_A_PATHS = tuple(
    sorted((MODEL_PATH, BUILDER_PATH, CHECKER_PATH, TEST_PATH, HYGIENE_PATH))
)
PROTECTED_PATHS = (PLAN_PATH, ADMISSION_PATH, REGISTRY_PATH, BLOCKER_PATH)
SOURCE_PATHS = tuple(sorted((*STAGE_A_PATHS, *PROTECTED_PATHS)))
MAX_BYTES = 2 * 1024 * 1024

PROTECTED_SHA256 = {
    PLAN_PATH: "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f",
    ADMISSION_PATH: "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d",
    REGISTRY_PATH: "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4",
    BLOCKER_PATH: "adea8492d5aa6f3369b202217f7b1baeb0961e3bf07b46594af0620e22cf2bfe",
}
PLAN_COMMIT = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
ADMISSION_COMMIT = "c0fb36c62b20293ebc54fc530f3dfe2e8046576d"
BLOCKER_STAGE_B_COMMIT = "4cbe500f4c7fb38202c9d39ac21efc0340cde20b"

EXACT_PLAN_ROW = {
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
SELECTED_BLOCKER_OPTION = {
    "id": "SOURCE_PINNED_PATCH_OR_FORK",
    "preferred": False,
    "authorization": "NOT_GRANTED_BY_PACKET",
    "requirements": [
        "review and hash-pin a rzup patch that removes or replaces rsa",
        "review and hash-pin the ark-relations or RISC0 closure change",
        "run dependency approval and full image rebuild review",
    ],
}
DIRECTIVE_PREMISE = {
    "classification": "EXTERNAL_USER_DIRECTIVE_NOT_MACHINE_VERIFIED",
    "recorded_date": "2026-08-31",
    "scope": (
        "O-008A_DEPENDENCY_RESOLUTION_OPTION_AND_ROOT_BACKED_LOCAL_RESEARCH_EXECUTION"
    ),
}
SELECTION = {
    "selected_resolution_option": "SOURCE_PINNED_PATCH_OR_FORK",
    "selection_status": "SELECTED_FOR_BOUNDED_RESEARCH_IMPLEMENTATION",
    "prior_blocker_option_authorization": "NOT_GRANTED_BY_PACKET",
    "supplemental_admission_effect": (
        "SELECT_OPTION_AND_AUTHORIZE_CONTROLLED_LOCAL_EXECUTION_ONLY"
    ),
}
EXECUTION_ADMISSION = {
    "status": "AUTHORIZED_WITH_EXACT_CONTROLS",
    "authorized_operations": [
        "LOCAL_SOURCE_PINNED_PATCH_OR_FORK_PREPARATION",
        "LOCAL_ISOLATED_CARGO_EXECUTION",
        "LOCAL_ISOLATED_RISC0_EXECUTION",
    ],
    "controls": {
        "build_storage": {
            "crucial_volume_use_authorized": False,
            "dev_shm_build_output_allowed": False,
            "removable_or_recovery_evidence_volume_use_authorized": False,
            "repository_worktree_allowed_as_build_output": False,
            "required_class": "ROOT_FILESYSTEM_BACKED_ISOLATED_DIRECTORY",
            "required_mountpoint": "/",
        },
        "cargo_home": "BENEATH_ISOLATED_ROOT_BACKED_BUILD_ROOT",
        "cargo_target_dir": "BENEATH_ISOLATED_ROOT_BACKED_BUILD_ROOT",
        "concurrency": "ONE_BUILD_AT_A_TIME",
        "isolated_worktree_required": True,
        "network_access_authorized": False,
        "preflight": {
            "fail_closed_if_any_threshold_unmet": True,
            "maximum_declared_build_budget_bytes": 8 * 1024**3,
            "measurement_required_immediately_before_each_run": True,
            "minimum_available_memory_bytes": 12 * 1024**3,
            "minimum_projected_root_free_bytes_after_build": 12 * 1024**3,
            "minimum_root_free_bytes": 20 * 1024**3,
            "minimum_root_free_inodes": 1_000_000,
        },
        "source_and_lock_pins_required_before_evidence_promotion": True,
        "tmpdir": "BENEATH_ISOLATED_ROOT_BACKED_BUILD_ROOT",
    },
    "required_before_qualification": [
        "review and hash-pin the exact dependency patch or fork",
        "produce a clean locked dependency audit",
        "perform two clean isolated build runs in independent targets",
        "regenerate and replay every affected RISC0 image and receipt",
        "record exact source, lock, toolchain, image, receipt, and artifact hashes",
    ],
}
RESOURCE_OBSERVATION = {
    "captured_date": "2026-08-31",
    "classification": "VOLATILE_SINGLE_HOST_OBSERVATION_REQUIRES_FRESH_PREFLIGHT",
    "observed_dev_shm_free_bytes": 7_459_278_848,
    "observed_root_free_bytes": 22_578_712_576,
    "storage_ordering": "ROOT_FREE_BYTES_GREATER_THAN_DEV_SHM_FREE_BYTES",
}
SUPERSEDED_CANDIDATE = {
    "adjudication": "REJECTED_BEFORE_INTEGRATION",
    "artifact_sha256": "307efbb795c2f1cd76a983e4a351d48f4bb5601c488e377abe46fe130c400b6d",
    "reason_code": "STALE_TMPFS_BUILD_STORAGE_SELECTION",
    "stage_a_commit": "40e0aa94a8f3c1a3da79b3e556f26d04526ec03f",
    "stage_b_commit": "c13f2980f5e72401f96f14ea95cc21b5688743c4",
}
NO_AUTHORITY = {
    "build_host_authority": "NONE",
    "migration_authority": "NONE",
    "production_authority": "NONE",
    "release_authority": "NONE",
    "settlement_authority": "NONE",
    "value_movement_authority": "NONE",
    "verifier_authority": "NONE",
}
CLAIM_CEILING = {
    "authority": NO_AUTHORITY,
    "build_host_qualification_gap_closed": False,
    "build_host_qualified": False,
    "clean_build_receipt": "MISSING",
    "dependency_patch_or_fork_validated": False,
    "dependency_policy_conflict_resolved": False,
    "dependency_safe": False,
    "local_isolated_execution_scope_admitted": True,
    "o008a_complete": False,
    "proof_validity": "NOT_CLAIMED",
    "qualification_complete": False,
    "release_ready": False,
    "resolution_option_selected": True,
    "risc0_3_0_6_image_rebuild_receipt": "MISSING",
    "storage_policy_corrected_from_unintegrated_candidate": True,
}
NONCLAIMS = [
    "The directive premise is external and is not machine verified by this packet.",
    "This packet selects a research resolution path; it does not validate any future patch or fork bytes.",
    "No Cargo command, RISC0 command, network request, build, image rebuild, or proof verification was run to create this packet.",
    "The historical blocker remains valid evidence of the unresolved dependency conflict; this packet supplies only the later bounded selection and execution admission.",
    "The recorded free-space values are a volatile comparison basis; every execution requires a fresh fail-closed resource preflight.",
    "No build output, Cargo home, or temporary build data is authorized on /dev/shm, any Crucial volume, or any removable or recovery-evidence volume.",
    "This packet does not complete O-008A or qualify a build host.",
    "No dependency-safety, proof-validity, release, production, verifier, settlement, migration, or value-movement authority is granted.",
]


@dataclass(frozen=True, slots=True)
class AdmissionReject(ValueError):
    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise AdmissionReject(code, path, detail)


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8") + b"\n"


def sha256_hex(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _reject("JSON_DUPLICATE_KEY", key, "duplicate object key")
        result[key] = value
    return result


def decode_json(raw: bytes, path: str) -> dict[str, Any]:
    if len(raw) > MAX_BYTES:
        _reject("INPUT_SIZE", path, "input exceeds byte limit")
    try:
        value = json.loads(raw, object_pairs_hook=_strict_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("JSON_DECODE", path, type(exc).__name__)
    if type(value) is not dict:
        _reject("JSON_SHAPE", path, "top-level object required")
    return value


def _git(root: Path, *arguments: str) -> bytes:
    result = subprocess.run(
        (
            "git",
            "-c",
            "core.fsmonitor=false",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.attributesFile=/dev/null",
            "-C",
            str(root),
            *arguments,
        ),
        check=False,
        capture_output=True,
        env={
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_OPTIONAL_LOCKS": "0",
            "HOME": "/nonexistent",
            "LANG": "C",
            "LC_ALL": "C",
            "PATH": "/usr/bin:/bin",
        },
    )
    if result.returncode != 0 or result.stderr:
        _reject("GIT_COMMAND", "git", f"{arguments[0]} failed")
    return result.stdout


def _oid(raw: bytes, path: str) -> str:
    value = raw.decode("ascii").strip()
    if len(value) != 40 or any(ch not in "0123456789abcdef" for ch in value):
        _reject("GIT_OID", path, "full lowercase SHA-1 required")
    return value


def git_head(root: Path) -> str:
    return _oid(_git(root, "rev-parse", "--verify", "HEAD^{commit}"), "HEAD")


def _parents(root: Path, commit: str) -> tuple[str, ...]:
    raw = _git(root, "show", "-s", "--format=%P", commit).decode("ascii").strip()
    return tuple(raw.split()) if raw else ()


def _changes(root: Path, parent: str, child: str) -> tuple[tuple[str, str], ...]:
    fields = _git(
        root,
        "diff-tree",
        "--no-commit-id",
        "--no-renames",
        "--name-status",
        "-r",
        "-z",
        parent,
        child,
    ).split(b"\0")
    if fields and fields[-1] == b"":
        fields.pop()
    if len(fields) % 2:
        _reject("GIT_DIFF", child, "unexpected name-status encoding")
    rows: list[tuple[str, str]] = []
    for index in range(0, len(fields), 2):
        status = fields[index].decode("ascii")
        path = fields[index + 1].decode("utf-8")
        if status not in {"A", "D", "M", "T"}:
            _reject("GIT_DIFF", path, f"unsupported status {status}")
        rows.append((status, path))
    return tuple(sorted(rows, key=lambda row: row[1]))


def _tree_entry(root: Path, commit: str, path: str) -> tuple[str, str, str]:
    rows = [
        row
        for row in _git(root, "ls-tree", "-z", commit, "--", path).split(b"\0")
        if row
    ]
    if len(rows) != 1:
        _reject("GIT_ENTRY", path, "exactly one Git entry required")
    meta, separator, encoded_path = rows[0].partition(b"\t")
    if not separator or encoded_path.decode("utf-8") != path:
        _reject("GIT_ENTRY", path, "exact path required")
    mode, kind, oid = meta.decode("ascii").split()
    return mode, kind, oid


def _blob(root: Path, commit: str, path: str) -> tuple[str, bytes]:
    mode, kind, oid = _tree_entry(root, commit, path)
    if mode != "100644" or kind != "blob":
        _reject("GIT_MODE", path, "regular mode 100644 blob required")
    size = int(_git(root, "cat-file", "-s", oid).decode("ascii"))
    if size > MAX_BYTES:
        _reject("SOURCE_SIZE", path, "source exceeds byte limit")
    raw = _git(root, "cat-file", "blob", oid)
    if len(raw) != size:
        _reject("GIT_BLOB", path, "blob size changed")
    return oid, raw


def _source_pin(root: Path, commit: str, path: str) -> dict[str, object]:
    oid, raw = _blob(root, commit, path)
    return {
        "git_blob_sha": oid,
        "git_mode": "100644",
        "path": path,
        "sha256": sha256_hex(raw),
        "size_bytes": len(raw),
    }


def _working_bytes(root: Path, path: str) -> bytes:
    target = root / path
    try:
        metadata = target.lstat()
    except OSError as exc:
        _reject("WORKTREE_SOURCE", path, type(exc).__name__)
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > MAX_BYTES:
        _reject("WORKTREE_SOURCE", path, "bounded regular file required")
    try:
        raw = target.read_bytes()
    except OSError as exc:
        _reject("WORKTREE_SOURCE", path, type(exc).__name__)
    if len(raw) != metadata.st_size:
        _reject("WORKTREE_SOURCE", path, "size changed during read")
    return raw


def _find_o008a(plan: dict[str, Any]) -> dict[str, Any]:
    matches: list[dict[str, Any]] = []

    def visit(value: object) -> None:
        if type(value) is dict:
            row = value
            if row.get("obligation_id") == "O-008A":
                matches.append(row)
            for nested in row.values():
                visit(nested)
        elif type(value) is list:
            for nested in value:
                visit(nested)

    visit(plan)
    if len(matches) != 1 or matches[0] != EXACT_PLAN_ROW:
        _reject("SUBJECT_BINDING", PLAN_PATH, "exact O-008A row required")
    return matches[0]


def _governed_subjects(root: Path, stage_a: str) -> dict[str, Any]:
    documents: dict[str, dict[str, Any]] = {}
    for path in PROTECTED_PATHS:
        _oid_value, raw = _blob(root, stage_a, path)
        if sha256_hex(raw) != PROTECTED_SHA256[path]:
            _reject("SUBJECT_BINDING", path, "protected artifact digest drift")
        documents[path] = decode_json(raw, path)

    plan = documents[PLAN_PATH]
    admission = documents[ADMISSION_PATH]
    registry = documents[REGISTRY_PATH]
    blocker = documents[BLOCKER_PATH]
    _find_o008a(plan)

    prior_selection = admission.get("selection_premise")
    if prior_selection != {
        "authority": "NONE",
        "classification": "EXTERNAL_USER_DIRECTIVE_NOT_MACHINE_VERIFIED",
        "scope": "RESEARCH_IMPLEMENTATION_COORDINATION_ONLY",
        "selected_plan_commit": PLAN_COMMIT,
    }:
        _reject("SUBJECT_BINDING", ADMISSION_PATH, "admission premise drift")
    admitted_plan = admission.get("admitted_plan")
    if (
        type(admitted_plan) is not dict
        or admitted_plan.get("commit") != PLAN_COMMIT
        or admitted_plan.get("plan_sha256") != PROTECTED_SHA256[PLAN_PATH]
    ):
        _reject("SUBJECT_BINDING", ADMISSION_PATH, "admitted plan drift")
    active_plans = registry.get("active_plans")
    if (
        registry.get("active_plan_count") != 1
        or type(active_plans) is not list
        or len(active_plans) != 1
        or type(active_plans[0]) is not dict
        or active_plans[0].get("plan_commit") != PLAN_COMMIT
        or active_plans[0].get("plan_sha256") != PROTECTED_SHA256[PLAN_PATH]
    ):
        _reject("SUBJECT_BINDING", REGISTRY_PATH, "active plan drift")
    options = blocker.get("governed_resolution_options")
    selected = (
        [row for row in options if type(row) is dict and row.get("id") == SELECTION["selected_resolution_option"]]
        if type(options) is list
        else []
    )
    if (
        blocker.get("schema") != "zenodex/o008a-dependency-policy-blocker/v1"
        or blocker.get("status") != "BLOCKED_DEPENDENCY_POLICY_CONFLICT"
        or selected != [SELECTED_BLOCKER_OPTION]
    ):
        _reject("SUBJECT_BINDING", BLOCKER_PATH, "exact blocker option required")

    return {
        "active_plan_registry": {
            "path": REGISTRY_PATH,
            "sha256": PROTECTED_SHA256[REGISTRY_PATH],
            "status": "RESEARCH_ONLY",
        },
        "dependency_policy_blocker": {
            "path": BLOCKER_PATH,
            "sha256": PROTECTED_SHA256[BLOCKER_PATH],
            "stage_b_commit": BLOCKER_STAGE_B_COMMIT,
            "status": "BLOCKED_DEPENDENCY_POLICY_CONFLICT",
        },
        "plan": {
            "commit": PLAN_COMMIT,
            "exact_o008a_row": deepcopy(EXACT_PLAN_ROW),
            "path": PLAN_PATH,
            "sha256": PROTECTED_SHA256[PLAN_PATH],
        },
        "plan_admission": {
            "commit": ADMISSION_COMMIT,
            "path": ADMISSION_PATH,
            "sha256": PROTECTED_SHA256[ADMISSION_PATH],
        },
    }


def _expected_subjects() -> dict[str, Any]:
    return {
        "active_plan_registry": {
            "path": REGISTRY_PATH,
            "sha256": PROTECTED_SHA256[REGISTRY_PATH],
            "status": "RESEARCH_ONLY",
        },
        "dependency_policy_blocker": {
            "path": BLOCKER_PATH,
            "sha256": PROTECTED_SHA256[BLOCKER_PATH],
            "stage_b_commit": BLOCKER_STAGE_B_COMMIT,
            "status": "BLOCKED_DEPENDENCY_POLICY_CONFLICT",
        },
        "plan": {
            "commit": PLAN_COMMIT,
            "exact_o008a_row": EXACT_PLAN_ROW,
            "path": PLAN_PATH,
            "sha256": PROTECTED_SHA256[PLAN_PATH],
        },
        "plan_admission": {
            "commit": ADMISSION_COMMIT,
            "path": ADMISSION_PATH,
            "sha256": PROTECTED_SHA256[ADMISSION_PATH],
        },
    }


def _certificate_payload(artifact: dict[str, Any]) -> dict[str, Any]:
    return {
        key: artifact[key]
        for key in (
            "schema",
            "status",
            "implementation_subject",
            "governed_subjects",
            "directive_premise",
            "resolution_selection",
            "execution_admission",
            "resource_observation",
            "superseded_candidate",
            "claim_ceiling",
            "source_binding",
        )
    }


def validate_semantics(artifact: dict[str, Any]) -> None:
    if artifact.get("schema") != SCHEMA or artifact.get("status") != STATUS:
        _reject("STATUS", "status", "exact schema and status required")
    if artifact.get("directive_premise") != DIRECTIVE_PREMISE:
        _reject("DIRECTIVE_PREMISE", "directive_premise", "exact external premise required")
    if artifact.get("governed_subjects") != _expected_subjects():
        _reject("SUBJECT_BINDING", "governed_subjects", "exact governed subjects required")
    if artifact.get("resolution_selection") != SELECTION:
        _reject("RESOLUTION_OPTION", "resolution_selection", "exact selected option required")
    if artifact.get("execution_admission") != EXECUTION_ADMISSION:
        _reject("EXECUTION_SCOPE", "execution_admission", "exact bounded execution scope required")
    if artifact.get("resource_observation") != RESOURCE_OBSERVATION:
        _reject("RESOURCE_OBSERVATION", "resource_observation", "exact volatile observation required")
    if artifact.get("superseded_candidate") != SUPERSEDED_CANDIDATE:
        _reject("SUPERSESSION", "superseded_candidate", "exact rejected predecessor required")
    claims = artifact.get("claim_ceiling")
    if type(claims) is not dict or claims.get("authority") != NO_AUTHORITY:
        _reject("AUTHORITY_PROMOTION", "claim_ceiling.authority", "all authority must be NONE")
    if claims != CLAIM_CEILING:
        _reject("CLAIM_PROMOTION", "claim_ceiling", "exact conservative ceiling required")
    if artifact.get("nonclaims") != NONCLAIMS:
        _reject("NONCLAIM_DRIFT", "nonclaims", "exact nonclaims required")
    subject = artifact.get("implementation_subject")
    if (
        type(subject) is not dict
        or set(subject) != {"base_commit", "stage_a_commit", "stage_a_tree"}
        or subject.get("base_commit") != BASE_COMMIT
    ):
        _reject("SUBJECT_BINDING", "implementation_subject", "exact Stage A subject required")
    for key in ("stage_a_commit", "stage_a_tree"):
        value = subject.get(key)
        if type(value) is not str or len(value) != 40 or any(
            character not in "0123456789abcdef" for character in value
        ):
            _reject("SUBJECT_BINDING", f"implementation_subject.{key}", "full Git OID required")
    binding = artifact.get("source_binding")
    if type(binding) is not dict or set(binding) != {"selection", "source_manifest"}:
        _reject("SOURCE_BINDING", "source_binding", "closed source binding required")
    if binding.get("selection") != "EXACT_STAGE_A_AND_PROTECTED_GOVERNANCE_BLOBS":
        _reject("SOURCE_BINDING", "source_binding.selection", "exact selection required")
    manifest = binding.get("source_manifest")
    if type(manifest) is not list or [row.get("path") for row in manifest if type(row) is dict] != list(SOURCE_PATHS):
        _reject("SOURCE_BINDING", "source_binding.source_manifest", "exact sorted path set required")


def build_artifact(root: Path, stage_a: str) -> dict[str, Any]:
    if _parents(root, stage_a) != (BASE_COMMIT,):
        _reject("STAGE_A_PARENT", stage_a, "exact admitted base parent required")
    expected_delta = tuple(("A", path) for path in STAGE_A_PATHS)
    if _changes(root, BASE_COMMIT, stage_a) != expected_delta:
        _reject("STAGE_A_DELTA", stage_a, "Stage A must add only the five admission sources")
    tree = _oid(_git(root, "show", "-s", "--format=%T", stage_a), stage_a)
    core: dict[str, Any] = {
        "schema": SCHEMA,
        "status": STATUS,
        "implementation_subject": {
            "base_commit": BASE_COMMIT,
            "stage_a_commit": stage_a,
            "stage_a_tree": tree,
        },
        "governed_subjects": _governed_subjects(root, stage_a),
        "directive_premise": deepcopy(DIRECTIVE_PREMISE),
        "resolution_selection": deepcopy(SELECTION),
        "execution_admission": deepcopy(EXECUTION_ADMISSION),
        "resource_observation": deepcopy(RESOURCE_OBSERVATION),
        "superseded_candidate": deepcopy(SUPERSEDED_CANDIDATE),
        "claim_ceiling": deepcopy(CLAIM_CEILING),
        "source_binding": {
            "selection": "EXACT_STAGE_A_AND_PROTECTED_GOVERNANCE_BLOBS",
            "source_manifest": [_source_pin(root, stage_a, path) for path in SOURCE_PATHS],
        },
        "nonclaims": list(NONCLAIMS),
    }
    core["certificate_root"] = sha256_hex(canonical_json_bytes(_certificate_payload(core)))
    core["artifact_payload_sha256"] = sha256_hex(canonical_json_bytes(core))
    validate_semantics(core)
    return core


def artifact_bytes(root: Path, stage_a: str) -> bytes:
    return canonical_json_bytes(build_artifact(root, stage_a))


def validate_artifact_bytes(raw: bytes, expected: bytes) -> dict[str, Any]:
    artifact = decode_json(raw, ARTIFACT_PATH)
    if canonical_json_bytes(artifact) != raw:
        _reject("NONCANONICAL_ARTIFACT", ARTIFACT_PATH, "canonical JSON required")
    validate_semantics(artifact)
    recorded_root = artifact.get("certificate_root")
    if recorded_root != sha256_hex(canonical_json_bytes(_certificate_payload(artifact))):
        _reject("CERTIFICATE_ROOT", ARTIFACT_PATH, "certificate root mismatch")
    payload = dict(artifact)
    recorded_payload = payload.pop("artifact_payload_sha256", None)
    if recorded_payload != sha256_hex(canonical_json_bytes(payload)):
        _reject("ARTIFACT_PAYLOAD_HASH", ARTIFACT_PATH, "payload digest mismatch")
    if raw != expected:
        _reject("ARTIFACT_PROJECTION_DRIFT", ARTIFACT_PATH, "artifact differs from Stage A projection")
    return artifact


def check_admission(root: Path) -> dict[str, Any]:
    stage_a: str | None = None
    stage_b: str | None = None
    historical_valid = False
    try:
        root = root.resolve(strict=True)
        head = git_head(root)
        touches = [
            _oid(line, ARTIFACT_PATH)
            for line in _git(root, "rev-list", head, "--", ARTIFACT_PATH).splitlines()
            if line
        ]
        if len(touches) != 1:
            _reject("ARTIFACT_HISTORY", ARTIFACT_PATH, "exactly one artifact commit required")
        stage_b = touches[0]
        parents = _parents(root, stage_b)
        if len(parents) != 1:
            _reject("STAGE_B_PARENT", stage_b, "one direct Stage A parent required")
        stage_a = parents[0]
        if _changes(root, stage_a, stage_b) != (("A", ARTIFACT_PATH),):
            _reject("STAGE_B_DELTA", stage_b, "Stage B may add only the artifact")
        _git(root, "merge-base", "--is-ancestor", stage_b, head)
        artifact_oid, committed = _blob(root, stage_b, ARTIFACT_PATH)
        expected = artifact_bytes(root, stage_a)
        artifact = validate_artifact_bytes(committed, expected)
        historical_valid = True
        current_oid, current = _blob(root, head, ARTIFACT_PATH)
        if current_oid != artifact_oid or current != committed:
            _reject("CURRENT_ARTIFACT_DRIFT", ARTIFACT_PATH, "current Git artifact differs from Stage B")
        if _working_bytes(root, ARTIFACT_PATH) != committed:
            _reject("WORKTREE_ARTIFACT_DRIFT", ARTIFACT_PATH, "working artifact differs from Stage B")
        for pin in artifact["source_binding"]["source_manifest"]:
            path = pin["path"]
            current_source_oid, current_source = _blob(root, head, path)
            if (
                current_source_oid != pin["git_blob_sha"]
                or sha256_hex(current_source) != pin["sha256"]
            ):
                _reject("CURRENT_SOURCE_DRIFT", path, "current Git source differs from Stage A")
            if _working_bytes(root, path) != current_source:
                _reject("WORKTREE_SOURCE_DRIFT", path, "working source differs from Stage A")
        return {
            "artifact_payload_sha256": artifact["artifact_payload_sha256"],
            "artifact_sha256": sha256_hex(committed),
            "authority": deepcopy(NO_AUTHORITY),
            "build_storage_class": "ROOT_FILESYSTEM_BACKED_ISOLATED_DIRECTORY",
            "certificate_root": artifact["certificate_root"],
            "crucial_volume_use_authorized": False,
            "current_applicable": True,
            "dev_shm_build_output_allowed": False,
            "finding": None,
            "historical_valid": True,
            "local_isolated_execution_scope_admitted": True,
            "network_access_authorized": False,
            "ok": True,
            "o008a_complete": False,
            "preflight_required": True,
            "schema": CHECK_SCHEMA,
            "selected_resolution_option": "SOURCE_PINNED_PATCH_OR_FORK",
            "stage_a_commit": stage_a,
            "stage_b_commit": stage_b,
            "status": STATUS,
        }
    except (AdmissionReject, OSError) as exc:
        finding = (
            {"code": exc.code, "detail": exc.detail, "path": exc.path}
            if isinstance(exc, AdmissionReject)
            else {"code": "IO_ERROR", "detail": type(exc).__name__, "path": str(root)}
        )
        return {
            "artifact_payload_sha256": None,
            "artifact_sha256": None,
            "authority": deepcopy(NO_AUTHORITY),
            "build_storage_class": "ROOT_FILESYSTEM_BACKED_ISOLATED_DIRECTORY",
            "certificate_root": None,
            "crucial_volume_use_authorized": False,
            "current_applicable": False,
            "dev_shm_build_output_allowed": False,
            "finding": finding,
            "historical_valid": historical_valid,
            "local_isolated_execution_scope_admitted": False,
            "network_access_authorized": False,
            "ok": False,
            "o008a_complete": False,
            "preflight_required": True,
            "schema": CHECK_SCHEMA,
            "selected_resolution_option": "SOURCE_PINNED_PATCH_OR_FORK",
            "stage_a_commit": stage_a,
            "stage_b_commit": stage_b,
            "status": STATUS,
        }
