"""Deterministic, authority-NONE O-008A dependency-policy blocker."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import tomllib
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NoReturn

SCHEMA = "zenodex/o008a-dependency-policy-blocker/v1"
CHECK_SCHEMA = "zenodex/o008a-dependency-policy-blocker-check/v1"
STATUS = "BLOCKED_DEPENDENCY_POLICY_CONFLICT"
BASE_COMMIT = "80dcdd74dc8ba6b814abe2f82671747b99f1c38f"
PLAN_COMMIT = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
ADMISSION_COMMIT = "c0fb36c62b20293ebc54fc530f3dfe2e8046576d"
STALE_CANDIDATE = "202838c8d1d9e868f47cac4c0227544b981813ff"
STALE_CANDIDATE_PARENT = "67acef7e1b640690dc32529c04882042f038ed5e"
ARTIFACT_PATH = "docs/research/ZENODEX_O008A_DEPENDENCY_POLICY_BLOCKER_V1.json"
EVIDENCE_PATH = "docs/research/evidence/ZENODEX_O008A_LOCAL_DEPENDENCY_EVIDENCE_V1.json"
PLAN_PATH = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
ADMISSION_PATH = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
REGISTRY_PATH = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
LOCK_PATH = "zk/economic_initial_state_risc0/Cargo.lock"
TOOLCHAIN_PATH = "zk/economic_initial_state_risc0/rust-toolchain.toml"
METHODS_MANIFEST_PATH = "zk/economic_initial_state_risc0/methods/Cargo.toml"
HOST_MANIFEST_PATH = "zk/economic_initial_state_risc0/host/Cargo.toml"
AUDIT_NOTE_PATH = "docs/DEPENDENCY_AUDIT_2026_04_27.md"
AUDIT_CHECKER_PATH = "tools/check_risc0_dependency_audit.py"
SOURCE_ROOTS = ("zk/economic_initial_state_risc0", "zk/global_settlement_abi_v1")

MODEL_PATH = "tools/o008a_dependency_policy_blocker_v1.py"
CHECKER_PATH = "tools/check_o008a_dependency_policy_blocker_v1.py"
TEST_PATH = "tests/test_check_o008a_dependency_policy_blocker_v1.py"
HYGIENE_PATH = (
    "tests/evidence/test_hygiene/"
    "THV1-20260831-o008a-dependency-policy-blocker-v1.json"
)
STAGE_A_PATHS = tuple(sorted((MODEL_PATH, CHECKER_PATH, TEST_PATH, HYGIENE_PATH, EVIDENCE_PATH)))
STATIC_INPUT_PATHS = tuple(
    sorted(
        (
            *STAGE_A_PATHS,
            PLAN_PATH,
            ADMISSION_PATH,
            REGISTRY_PATH,
            LOCK_PATH,
            TOOLCHAIN_PATH,
            METHODS_MANIFEST_PATH,
            HOST_MANIFEST_PATH,
            AUDIT_NOTE_PATH,
            AUDIT_CHECKER_PATH,
        )
    )
)

NO_AUTHORITY = {
    "build_host_authority": "NONE",
    "migration_authority": "NONE",
    "production_authority": "NONE",
    "release_authority": "NONE",
    "settlement_authority": "NONE",
    "value_movement_authority": "NONE",
    "verifier_authority": "NONE",
}
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
EXPECTED_PACKAGES = {
    "ark-groth16": ("0.5.0", "88f1d0f3a534bb54188b8dcc104307db6c56cdae574ddc3212aec0625740fc7e"),
    "ark-relations": ("0.5.1", "ec46ddc93e7af44bcab5230937635b06fb5744464dd6a7e7b083e80ebd274384"),
    "risc0-build": ("3.0.6", "bd8216cdd9f573808a94769767480b06ad1e74ae60841c9582fdf51b8e29ba53"),
    "risc0-groth16": ("3.0.5", "b0ca702ea7d0162766defe7ed6a79bda4a747ad9e2684000a6edd14df0a6d1f3"),
    "risc0-zkvm": ("3.0.6", "a5d4f24ec767f71a1663a4d24cf9d02b6bfee44c64647cae677227817051007a"),
    "rsa": ("0.9.10", "b8573f03f5883dcaebdfcf4725caa1ecb9c15b2ef50c43a07b816e06799bb12d"),
    "rzup": ("0.5.2", "96909a7ea8fdf7e18da727d7facbc43eea8a4f77635e7ec75a69794dede16fb6"),
    "tracing-subscriber": ("0.2.25", "0e0d2eaa99c3c2e41547cfa109e910a68ea03823cccad4a0525dcbc9b01e8c71"),
}
DEPENDENCY_CHAINS = (
    ("risc0-build", "rzup", "rsa"),
    ("risc0-zkvm", "risc0-groth16", "ark-groth16", "ark-relations", "tracing-subscriber"),
)
MIN_REUSE_TMPFS_BYTES = 4 * 1024**3
MIN_ISOLATED_TMPFS_BYTES = 7 * 1024**3
MIN_AVAILABLE_MEMORY_BYTES = 16 * 1024**3
MAX_BYTES = 2 * 1024 * 1024


@dataclass(frozen=True, slots=True)
class BlockerReject(ValueError):
    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise BlockerReject(code, path, detail)


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
    env = {
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "HOME": os.environ.get("HOME", "/nonexistent"),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
    }
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
        env=env,
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
    rows = []
    for index in range(0, len(fields), 2):
        status = fields[index].decode("ascii")
        path = fields[index + 1].decode("utf-8")
        if status not in {"A", "D", "M", "T"}:
            _reject("GIT_DIFF", path, f"unsupported status {status}")
        rows.append((status, path))
    return tuple(sorted(rows, key=lambda row: row[1]))


def _tree_entry(root: Path, commit: str, path: str) -> tuple[str, str, str]:
    rows = _git(root, "ls-tree", "-z", commit, "--", path).split(b"\0")
    rows = [row for row in rows if row]
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


def _closure(root: Path, commit: str) -> dict[str, object]:
    summaries: list[dict[str, object]] = []
    for source_root in SOURCE_ROOTS:
        mode, kind, tree_oid = _tree_entry(root, commit, source_root)
        if mode != "040000" or kind != "tree":
            _reject("SOURCE_CLOSURE", source_root, "Git tree required")
        raw_rows = _git(root, "ls-tree", "-r", "-z", commit, "--", source_root)
        entries: list[dict[str, object]] = []
        total = 0
        for row in (item for item in raw_rows.split(b"\0") if item):
            meta, separator, encoded_path = row.partition(b"\t")
            if not separator:
                _reject("SOURCE_CLOSURE", source_root, "invalid tree row")
            file_mode, file_kind, blob_oid = meta.decode("ascii").split()
            path = encoded_path.decode("utf-8")
            if file_mode != "100644" or file_kind != "blob":
                _reject("SOURCE_CLOSURE", path, "regular source blob required")
            size = int(_git(root, "cat-file", "-s", blob_oid).decode("ascii"))
            content = _git(root, "cat-file", "blob", blob_oid)
            if len(content) != size:
                _reject("SOURCE_CLOSURE", path, "blob size changed")
            total += size
            entries.append(
                {
                    "git_blob_sha": blob_oid,
                    "git_mode": file_mode,
                    "path": path,
                    "sha256": sha256_hex(content),
                    "size_bytes": size,
                }
            )
        summaries.append(
            {
                "file_count": len(entries),
                "git_tree_sha": tree_oid,
                "manifest_sha256": sha256_hex(canonical_json_bytes(entries)),
                "root": source_root,
                "total_size_bytes": total,
            }
        )
    return {
        "selection": "ALL_REGULAR_TRACKED_FILES_UNDER_GOVERNED_WORKSPACE_AND_PATH_DEPENDENCY",
        "roots": summaries,
    }


def _toml(raw: bytes, path: str) -> dict[str, object]:
    try:
        value = tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        _reject("TOML_DECODE", path, type(exc).__name__)
    return value


def _plan_binding(root: Path, commit: str) -> dict[str, object]:
    _oid_value, raw = _blob(root, commit, PLAN_PATH)
    plan = decode_json(raw, PLAN_PATH)
    obligations = plan.get("next_obligations")
    if type(obligations) is not list:
        _reject("PLAN_SHAPE", PLAN_PATH, "obligations list required")
    matches = [row for row in obligations if type(row) is dict and row.get("obligation_id") == "O-008A"]
    if matches != [EXACT_PLAN_ROW]:
        _reject("PLAN_O008A", PLAN_PATH, "exact admitted O-008A row required")

    _admission_oid, admission_raw = _blob(root, commit, ADMISSION_PATH)
    admission = decode_json(admission_raw, ADMISSION_PATH)
    admitted = admission.get("admitted_plan")
    if type(admitted) is not dict or admitted.get("commit") != PLAN_COMMIT:
        _reject("PLAN_ADMISSION", ADMISSION_PATH, "exact plan commit required")
    if admitted.get("plan_sha256") != sha256_hex(raw):
        _reject("PLAN_ADMISSION", ADMISSION_PATH, "plan digest mismatch")
    if admission.get("status") != "ADMITTED_RESEARCH_IMPLEMENTATION_PLAN":
        _reject("PLAN_ADMISSION", ADMISSION_PATH, "research admission required")

    _registry_oid, registry_raw = _blob(root, commit, REGISTRY_PATH)
    registry = decode_json(registry_raw, REGISTRY_PATH)
    active = registry.get("active_plans")
    if type(active) is not list or len(active) != 1 or type(active[0]) is not dict:
        _reject("PLAN_REGISTRY", REGISTRY_PATH, "one active research plan required")
    if active[0].get("plan_commit") != PLAN_COMMIT or registry.get("status") != "RESEARCH_ONLY":
        _reject("PLAN_REGISTRY", REGISTRY_PATH, "exact research-only plan required")
    return {
        "admission_commit": ADMISSION_COMMIT,
        "admission_path": ADMISSION_PATH,
        "admission_sha256": sha256_hex(admission_raw),
        "exact_o008a_row": deepcopy(EXACT_PLAN_ROW),
        "plan_commit": PLAN_COMMIT,
        "plan_path": PLAN_PATH,
        "plan_sha256": sha256_hex(raw),
        "registry_path": REGISTRY_PATH,
        "registry_sha256": sha256_hex(registry_raw),
    }


def _package_rows(lock: dict[str, Any]) -> list[dict[str, Any]]:
    packages = lock.get("package")
    if type(packages) is not list:
        _reject("LOCK_SHAPE", LOCK_PATH, "package list required")
    result: list[dict[str, Any]] = []
    for name, (version, checksum) in sorted(EXPECTED_PACKAGES.items()):
        matches = [
            row
            for row in packages
            if type(row) is dict and row.get("name") == name and row.get("version") == version
        ]
        if len(matches) != 1 or matches[0].get("checksum") != checksum:
            _reject("LOCK_PACKAGE", name, "exact locked package required")
        dependencies = matches[0].get("dependencies", [])
        if type(dependencies) is not list or any(type(item) is not str for item in dependencies):
            _reject("LOCK_PACKAGE", name, "dependency list required")
        result.append(
            {
                "checksum": checksum,
                "dependencies": sorted(item.split()[0] for item in dependencies),
                "package": name,
                "version": version,
            }
        )
    by_name = {row["package"]: row for row in result}
    for chain in DEPENDENCY_CHAINS:
        for parent, child in zip(chain[:-1], chain[1:], strict=True):
            if child not in by_name[parent]["dependencies"]:
                _reject("LOCK_CHAIN", parent, f"missing {child}")
    return result


def _dependency_policy(root: Path, commit: str) -> dict[str, object]:
    _lock_oid, lock_raw = _blob(root, commit, LOCK_PATH)
    packages = _package_rows(_toml(lock_raw, LOCK_PATH))
    _toolchain_oid, toolchain_raw = _blob(root, commit, TOOLCHAIN_PATH)
    toolchain = _toml(toolchain_raw, TOOLCHAIN_PATH).get("toolchain")
    if type(toolchain) is not dict or toolchain.get("channel") != "1.90.0":
        _reject("TOOLCHAIN_LOCK", TOOLCHAIN_PATH, "Rust 1.90.0 required")
    _methods_oid, methods_raw = _blob(root, commit, METHODS_MANIFEST_PATH)
    methods = _toml(methods_raw, METHODS_MANIFEST_PATH).get("build-dependencies")
    if type(methods) is not dict or methods.get("risc0-build") != "=3.0.6":
        _reject("RISC0_PIN", METHODS_MANIFEST_PATH, "risc0-build =3.0.6 required")
    _host_oid, host_raw = _blob(root, commit, HOST_MANIFEST_PATH)
    host = _toml(host_raw, HOST_MANIFEST_PATH).get("dependencies")
    if type(host) is not dict or type(host.get("risc0-zkvm")) is not dict:
        _reject("RISC0_PIN", HOST_MANIFEST_PATH, "risc0-zkvm dependency required")
    if host["risc0-zkvm"].get("version") != "=3.0.6":
        _reject("RISC0_PIN", HOST_MANIFEST_PATH, "risc0-zkvm =3.0.6 required")

    _evidence_oid, evidence_raw = _blob(root, commit, EVIDENCE_PATH)
    evidence = decode_json(evidence_raw, EVIDENCE_PATH)
    database = evidence.get("rustsec_database")
    if type(database) is not dict or type(database.get("records")) is not list:
        _reject("ADVISORY_EVIDENCE", EVIDENCE_PATH, "RustSec records required")
    records = database["records"]
    expected_advisories = {
        "RUSTSEC-2023-0071": ("rsa", []),
        "RUSTSEC-2025-0055": ("tracing-subscriber", [">=0.3.20"]),
    }
    if {row.get("id") for row in records if type(row) is dict} != set(expected_advisories):
        _reject("ADVISORY_SET", EVIDENCE_PATH, "both exact RustSec IDs required")
    advisory_rows: list[dict[str, Any]] = []
    for advisory_id, (package, patched) in expected_advisories.items():
        row = next(item for item in records if item.get("id") == advisory_id)
        if row.get("package") != package or row.get("patched_versions") != patched:
            _reject("ADVISORY_FACT", advisory_id, "package or patched versions drift")
        advisory_rows.append(
            {
                "advisory_id": advisory_id,
                "locked_package": package,
                "locked_version": EXPECTED_PACKAGES[package][0],
                "patched_versions": patched,
                "record_sha256": row.get("record_sha256"),
                "resolution_fact": (
                    "NO_PATCHED_VERSION_LISTED"
                    if advisory_id == "RUSTSEC-2023-0071"
                    else "PATCH_REQUIRES_TRACING_SUBSCRIBER_AT_LEAST_0_3_20"
                ),
            }
        )
    manifests = evidence.get("locally_cached_crate_manifests")
    if type(manifests) is not list or len(manifests) != 3:
        _reject("MANIFEST_EVIDENCE", EVIDENCE_PATH, "three exact crate manifests required")
    manifest_by_package = {row.get("package"): row for row in manifests if type(row) is dict}
    required_manifest_facts = {
        "risc0-build": {"package": "rzup", "requirement": "0.5.2", "default_features": False},
        "rzup": {"package": "rsa", "requirement": "0.9"},
        "ark-relations": {
            "package": "tracing-subscriber",
            "requirement": "0.2",
            "optional": True,
            "activated_by_feature": "std",
        },
    }
    for package, fact in required_manifest_facts.items():
        row = manifest_by_package.get(package)
        if type(row) is not dict or row.get("relevant_dependency") != fact:
            _reject("MANIFEST_FACT", package, "exact dependency requirement required")

    _audit_note_oid, audit_note_raw = _blob(root, commit, AUDIT_NOTE_PATH)
    required_note_fragments = (
        b"`cargo audit` also reports `RUSTSEC-2023-0071` for `rsa 0.9.10`",
        b"`cargo audit` still fails on `RUSTSEC-2025-0055`.",
        b"RISC Zero 3.0.x is not the clean migration target",
    )
    if any(fragment not in audit_note_raw for fragment in required_note_fragments):
        _reject("AUDIT_NOTE", AUDIT_NOTE_PATH, "required local audit findings missing")
    return {
        "advisories": sorted(advisory_rows, key=lambda row: row["advisory_id"]),
        "audit_clean": False,
        "audit_note_sha256": sha256_hex(audit_note_raw),
        "dependency_chains": [list(chain) for chain in DEPENDENCY_CHAINS],
        "governed_lock_sha256": sha256_hex(lock_raw),
        "lock_only_resolution": "IMPOSSIBLE_FOR_BOTH_FINDINGS",
        "locked_packages": packages,
        "policy_result": STATUS,
        "risc0_requirement": "=3.0.6",
        "rust_toolchain": "1.90.0",
        "rust_toolchain_sha256": sha256_hex(toolchain_raw),
        "silent_vulnerability_exceptions_allowed": False,
        "source_evidence_sha256": sha256_hex(evidence_raw),
    }


def _stale_candidate(root: Path, stage_a: str) -> dict[str, object]:
    parents = _parents(root, STALE_CANDIDATE)
    if parents != (STALE_CANDIDATE_PARENT,):
        _reject("STALE_CANDIDATE", STALE_CANDIDATE, "candidate parent drift")
    tree = _oid(_git(root, "show", "-s", "--format=%T", STALE_CANDIDATE), STALE_CANDIDATE)
    title = _git(root, "show", "-s", "--format=%s", STALE_CANDIDATE).decode("utf-8").strip()
    if title != "formal: add O008A RISC0 host qualification":
        _reject("STALE_CANDIDATE", STALE_CANDIDATE, "candidate title drift")
    try:
        _tree_entry(root, STALE_CANDIDATE, "docs/research/ZENODEX_RISC0_BUILD_HOST_QUALIFICATION_V2.json")
    except BlockerReject as exc:
        if exc.code != "GIT_ENTRY":
            raise
    else:
        _reject("STALE_CANDIDATE", STALE_CANDIDATE, "candidate unexpectedly contains Stage E")
    changed_paths = _git(
        root,
        "diff",
        "--no-renames",
        "--name-only",
        "-z",
        STALE_CANDIDATE,
        stage_a,
        "--",
        *SOURCE_ROOTS,
    ).split(b"\0")
    paths = sorted(item.decode("utf-8") for item in changed_paths if item)
    if len(paths) != 11:
        _reject("STALE_CANDIDATE", STALE_CANDIDATE, "expected 11 current closure changes")
    write_set = _changes(root, STALE_CANDIDATE_PARENT, STALE_CANDIDATE)
    return {
        "adjudication": "STALE_REJECTED",
        "candidate_commit": STALE_CANDIDATE,
        "candidate_parent": STALE_CANDIDATE_PARENT,
        "candidate_tree": tree,
        "candidate_title": title,
        "candidate_write_set_count": len(write_set),
        "candidate_write_set_root": sha256_hex(canonical_json_bytes([list(row) for row in write_set])),
        "current_source_closure_changed_path_count": len(paths),
        "current_source_closure_changed_paths": paths,
        "current_source_closure_changed_paths_root": sha256_hex(canonical_json_bytes(paths)),
        "historical_bundle_current_application": "REJECTED_STALE_SOURCE_SUBJECT",
        "historical_bundle_payload_sha256": "2a3c91e1e32667afed8d40f0d64f6e5585150bfe5824ea5a79bb42d804a0172d",
        "stage_e_artifact_at_candidate": "ABSENT",
    }


def _resource_feasibility(root: Path, commit: str) -> dict[str, object]:
    _evidence_oid, evidence_raw = _blob(root, commit, EVIDENCE_PATH)
    evidence = decode_json(evidence_raw, EVIDENCE_PATH)
    snapshot = evidence.get("resource_snapshot")
    historical = evidence.get("historical_candidate_evidence")
    if type(snapshot) is not dict or type(historical) is not dict:
        _reject("RESOURCE_EVIDENCE", EVIDENCE_PATH, "resource evidence required")
    sizes = snapshot.get("observed_apparent_sizes_bytes")
    runs = historical.get("run_resource_observations")
    if type(sizes) is not dict or type(runs) is not list or len(runs) != 2:
        _reject("RESOURCE_EVIDENCE", EVIDENCE_PATH, "exact sizes and two runs required")
    integer_values = [*sizes.values(), snapshot.get("tmpfs_free_bytes"), snapshot.get("root_free_bytes"), snapshot.get("available_memory_bytes")]
    if any(type(value) is not int or value < 0 for value in integer_values):
        _reject("RESOURCE_EVIDENCE", EVIDENCE_PATH, "non-negative exact byte counts required")
    run_targets: list[int] = []
    peaks: list[int] = []
    for row in runs:
        if type(row) is not dict:
            _reject("RESOURCE_EVIDENCE", EVIDENCE_PATH, "exact run object required")
        target = row.get("target_size_bytes")
        peak = row.get("max_command_cumulative_child_peak_rss_upper_bound_bytes")
        if type(target) is not int or type(peak) is not int:
            _reject("RESOURCE_EVIDENCE", EVIDENCE_PATH, "exact run observations required")
        run_targets.append(target)
        peaks.append(peak)
    calibration_target = sizes["calibration_target"]
    target_budget = max(max(run_targets), calibration_target)
    evidence_overhead = sizes["external_evidence"] + sizes["audit_evidence"] + sizes["frozen_manifests"]
    reuse_incremental = target_budget + evidence_overhead
    isolated_incremental = reuse_incremental + sizes["qualification_home"] + sizes["vendor_tree"]
    tmpfs_free = snapshot["tmpfs_free_bytes"]
    memory_available = snapshot["available_memory_bytes"]
    return {
        "assessment": "FEASIBLE_ONLY_WITH_CALIBRATED_ISOLATED_BUDGET",
        "build_authorized": False,
        "cache_reuse": {
            "calculated_incremental_bytes": reuse_incremental,
            "calculated_remaining_tmpfs_bytes": tmpfs_free - reuse_incremental,
            "governed_minimum_free_tmpfs_bytes": MIN_REUSE_TMPFS_BYTES,
            "observed_threshold_met": tmpfs_free >= MIN_REUSE_TMPFS_BYTES,
        },
        "full_isolation": {
            "calculated_incremental_bytes": isolated_incremental,
            "calculated_remaining_tmpfs_bytes": tmpfs_free - isolated_incremental,
            "governed_minimum_free_tmpfs_bytes": MIN_ISOLATED_TMPFS_BYTES,
            "observed_threshold_met": tmpfs_free >= MIN_ISOLATED_TMPFS_BYTES,
        },
        "memory": {
            "governed_minimum_available_bytes": MIN_AVAILABLE_MEMORY_BYTES,
            "historical_cumulative_child_peak_rss_upper_bound_bytes": max(peaks),
            "observed_available_bytes": memory_available,
            "observed_headroom_over_historical_upper_bound_bytes": memory_available - max(peaks),
            "observed_threshold_met": memory_available >= MIN_AVAILABLE_MEMORY_BYTES,
        },
        "observation": {
            "captured_at_utc": evidence.get("captured_at_utc"),
            "root_free_bytes": snapshot["root_free_bytes"],
            "semantics": snapshot.get("semantics"),
            "tmpfs_free_bytes": tmpfs_free,
        },
        "required_controls": {
            "cargo_and_home_paths": "FIXED_BENEATH_REQUIRED_TMPDIR",
            "concurrency": "ONE_BUILD_AT_A_TIME",
            "required_tmpdir": "/dev/shm",
            "root_filesystem_build_target_allowed": False,
        },
        "understated_candidate_minima_rejected": {
            "available_memory_bytes": 128 * 1024**2,
            "tmp_free_bytes": 50 * 1024**2,
        },
    }


def validate_semantics(artifact: dict[str, Any]) -> None:
    if artifact.get("schema") != SCHEMA or artifact.get("status") != STATUS:
        _reject("STATUS", "status", "exact blocker schema and status required")
    claims = artifact.get("claim_ceiling")
    if type(claims) is not dict or claims.get("authority") != NO_AUTHORITY:
        _reject("AUTHORITY_PROMOTION", "claim_ceiling.authority", "all authority must be NONE")
    for key in ("build_host_qualified", "build_host_qualification_gap_closed", "qualification_complete", "release_ready"):
        if claims.get(key) is not False:
            _reject("CLAIM_PROMOTION", f"claim_ceiling.{key}", "false required")
    policy = artifact.get("dependency_policy")
    if type(policy) is not dict:
        _reject("DEPENDENCY_POLICY", "dependency_policy", "exact object required")
    advisories = policy.get("advisories")
    if type(advisories) is not list or [row.get("advisory_id") for row in advisories if type(row) is dict] != [
        "RUSTSEC-2023-0071",
        "RUSTSEC-2025-0055",
    ]:
        _reject("ADVISORY_REMOVAL", "dependency_policy.advisories", "both advisories required")
    if policy.get("audit_clean") is not False or policy.get("silent_vulnerability_exceptions_allowed") is not False:
        _reject("DEPENDENCY_POLICY", "dependency_policy", "clean or silent exception claim forbidden")
    stale = artifact.get("stale_candidate_adjudication")
    if type(stale) is not dict or stale.get("adjudication") != "STALE_REJECTED":
        _reject("STALE_CANDIDATE_ACCEPTANCE", "stale_candidate_adjudication", "stale candidate must reject")
    resources = artifact.get("resource_feasibility")
    if type(resources) is not dict or resources.get("build_authorized") is not False:
        _reject("RESOURCE_BUDGET", "resource_feasibility", "build must remain unauthorized")
    reuse = resources.get("cache_reuse")
    isolated = resources.get("full_isolation")
    memory = resources.get("memory")
    controls = resources.get("required_controls")
    if (
        type(reuse) is not dict
        or reuse.get("governed_minimum_free_tmpfs_bytes", 0) < MIN_REUSE_TMPFS_BYTES
        or type(isolated) is not dict
        or isolated.get("governed_minimum_free_tmpfs_bytes", 0) < MIN_ISOLATED_TMPFS_BYTES
        or type(memory) is not dict
        or memory.get("governed_minimum_available_bytes", 0) < MIN_AVAILABLE_MEMORY_BYTES
        or type(controls) is not dict
        or controls.get("required_tmpdir") != "/dev/shm"
        or controls.get("concurrency") != "ONE_BUILD_AT_A_TIME"
    ):
        _reject("RESOURCE_BUDGET_UNDERSTATEMENT", "resource_feasibility", "calibrated minima required")


def build_artifact(root: Path, stage_a: str) -> dict[str, Any]:
    parents = _parents(root, stage_a)
    if parents != (BASE_COMMIT,):
        _reject("STAGE_A_PARENT", stage_a, "exact canonical r8 parent required")
    expected_delta = tuple(("A", path) for path in STAGE_A_PATHS)
    if _changes(root, BASE_COMMIT, stage_a) != expected_delta:
        _reject("STAGE_A_DELTA", stage_a, "Stage A must add only the blocker sources")
    tree = _oid(_git(root, "show", "-s", "--format=%T", stage_a), stage_a)
    source_manifest = [_source_pin(root, stage_a, path) for path in STATIC_INPUT_PATHS]
    core: dict[str, Any] = {
        "schema": SCHEMA,
        "status": STATUS,
        "implementation_subject": {
            "base_commit": BASE_COMMIT,
            "stage_a_commit": stage_a,
            "stage_a_tree": tree,
        },
        "plan_binding": _plan_binding(root, stage_a),
        "source_binding": {
            "governed_build_closure": _closure(root, stage_a),
            "source_manifest": source_manifest,
        },
        "dependency_policy": _dependency_policy(root, stage_a),
        "stale_candidate_adjudication": _stale_candidate(root, stage_a),
        "resource_feasibility": _resource_feasibility(root, stage_a),
        "governed_resolution_options": [
            {
                "id": "CLEAN_UPSTREAM_RELEASE",
                "preferred": True,
                "authorization": "NOT_GRANTED_BY_PACKET",
                "requirements": [
                    "select an exact RISC0 release whose lock removes the rsa advisory path",
                    "resolve tracing-subscriber to >=0.3.20 or remove that path",
                    "govern the plan and lock change, then rebuild every image and receipt",
                ],
            },
            {
                "id": "SOURCE_PINNED_PATCH_OR_FORK",
                "preferred": False,
                "authorization": "NOT_GRANTED_BY_PACKET",
                "requirements": [
                    "review and hash-pin a rzup patch that removes or replaces rsa",
                    "review and hash-pin the ark-relations or RISC0 closure change",
                    "run dependency approval and full image rebuild review",
                ],
            },
            {
                "id": "EXPLICIT_RESEARCH_ONLY_WAIVER",
                "preferred": False,
                "authorization": "NOT_GRANTED_BY_PACKET",
                "requirements": [
                    "record governance approval, exact lock, both advisory IDs, scope, expiry, and residual risk",
                    "keep dependency safety, proof validity, release, and production gates open",
                    "do not convert the waiver into general build-host qualification",
                ],
            },
        ],
        "claim_ceiling": {
            "authority": deepcopy(NO_AUTHORITY),
            "build_host_qualification_gap_closed": False,
            "build_host_qualified": False,
            "clean_build_receipt": "NOT_ACCEPTED",
            "dependency_safe": False,
            "proof_validity": "NOT_CLAIMED",
            "qualification_complete": False,
            "release_ready": False,
            "risc0_3_0_6_image_rebuild_receipt": "HISTORICAL_STALE_NOT_ACCEPTED",
        },
        "nonclaims": [
            "This packet records a blocker; it does not complete O-008A.",
            "No Cargo command, network request, RISC0 build, image rebuild, proof verification, or cleanup was performed.",
            "Historical same-host evidence does not qualify the current source closure.",
            "Resource feasibility is a volatile bounded observation and does not reserve resources or authorize execution.",
            "No dependency safety, proof validity, release, production readiness, settlement, or value-movement claim is made.",
        ],
    }
    root_payload = {
        key: core[key]
        for key in (
            "schema",
            "status",
            "implementation_subject",
            "plan_binding",
            "source_binding",
            "dependency_policy",
            "stale_candidate_adjudication",
            "resource_feasibility",
            "governed_resolution_options",
            "claim_ceiling",
        )
    }
    core["certificate_root"] = sha256_hex(canonical_json_bytes(root_payload))
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
    if raw != expected:
        _reject("ARTIFACT_PROJECTION_DRIFT", ARTIFACT_PATH, "artifact differs from Stage A projection")
    payload = dict(artifact)
    recorded = payload.pop("artifact_payload_sha256", None)
    if recorded != sha256_hex(canonical_json_bytes(payload)):
        _reject("ARTIFACT_PAYLOAD_HASH", ARTIFACT_PATH, "self-excluding payload digest mismatch")
    return artifact


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


def check_blocker(root: Path) -> dict[str, Any]:
    stage_a: str | None = None
    stage_b: str | None = None
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
        if _git(root, "merge-base", "--is-ancestor", stage_b, head) != b"":
            _reject("STAGE_B_ANCESTRY", stage_b, "Stage B must be in current ancestry")
        _artifact_oid, committed = _blob(root, stage_b, ARTIFACT_PATH)
        expected = artifact_bytes(root, stage_a)
        artifact = validate_artifact_bytes(committed, expected)
        current_oid, current = _blob(root, head, ARTIFACT_PATH)
        if current != committed or current_oid != _artifact_oid:
            _reject("CURRENT_ARTIFACT_DRIFT", ARTIFACT_PATH, "current Git artifact differs from Stage B")
        if _working_bytes(root, ARTIFACT_PATH) != committed:
            _reject("WORKTREE_ARTIFACT_DRIFT", ARTIFACT_PATH, "working artifact differs from Stage B")
        source_pins = artifact["source_binding"]["source_manifest"]
        for pin in source_pins:
            path = pin["path"]
            current_source_oid, current_source = _blob(root, head, path)
            if current_source_oid != pin["git_blob_sha"] or sha256_hex(current_source) != pin["sha256"]:
                _reject("CURRENT_SOURCE_DRIFT", path, "current Git source differs from Stage A")
            if _working_bytes(root, path) != current_source:
                _reject("WORKTREE_SOURCE_DRIFT", path, "working source differs from Stage A")
        if _closure(root, head) != artifact["source_binding"]["governed_build_closure"]:
            _reject("CURRENT_CLOSURE_DRIFT", "source_binding", "governed closure differs from Stage A")
        return {
            "artifact_payload_sha256": artifact["artifact_payload_sha256"],
            "artifact_sha256": sha256_hex(committed),
            "authority": deepcopy(NO_AUTHORITY),
            "certificate_root": artifact["certificate_root"],
            "finding": None,
            "historical_valid": True,
            "current_applicable": True,
            "ok": True,
            "qualification_complete": False,
            "release_ready": False,
            "schema": CHECK_SCHEMA,
            "stage_a_commit": stage_a,
            "stage_b_commit": stage_b,
            "status": STATUS,
        }
    except (BlockerReject, OSError) as exc:
        finding = (
            {"code": exc.code, "detail": exc.detail, "path": exc.path}
            if isinstance(exc, BlockerReject)
            else {"code": "IO_ERROR", "detail": type(exc).__name__, "path": str(root)}
        )
        return {
            "artifact_payload_sha256": None,
            "artifact_sha256": None,
            "authority": deepcopy(NO_AUTHORITY),
            "certificate_root": None,
            "finding": finding,
            "historical_valid": False,
            "current_applicable": False,
            "ok": False,
            "qualification_complete": False,
            "release_ready": False,
            "schema": CHECK_SCHEMA,
            "stage_a_commit": stage_a,
            "stage_b_commit": stage_b,
            "status": STATUS,
        }
