"""Exact research-plan admission: immutable source replay and fixed file writes.

Human selection remains an external premise. Writes assume exclusive access to
trusted repository directories; per-file replacement is not a database commit.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools import check_whole_program_plan_v3 as plan_checker
from tools.build_m6_normative_requirements_v1 import _atomic_replace_regular_file_v1
from tools.o008_formal_cycle_shell_v1 import tree_entry_v1

REPO_ROOT = Path(__file__).resolve().parents[1]
TRUSTED_PLAN_COMMIT: str | None = "bde0fac341f312b8b12b96d0bf1477a7091cdc3f"
PLAN_PATH = plan_checker.DEFAULT_PLAN
REGISTRY_PATH = Path("docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json")
HISTORY_PATH = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2_1_REGISTRY.json")
RECEIPT_PATH = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V2.json")
OLD_RECEIPT_PATH = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json")
REVIEW_PATH = "docs/research/ZENODEX_WHOLE_PROGRAM_V3_ADVISORY_REVIEW.md"
CHECKER_PATH = "tools/check_whole_program_plan_v3.py"
SUBJECT_PATHS = tuple(sorted((str(PLAN_PATH), REVIEW_PATH, CHECKER_PATH,
    "docs/ZENODEX_COMPLETION_PLAN.md",
    "docs/research/ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md",
    "tests/test_check_whole_program_plan_v3.py")))
GENERATION_COMMAND = "python3 tools/build_whole_program_plan_admission_v2.py --write"
MAX_INPUT_BYTES = 131_072
AUTHORITY = {k: "NONE" for k in ("production_authority", "settlement_authority",
                               "release_authority", "value_movement_authority")}
REJECTS = (plan_checker.PlanReject, plan_checker.RequirementsRejectV1,
           plan_checker.ShellRejectV1, plan_checker.AdmissionRejectV1)


@dataclass(frozen=True, slots=True)
class AdmissionArtifacts:
    receipt: bytes
    registry: bytes
    historical_registry: bytes


def _require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise plan_checker.PlanReject(code, detail)


def _read(path: Path) -> bytes:
    return plan_checker._read_bounded_regular_file_v1(path, MAX_INPUT_BYTES, str(path))


def _decode(raw: bytes) -> dict[str, Any]:
    return plan_checker.decode_json_object_v1(raw, "plan admission")


def _encode(value: object) -> bytes:
    return plan_checker.canonical_json_bytes_v1(value)


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git(root: Path, *args: str) -> str:
    return plan_checker._run_git_v1(root, tuple(args))[1].strip()


def _blob(root: Path, commit: str, path: str) -> tuple[dict[str, str], bytes]:
    port = plan_checker.GitReadPortV1(root)
    entry = tree_entry_v1(port, commit, path)
    if entry is None:
        raise plan_checker.PlanReject("SUBJECT_FILE_MISSING", path)
    mode, oid = entry
    _require(mode in ("100644", "100755"), "SUBJECT_FILE_MODE", path)
    raw = plan_checker.read_blob_v1(port, oid, path)
    return {"path": path, "blob": oid, "mode": mode, "sha256": _sha(raw)}, raw


def expected_artifacts(root: Path = REPO_ROOT) -> AdmissionArtifacts:
    """Replay the fixed committed subject before constructing any inert output."""
    commit = TRUSTED_PLAN_COMMIT
    if commit is None:
        raise plan_checker.PlanReject("PLAN_ANCHOR_UNSET", "reviewed commit has not been pinned")
    _require(len(commit) == 40 and all(c in "0123456789abcdef" for c in commit), "PLAN_ANCHOR", "exact commit required")
    _require(_git(root, "rev-parse", "--verify", commit + "^{commit}") == commit, "PLAN_ANCHOR", "commit mismatch")
    _require(_git(root, "rev-list", "--parents", "-n", "1", commit).split() == [commit, plan_checker.BASE_COMMIT], "PLAN_PARENT", "single pinned baseline parent required")
    _git(root, "merge-base", "--is-ancestor", commit, "HEAD")
    tree = _git(root, "rev-parse", commit + "^{tree}")
    changed = _git(root, "diff-tree", "--no-commit-id", "--name-only", "-r", commit).splitlines()
    _require(changed == list(SUBJECT_PATHS), "SUBJECT_INVENTORY", "reviewed bundle inventory drift")
    blobs = {path: _blob(root, commit, path) for path in SUBJECT_PATHS}
    plan_raw = blobs[str(PLAN_PATH)][1]
    _require(_read(root / PLAN_PATH) == plan_raw, "CURRENT_PLAN_DRIFT", str(PLAN_PATH))
    _require(_read(Path(plan_checker.__file__)) == blobs[CHECKER_PATH][1], "CURRENT_CHECKER_DRIFT", CHECKER_PATH)
    plan = _decode(plan_raw)
    manifest = plan_checker._source_manifest(root, plan)
    plan_checker.validate_plan_v3(plan, manifest)
    old_registry = _blob(root, plan_checker.BASE_COMMIT, str(REGISTRY_PATH))[1]
    old_receipt = _blob(root, plan_checker.BASE_COMMIT, str(OLD_RECEIPT_PATH))[1]
    _require(_read(root / OLD_RECEIPT_PATH) == old_receipt, "HISTORICAL_RECEIPT_DRIFT", str(OLD_RECEIPT_PATH))
    review = blobs[REVIEW_PATH][0]
    receipt = {
        "schema": "zenodex/plan-admission-receipt/v2", "status": "ADMITTED_RESEARCH_IMPLEMENTATION_PLAN",
        "admitted_plan": {"schema": plan["schema"], "commit": commit, "parent": plan_checker.BASE_COMMIT,
            "tree": tree, "plan_path": str(PLAN_PATH), "plan_sha256": _sha(plan_raw)},
        "subject_files": [blobs[path][0] for path in SUBJECT_PATHS],
        "selection_premise": {"classification": "EXTERNAL_USER_DIRECTIVE_NOT_MACHINE_VERIFIED",
            "selected_plan_commit": commit, "scope": "RESEARCH_IMPLEMENTATION_COORDINATION_ONLY", "authority": "NONE"},
        "advisory_review": {"artifact_commit": commit, "artifact_path": REVIEW_PATH,
            "artifact_blob": review["blob"], "artifact_sha256": review["sha256"],
            "evidence_class": "HASH_BOUND_ADVISORY_ARTIFACT", "authority": "NONE"},
        "predecessor": {"source_commit": plan_checker.BASE_COMMIT, "registry_source_path": str(REGISTRY_PATH),
            "registry_history_path": str(HISTORY_PATH), "registry_sha256": _sha(old_registry),
            "receipt_path": str(OLD_RECEIPT_PATH), "receipt_sha256": _sha(old_receipt)},
        "authority": dict(AUTHORITY), "claim_ceiling": dict(plan_checker.CEILING),
        "generation_command": GENERATION_COMMAND,
        "nonclaims": ["Selection orders research implementation only; it grants no economic or release authority.",
            "The user-selection premise is external and not machine verified.",
            "The exact advisory review is bound as an artifact; it is not a proof.",
            "Source and plan replay closes no implementation, formal, deployment or value-movement gate.",
            "File replacement assumes exclusive access to trusted repository directories."],
    }
    receipt["receipt_payload_sha256"] = _sha(_encode(receipt))
    registry = _decode(old_registry)
    registry["active_plans"] = [{"plan_schema": plan["schema"], "plan_commit": commit,
        "plan_tree": tree, "plan_path": str(PLAN_PATH), "plan_sha256": _sha(plan_raw),
        "admission_receipt_path": str(RECEIPT_PATH),
        "admission_receipt_payload_sha256": receipt["receipt_payload_sha256"],
        "activation_class": "ACTIVE_RESEARCH_IMPLEMENTATION_PLAN"}]
    return AdmissionArtifacts(_encode(receipt) + b"\n", _encode(registry) + b"\n", old_registry)


def _report() -> dict[str, Any]:
    return {"schema": "zenodex/plan-admission-check/v2", "ok": False, "findings": [],
        "active_research_plan_count": 0, **AUTHORITY, "claim_ceiling": dict(plan_checker.CEILING)}


def _failure(report: dict[str, Any], exc: Any) -> dict[str, Any]:
    report["findings"] = [{"code": exc.code, "detail": exc.detail}]
    return report


def check_active_whole_program_plan_v2(
    root: Path = REPO_ROOT, *, receipt_path: Path | None = None,
    registry_path: Path | None = None, history_path: Path | None = None,
) -> dict[str, Any]:
    """Check the single selected plan; all successful claims remain research-only."""
    report = _report()
    try:
        expected = expected_artifacts(root)
        for path, raw, code in ((receipt_path or root / RECEIPT_PATH, expected.receipt, "ADMISSION_RECEIPT"),
                               (registry_path or root / REGISTRY_PATH, expected.registry, "ACTIVE_REGISTRY")):
            _require(_encode(_decode(_read(path))) == _encode(_decode(raw)), code, "exact closed artifact required")
        _require(_read(history_path or root / HISTORY_PATH) == expected.historical_registry,
                 "HISTORICAL_REGISTRY", "original registry bytes required")
        report.update(ok=True, active_research_plan_count=1, active_plan_commit=TRUSTED_PLAN_COMMIT)
    except REJECTS as exc:
        return _failure(report, exc)
    return report


def _optional(path: Path) -> bytes | None:
    try:
        return _read(path)
    except plan_checker.ShellRejectV1 as exc:
        if exc.code == "FILE_NOT_FOUND":
            return None
        raise


def build_whole_program_plan_admission_v2(
    root: Path = REPO_ROOT, *, write: bool = False,
) -> dict[str, Any]:
    """Prepare, or write three fixed artifacts with the active registry last."""
    report = _report()
    try:
        _require(type(write) is bool, "WRITE_TYPE", "exact boolean required")
        expected = expected_artifacts(root)
        outputs = ((HISTORY_PATH, expected.historical_registry), (RECEIPT_PATH, expected.receipt),
                   (REGISTRY_PATH, expected.registry))
        observed = {path: _optional(root / path) for path, _ in outputs}
        _require(observed[REGISTRY_PATH] in (expected.historical_registry, expected.registry),
                 "REGISTRY_REPLACEMENT", "only exact previous or selected registry may be replaced")
        for path, raw in outputs[:2]:
            _require(observed[path] in (None, raw), "OUTPUT_CONFLICT", str(path))
        if write:
            for path, raw in outputs:
                if observed[path] != raw:
                    _atomic_replace_regular_file_v1(root / path, raw)
                _require(_read(root / path) == raw, "OUTPUT_REPLAY", str(path))
        report.update(ok=True, written=write, generation_command=GENERATION_COMMAND,
            receipt_payload_sha256=_decode(expected.receipt)["receipt_payload_sha256"],
            active_research_plan_count=1 if write else 0)
    except REJECTS as exc:
        return _failure(report, exc)
    return report
