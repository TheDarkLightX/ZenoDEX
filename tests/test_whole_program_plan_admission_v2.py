"""Pinned admission and fixed-destination publication; no economic authority.

Git replay uses the actual reviewed subject. Writer histories use its immutable
expected bytes in temporary directories, without changing the repository.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import whole_program_plan_admission_v2 as admission


@pytest.fixture(scope="module")
def artifacts() -> admission.AdmissionArtifacts:
    return admission.expected_artifacts(admission.REPO_ROOT)


def _case(tmp_path: Path, artifacts: admission.AdmissionArtifacts) -> dict[str, Path]:
    paths = {"receipt_path": tmp_path / "receipt.json", "registry_path": tmp_path / "registry.json",
             "history_path": tmp_path / "history.json"}
    for key, raw in (("receipt_path", artifacts.receipt), ("registry_path", artifacts.registry),
                     ("history_path", artifacts.historical_registry)):
        paths[key].write_bytes(raw)
    return paths


def test_pinned_commit_replays_and_selects_only_research(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts,
) -> None:
    report = admission.check_active_whole_program_plan_v2(**_case(tmp_path, artifacts))
    assert report["ok"] is True, report
    assert report["active_research_plan_count"] == 1
    assert report["active_plan_commit"] == admission.TRUSTED_PLAN_COMMIT
    assert report["production_authority"] == "NONE"
    assert report["claim_ceiling"] == admission.plan_checker.CEILING
    receipt = json.loads(artifacts.receipt)
    assert receipt["selection_premise"]["classification"] == "EXTERNAL_USER_DIRECTIVE_NOT_MACHINE_VERIFIED"
    assert receipt["advisory_review"]["authority"] == "NONE"
    assert receipt["generation_command"] == admission.GENERATION_COMMAND
    assert {r["path"] for r in receipt["subject_files"]} == set(admission.SUBJECT_PATHS)


@pytest.mark.parametrize(("role", "mutate"), [
    ("receipt_path", lambda r: r["authority"].update(production_authority="ACTIVE")),
    ("receipt_path", lambda r: r["claim_ceiling"].update(formal_core_complete=True)),
    ("receipt_path", lambda r: r["admitted_plan"].update(commit="0" * 40)),
    ("receipt_path", lambda r: r["admitted_plan"].update(parent="0" * 40)),
    ("receipt_path", lambda r: r["subject_files"].pop()),
    ("receipt_path", lambda r: r["subject_files"][0].update(unchecked=True)),
    ("receipt_path", lambda r: r["advisory_review"].update(artifact_sha256="0" * 64)),
    ("receipt_path", lambda r: r.pop("advisory_review")),
    ("receipt_path", lambda r: r["selection_premise"].update(classification="MACHINE_VERIFIED")),
    ("receipt_path", lambda r: r.update(receipt_payload_sha256="0" * 64)),
    ("receipt_path", lambda r: r.update(generation_command="arbitrary command")),
    ("receipt_path", lambda r: r["predecessor"].update(registry_sha256="0" * 64)),
    ("registry_path", lambda r: r.update(active_plan_count=2)),
    ("registry_path", lambda r: r.update(active_plan_count=True)),
    ("registry_path", lambda r: r["active_plans"].append(dict(r["active_plans"][0]))),
    ("registry_path", lambda r: r["active_plans"][0].update(admission_receipt_path="other.json")),
    ("registry_path", lambda r: r.update(unchecked=True)),
])
def test_admission_semantic_mutants_fail_closed(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts, role: str,
    mutate: Callable[[dict[str, Any]], Any],
) -> None:
    paths = _case(tmp_path, artifacts)
    value = json.loads(paths[role].read_bytes())
    mutate(value)
    paths[role].write_text(json.dumps(value), encoding="utf-8")
    report = admission.check_active_whole_program_plan_v2(**paths)
    assert report["ok"] is False
    assert report["active_research_plan_count"] == 0
    assert report["production_authority"] == "NONE"
    assert report["claim_ceiling"]["closed_value_movement_gate_count"] == 0


@pytest.mark.parametrize("raw", [b'{"x":1,"x":2}', b"[]", b"{", b'{"x":NaN}',
                                  b'{"x":1.2}', b"\xff", b"[" * 2000 + b"0" + b"]" * 2000])
def test_untrusted_json_rejection_has_no_selection(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts, raw: bytes,
) -> None:
    paths = _case(tmp_path, artifacts)
    paths["receipt_path"].write_bytes(raw)
    report = admission.check_active_whole_program_plan_v2(**paths)
    assert report["ok"] is False
    assert report["active_research_plan_count"] == 0


def test_historical_registry_requires_exact_original_bytes(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts,
) -> None:
    paths = _case(tmp_path, artifacts)
    paths["history_path"].write_bytes(artifacts.historical_registry + b"\n")
    report = admission.check_active_whole_program_plan_v2(**paths)
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "HISTORICAL_REGISTRY"


def test_missing_large_and_symlink_inputs_fail_closed(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts,
) -> None:
    paths = _case(tmp_path, artifacts)
    receipt = paths["receipt_path"]
    receipt.unlink()
    assert admission.check_active_whole_program_plan_v2(**paths)["ok"] is False
    receipt.write_bytes(b" " * (admission.MAX_INPUT_BYTES + 1))
    assert admission.check_active_whole_program_plan_v2(**paths)["ok"] is False
    receipt.unlink()
    receipt.symlink_to(paths["registry_path"])
    assert admission.check_active_whole_program_plan_v2(**paths)["ok"] is False


def test_unpinned_commit_rejects_without_any_write(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(admission, "TRUSTED_PLAN_COMMIT", None)
    report = admission.build_whole_program_plan_admission_v2()
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "PLAN_ANCHOR_UNSET"


def test_foreign_head_cannot_admit_the_plan(tmp_path: Path) -> None:
    report = admission.build_whole_program_plan_admission_v2(root=tmp_path)
    assert report["ok"] is False


@pytest.mark.parametrize(("source", "code"), [(admission.PLAN_PATH, "CURRENT_PLAN_DRIFT"),
    (Path(admission.plan_checker.__file__), "CURRENT_CHECKER_DRIFT"),
    (admission.OLD_RECEIPT_PATH, "HISTORICAL_RECEIPT_DRIFT")])
def test_current_source_drift_prevents_selection(
    source: Path, code: str, monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = admission._read

    def changed(path: Path) -> bytes:
        raw = original(path)
        return raw + b"\n" if path == admission.REPO_ROOT / source else raw

    monkeypatch.setattr(admission, "_read", changed)
    report = admission.build_whole_program_plan_admission_v2()
    assert report["ok"] is False
    assert report["findings"][0]["code"] == code


def test_missing_committed_review_prevents_selection(monkeypatch: pytest.MonkeyPatch) -> None:
    original = admission._blob

    def missing(root: Path, commit: str, path: str) -> tuple[dict[str, str], bytes]:
        if path == admission.REVIEW_PATH:
            raise admission.plan_checker.PlanReject("SUBJECT_FILE_MISSING", path)
        return original(root, commit, path)

    monkeypatch.setattr(admission, "_blob", missing)
    report = admission.build_whole_program_plan_admission_v2()
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "SUBJECT_FILE_MISSING"


def test_ancestry_gate_failure_prevents_selection(monkeypatch: pytest.MonkeyPatch) -> None:
    original = admission._git

    def unrelated(root: Path, *args: str) -> str:
        if args[0] == "merge-base":
            raise admission.plan_checker.PlanReject("WRONG_ANCESTRY", "unrelated HEAD")
        return original(root, *args)

    monkeypatch.setattr(admission, "_git", unrelated)
    report = admission.build_whole_program_plan_admission_v2()
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "WRONG_ANCESTRY"


def _writer_root(tmp_path: Path, artifacts: admission.AdmissionArtifacts,
                 monkeypatch: pytest.MonkeyPatch) -> Path:
    (tmp_path / admission.REGISTRY_PATH).parent.mkdir(parents=True)
    (tmp_path / admission.REGISTRY_PATH).write_bytes(artifacts.historical_registry)
    monkeypatch.setattr(admission, "expected_artifacts", lambda root: artifacts)
    return tmp_path


def test_given_old_registry_when_builder_runs_then_history_precedes_selection_and_retry_is_exact(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = _writer_root(tmp_path, artifacts, monkeypatch)
    before = {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()}
    assert admission.build_whole_program_plan_admission_v2(root=root)["ok"] is True
    assert {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()} == before
    writes: list[Path] = []
    original = admission._atomic_replace_regular_file_v1

    def record(path: Path, raw: bytes) -> None:
        if path == root / admission.REGISTRY_PATH:
            assert (root / admission.HISTORY_PATH).read_bytes() == artifacts.historical_registry
            assert (root / admission.RECEIPT_PATH).read_bytes() == artifacts.receipt
        writes.append(path.relative_to(root))
        original(path, raw)

    monkeypatch.setattr(admission, "_atomic_replace_regular_file_v1", record)
    assert admission.build_whole_program_plan_admission_v2(root=root, write=True)["ok"] is True
    assert writes == [admission.HISTORY_PATH, admission.RECEIPT_PATH, admission.REGISTRY_PATH]
    writes.clear()
    assert admission.build_whole_program_plan_admission_v2(root=root, write=True)["ok"] is True
    assert writes == []


@pytest.mark.parametrize("destination", ["REGISTRY_PATH", "HISTORY_PATH", "RECEIPT_PATH"])
def test_conflicting_artifacts_reject_before_any_builder_write(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts, monkeypatch: pytest.MonkeyPatch,
    destination: str,
) -> None:
    root = _writer_root(tmp_path, artifacts, monkeypatch)
    path = root / getattr(admission, destination)
    path.write_bytes(b"preserve unrelated work")
    before = {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()}
    result = admission.build_whole_program_plan_admission_v2(root=root, write=True)
    assert result["ok"] is False
    assert {p.relative_to(root): p.read_bytes() for p in root.rglob("*") if p.is_file()} == before


def test_interrupted_preparation_retains_previous_selection_and_resumes(
    tmp_path: Path, artifacts: admission.AdmissionArtifacts, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = _writer_root(tmp_path, artifacts, monkeypatch)
    original = admission._atomic_replace_regular_file_v1

    def interrupt(path: Path, raw: bytes) -> None:
        if path == root / admission.RECEIPT_PATH:
            raise admission.plan_checker.PlanReject("TEST_INTERRUPTION", "before receipt write")
        original(path, raw)

    monkeypatch.setattr(admission, "_atomic_replace_regular_file_v1", interrupt)
    report = admission.build_whole_program_plan_admission_v2(root=root, write=True)
    assert report["ok"] is False
    assert (root / admission.REGISTRY_PATH).read_bytes() == artifacts.historical_registry
    assert (root / admission.HISTORY_PATH).read_bytes() == artifacts.historical_registry
    monkeypatch.setattr(admission, "_atomic_replace_regular_file_v1", original)
    assert admission.build_whole_program_plan_admission_v2(root=root, write=True)["ok"] is True
    assert (root / admission.REGISTRY_PATH).read_bytes() == artifacts.registry
