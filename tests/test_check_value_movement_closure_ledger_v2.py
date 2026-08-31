from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

from tools import value_movement_closure_ledger_v2 as ledger
from tools.check_value_movement_closure_ledger_v2 import (
    check_value_movement_closure_ledger_v2,
)

ROOT = Path(__file__).resolve().parents[1]


def _git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", "--sparse", "-A")
    _git(
        root,
        "-c",
        "user.name=O005B V2 Test",
        "-c",
        "user.email=o005b-v2@example.invalid",
        "commit",
        "-m",
        message,
    )
    return _git(root, "rev-parse", "HEAD")


def _source_bytes() -> dict[str, bytes]:
    return {path: (ROOT / path).read_bytes() for path in ledger.SOURCE_PATHS_V2}


def _subject_repo(tmp_path: Path) -> Path:
    """Create a sparse local subject while retaining admitted-plan ancestry."""

    repo = tmp_path / "subject"
    subprocess.run(
        ("git", "clone", "--shared", "--no-checkout", "--quiet", str(ROOT), str(repo)),
        check=True,
        capture_output=True,
        text=True,
    )
    _git(repo, "sparse-checkout", "init", "--no-cone")
    _git(repo, "sparse-checkout", "set", "--no-cone", *ledger.SOURCE_PATHS_V2)
    _git(repo, "checkout", "-q", "-b", "o005b-test-subject", _git(ROOT, "rev-parse", "HEAD"))
    for relative_path in ledger.SOURCE_PATHS_V2:
        source = ROOT / relative_path
        target = repo / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    (repo / "o005b-stage-a-marker.txt").write_text("exact Stage A\n", encoding="utf-8")
    _commit(repo, "stage-a O005B ledger source")
    return repo


def _stage_b_repo(tmp_path: Path) -> tuple[Path, bytes, str]:
    repo = _subject_repo(tmp_path)
    stage_a = _git(repo, "rev-parse", "HEAD")
    payload = ledger.build_ledger_bytes_v2(repo)
    artifact = repo / ledger.ARTIFACT_RELATIVE_PATH_V2
    artifact.parent.mkdir(parents=True, exist_ok=True)
    artifact.write_bytes(payload)
    _commit(repo, "stage-b O005B ledger artifact")
    return repo, payload, stage_a


def _finding_code(report: dict[str, object]) -> str:
    findings = report["findings"]
    assert type(findings) is list and findings
    finding = findings[0]
    assert type(finding) is dict
    code = finding["code"]
    assert type(code) is str
    return code


def test_stage_a_projection_closes_only_current_ledger_gap() -> None:
    artifact = ledger.build_ledger_artifact_from_sources_v2("a" * 40, _source_bytes())

    assert artifact["schema"] == ledger.SCHEMA_V2
    assert artifact["closed_gap"] == "current_closure_ledger_gap"
    assert artifact["authority"] == ledger.NO_AUTHORITY_V2
    assert artifact["vm_gates_closed"] == []
    gates = artifact["current_gate_rows"]
    assert type(gates) is list
    assert [row["gate_id"] for row in gates] == list(ledger.GATE_IDS_V2)
    assert all(row["closed"] is False for row in gates)
    assert all(row["current_promoted_evidence"] == [] for row in gates)
    donors = artifact["historical_donor_rows"]
    assert type(donors) is list
    assert all(row["disposition"] == "STALE_DONOR_NOT_CURRENT_EVIDENCE" for row in donors)


def test_stage_b_checker_requires_exact_artifact_only_child(tmp_path: Path) -> None:
    repo, payload, stage_a = _stage_b_repo(tmp_path)

    report = check_value_movement_closure_ledger_v2(repo)

    assert report["ok"] is True
    assert report["implementation_subject"] == stage_a
    assert report["artifact_sha256"] == ledger.sha256_hex_v2(payload)
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True
    assert report["closed_value_movement_gate_count"] == 0
    assert report["authority"] == ledger.NO_AUTHORITY_V2


def test_checker_rejects_source_drift_after_preserving_historical_validity(
    tmp_path: Path,
) -> None:
    repo, _payload, _stage_a = _stage_b_repo(tmp_path)
    formal_claim = repo / ledger.FORMAL_CLAIM_PATH_V2
    formal_claim.write_text(formal_claim.read_text(encoding="utf-8") + "\n", encoding="utf-8")
    _commit(repo, "mutate current formal claim")

    report = check_value_movement_closure_ledger_v2(repo)

    assert report["ok"] is False
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False
    assert _finding_code(report) == "CURRENT_SOURCE_DRIFT"


def test_checker_rejects_noncanonical_or_non_artifact_stage_b(tmp_path: Path) -> None:
    repo, payload, _stage_a = _stage_b_repo(tmp_path)
    artifact = repo / ledger.ARTIFACT_RELATIVE_PATH_V2
    artifact.write_text(json.dumps(json.loads(payload), indent=2), encoding="utf-8")
    report = check_value_movement_closure_ledger_v2(repo)
    assert report["ok"] is False
    assert _finding_code(report) == "NONCANONICAL_ARTIFACT"

    invalid_root = tmp_path / "invalid"
    invalid_root.mkdir()
    invalid_repo = _subject_repo(invalid_root)
    artifact = invalid_repo / ledger.ARTIFACT_RELATIVE_PATH_V2
    artifact.parent.mkdir(parents=True, exist_ok=True)
    artifact.write_bytes(ledger.build_ledger_bytes_v2(invalid_repo))
    (invalid_repo / "extra-stage-b.txt").write_text("forbidden\n", encoding="utf-8")
    _commit(invalid_repo, "invalid stage B")
    report = check_value_movement_closure_ledger_v2(invalid_repo)
    assert report["ok"] is False
    assert _finding_code(report) == "ARTIFACT_TOPOLOGY"


def test_checker_rejects_index_suppression_and_dirty_sources(tmp_path: Path) -> None:
    repo, _payload, _stage_a = _stage_b_repo(tmp_path)
    _git(repo, "update-index", "--assume-unchanged", ledger.FORMAL_CLAIM_PATH_V2)
    report = check_value_movement_closure_ledger_v2(repo)
    assert report["ok"] is False
    assert _finding_code(report) == "INDEX_SUPPRESSION"

    dirty_root = tmp_path / "dirty"
    dirty_root.mkdir()
    dirty_repo, _payload, _stage_a = _stage_b_repo(dirty_root)
    plan = dirty_repo / ledger.PLAN_PATH_V2
    plan.write_text(plan.read_text(encoding="utf-8") + "\n", encoding="utf-8")
    report = check_value_movement_closure_ledger_v2(dirty_repo)
    assert report["ok"] is False
    assert _finding_code(report) == "WORKTREE_SOURCE_DRIFT"


def test_direct_cli_build_and_check_roundtrip(tmp_path: Path) -> None:
    repo = _subject_repo(tmp_path)
    builder = repo / "tools/build_value_movement_closure_ledger_v2.py"
    checker = repo / "tools/check_value_movement_closure_ledger_v2.py"

    built = subprocess.run(
        (sys.executable, str(builder), "--root", str(repo)),
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    assert built.returncode == 0, built.stderr
    _commit(repo, "stage-b O005B ledger artifact")

    checked_build = subprocess.run(
        (sys.executable, str(builder), "--root", str(repo), "--check"),
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    checked = subprocess.run(
        (sys.executable, str(checker), "--root", str(repo)),
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    assert checked_build.returncode == 0, checked_build.stderr
    assert checked.returncode == 0, checked.stderr
    assert json.loads(checked.stdout)["ok"] is True
