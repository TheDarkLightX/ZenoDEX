"""Adversarial tests for the FCIS M5-P4B5A ATDD execution contract."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from tools.check_fcis_m5_p4b5a_atdd_contract import (
    GitDiffDiscoveryError,
    discover_changed_paths,
    resolve_merge_base,
    validate_matrix,
)
from tools.fcis_m5_p4b5a_atdd_validation import select_relevant_changed_paths

REPO_ROOT = Path(__file__).resolve().parents[2]
CHECKER = REPO_ROOT / "tools/check_fcis_m5_p4b5a_atdd_contract.py"
MATRIX = (
    REPO_ROOT
    / "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/ACCEPTANCE_MATRIX.json"
)


def _load_matrix() -> dict[str, Any]:
    return json.loads(MATRIX.read_text(encoding="utf-8"))


def _write_matrix(path: Path, value: dict[str, Any]) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _run_checker(
    path: Path = MATRIX,
    *,
    assigned_id: str = "ATDD-B1B1-009",
    diff_base: str = "HEAD",
) -> tuple[int, dict[str, Any]]:
    command = [
        sys.executable,
        "-B",
        str(CHECKER),
        "--matrix",
        str(path),
        "--assigned-id",
        assigned_id,
        "--diff-base",
        diff_base,
    ]
    completed = subprocess.run(
        command,
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.stderr == ""
    return completed.returncode, json.loads(completed.stdout)


def test_clean_atdd_contract_is_accepted() -> None:
    returncode, report = _run_checker()

    assert returncode == 0
    assert report.pop("changed_path_count") >= 0
    assert report == {
        "acceptance_case_count": 20,
        "assigned_acceptance_id": "ATDD-B1B1-009",
        "b1b1_case_count": 12,
        "b1b2_case_count": 8,
        "errors": [],
        "ok": True,
        "phase_order": ["B1B-1", "B1B-2"],
        "schema": "zenodex/fcis-m5-p4b5a-atdd-contract/v1",
    }


def test_duplicate_acceptance_id_is_rejected(tmp_path: Path) -> None:
    value = _load_matrix()
    value["acceptance_cases"].append(dict(value["acceptance_cases"][0]))
    path = tmp_path / "duplicate.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "ACCEPTANCE_ID_DUPLICATE:ATDD-B1B1-001" in report["errors"]


def test_missing_counterexample_is_rejected(tmp_path: Path) -> None:
    value = _load_matrix()
    del value["acceptance_cases"][0]["counterexample"]
    path = tmp_path / "missing-counterexample.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert (
        "ACCEPTANCE_FIELDS:ATDD-B1B1-001:missing=counterexample:unknown="
        in report["errors"]
    )


def test_phase_order_drift_is_rejected(tmp_path: Path) -> None:
    value = _load_matrix()
    value["phase_order"] = ["B1B-2", "B1B-1"]
    path = tmp_path / "phase-order.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "PHASE_ORDER:B1B-2,B1B-1" in report["errors"]


def test_b1b2_execution_authority_is_rejected(tmp_path: Path) -> None:
    value = _load_matrix()
    value["phases"]["B1B-2"]["execution_authorized"] = True
    value["phases"]["B1B-2"]["status"] = "authorized"
    path = tmp_path / "premature-b1b2.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert "B1B2_EXECUTION_PREMATURE" in report["errors"]
    assert returncode == 1


def test_b1b2_short_promotion_gate_is_rejected(tmp_path: Path) -> None:
    value = _load_matrix()
    value["phases"]["B1B-2"]["promotion_gate"] = "two reviews"
    path = tmp_path / "short-b1b2-promotion.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "B1B2_PROMOTION_GATE" in report["errors"]


def test_b1b2_design_packet_procedure_cannot_be_omitted(tmp_path: Path) -> None:
    value = _load_matrix()
    del value["b1b2_design_gate"]["design_packet"]
    path = tmp_path / "missing-b1b2-packet-procedure.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "B1B2_DESIGN_GATE" in report["errors"]


def test_hidden_pythonpath_requirement_is_rejected(tmp_path: Path) -> None:
    value = _load_matrix()
    value["acceptance_cases"][1]["evidence_commands"] = [
        "PYTHONPATH=. python3 -m pytest -q tests/core"
    ]
    path = tmp_path / "hidden-env.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "EVIDENCE_HIDDEN_ENV:ATDD-B1B1-002:PYTHONPATH=" in report["errors"]


def test_b1b1_forbidden_authority_surface_cannot_be_removed(tmp_path: Path) -> None:
    value = _load_matrix()
    value["phases"]["B1B-1"]["forbidden_scope"].remove(
        "PinnedDeploymentBootstrapVerifierV2"
    )
    path = tmp_path / "scope-widening.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert (
        "B1B1_FORBIDDEN_SCOPE:"
        "missing=PinnedDeploymentBootstrapVerifierV2:unknown="
        in report["errors"]
    )


def test_normative_target_substitution_is_rejected(tmp_path: Path) -> None:
    value = _load_matrix()
    value["normative_authority"]["target_commit"] = "0" * 40
    path = tmp_path / "wrong-target.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "NORMATIVE_AUTHORITY:target_commit" in report["errors"]


def test_duplicate_json_member_is_rejected(tmp_path: Path) -> None:
    raw = MATRIX.read_text(encoding="utf-8")
    path = tmp_path / "duplicate-member.json"
    path.write_text(
        raw.replace(
            '"contract_version": "1.0.0",',
            '"contract_version": "1.0.0",\n  "contract_version": "1.0.0",',
            1,
        ),
        encoding="utf-8",
    )

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert report["errors"] == ["MATRIX_INVALID:DuplicateJsonMember:contract_version"]


def test_probity_cannot_be_promoted_to_authority(tmp_path: Path) -> None:
    value = _load_matrix()
    value["probity"]["authority"] = True
    path = tmp_path / "probity-authority.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "PROBITY_MUST_REMAIN_NON_AUTHORITATIVE" in report["errors"]


def test_disk_bounded_mutation_harness_case_is_required(tmp_path: Path) -> None:
    value = _load_matrix()
    value["acceptance_cases"] = [
        case
        for case in value["acceptance_cases"]
        if case["id"] != "ATDD-B1B1-011"
    ]
    path = tmp_path / "missing-bounded-harness.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert (
        "ACCEPTANCE_IDS:missing=ATDD-B1B1-011:unknown="
        in report["errors"]
    )


def test_preflight_case_cannot_require_a_red_implementation_test(
    tmp_path: Path,
) -> None:
    value = _load_matrix()
    value["case_lifecycle"]["red_required"].append("ATDD-B1B1-001")
    path = tmp_path / "preflight-red.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
    assert "RED_REQUIRED_NOT_IMPLEMENTATION:ATDD-B1B1-001" in report["errors"]


def test_out_of_scope_changed_path_is_rejected() -> None:
    errors, _, _ = validate_matrix(
        _load_matrix(),
        assigned_id="ATDD-B1B1-009",
        changed_paths=(
            "src/core/fcis_fee_distribution_configuration_content_validation.py",
        ),
    )

    assert (
        "CHANGED_PATH_FORBIDDEN:"
        "src/core/fcis_fee_distribution_configuration_content_validation.py"
        in errors
    )


def test_unowned_changed_path_is_rejected() -> None:
    errors, _, _ = validate_matrix(
        _load_matrix(),
        assigned_id="ATDD-B1B1-009",
        changed_paths=("src/core/fcis_b1b_unreviewed_authority.py",),
    )

    assert "CHANGED_PATH_UNOWNED:src/core/fcis_b1b_unreviewed_authority.py" in errors


def test_event_scope_ignores_unrelated_cumulative_paths() -> None:
    assert select_relevant_changed_paths(
        (
            "docs/research/m6_tasks/TASK_J07_REPORT.md",
            "requirements-core.lock.txt",
            "src/core/fcis_b1b_unreviewed_authority.py",
        )
    ) == ("src/core/fcis_b1b_unreviewed_authority.py",)


def test_event_scope_retains_every_forbidden_path() -> None:
    path = "src/core/fcis_fee_distribution_configuration_content_validation.py"

    assert select_relevant_changed_paths((path,)) == (path,)


def test_event_scope_retains_registered_shared_integration_path() -> None:
    path = "rust-runtime/crates/zenodex-runtime-core/src/lib.rs"

    assert select_relevant_changed_paths((path,)) == (path,)


def test_changed_path_must_be_owned_by_active_assigned_id() -> None:
    errors, _, _ = validate_matrix(
        _load_matrix(),
        assigned_id="ATDD-B1B1-003",
        changed_paths=("tools/check_fcis_m5_p4b5a_atdd_contract.py",),
    )

    assert (
        "CHANGED_PATH_NOT_OWNED_BY_ASSIGNED_ID:ATDD-B1B1-003:"
        "tools/check_fcis_m5_p4b5a_atdd_contract.py"
        in errors
    )



def test_planned_carrier_acceptance_path_is_owned() -> None:
    path = "tests/core/test_fcis_b1b1_carriers.py"
    for assigned_id in (
        "ATDD-B1B1-003",
        "ATDD-B1B1-005",
        "ATDD-B1B1-007",
    ):
        errors, _, _ = validate_matrix(
            _load_matrix(),
            assigned_id=assigned_id,
            changed_paths=(path,),
        )
        assert errors == []


def test_changed_paths_are_derived_from_git_without_caller_enumeration(
    tmp_path: Path,
) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()

    def run_git(*arguments: str) -> None:
        subprocess.run(
            ["git", *arguments],
            cwd=repo,
            check=True,
            capture_output=True,
        )

    run_git("init", "-q")
    run_git("config", "user.email", "atdd@example.invalid")
    run_git("config", "user.name", "FCIS ATDD")
    (repo / "tracked.txt").write_text("before\n", encoding="utf-8")
    run_git("add", "tracked.txt")
    run_git("commit", "-qm", "base")
    (repo / "tracked.txt").write_text("after\n", encoding="utf-8")
    (repo / "untracked.txt").write_text("new\n", encoding="utf-8")

    assert discover_changed_paths(repo, "HEAD") == (
        "tracked.txt",
        "untracked.txt",
    )


def test_event_diff_uses_the_exact_git_merge_base(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()

    def run_git(*arguments: str) -> str:
        return subprocess.run(
            ["git", *arguments],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()

    run_git("init", "-q")
    run_git("config", "user.email", "atdd@example.invalid")
    run_git("config", "user.name", "FCIS ATDD")
    (repo / "base.txt").write_text("base\n", encoding="utf-8")
    run_git("add", "base.txt")
    run_git("commit", "-qm", "base")
    common = run_git("rev-parse", "HEAD")
    run_git("branch", "feature")
    (repo / "main.txt").write_text("main\n", encoding="utf-8")
    run_git("add", "main.txt")
    run_git("commit", "-qm", "main advances")
    main_head = run_git("rev-parse", "HEAD")
    run_git("checkout", "-q", "feature")
    (repo / "feature.txt").write_text("feature\n", encoding="utf-8")
    run_git("add", "feature.txt")
    run_git("commit", "-qm", "feature advances")

    assert resolve_merge_base(repo, main_head) == common


def test_ignored_owned_evidence_path_must_be_force_added(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()

    def run_git(*arguments: str) -> None:
        subprocess.run(
            ["git", *arguments],
            cwd=repo,
            check=True,
            capture_output=True,
        )

    run_git("init", "-q")
    run_git("config", "user.email", "atdd@example.invalid")
    run_git("config", "user.name", "FCIS ATDD")
    (repo / ".gitignore").write_text("tests/tools/\n", encoding="utf-8")
    run_git("add", ".gitignore")
    run_git("commit", "-qm", "base")
    evidence = repo / "tests/tools/test_check_fcis_m5_p4b5a_atdd_contract.py"
    evidence.parent.mkdir(parents=True)
    evidence.write_text("ignored evidence\n", encoding="utf-8")

    with pytest.raises(
        GitDiffDiscoveryError,
        match="owned evidence path is ignored and untracked",
    ):
        discover_changed_paths(repo, "HEAD")



def test_inherited_revision31_digest_is_pinned(tmp_path: Path) -> None:
    value = _load_matrix()
    value["normative_authority"]["carrier_definition_sha256"] = "0" * 64
    path = tmp_path / "wrong-carrier-source.json"
    _write_matrix(path, value)

    returncode, report = _run_checker(path)

    assert returncode == 1
