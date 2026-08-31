"""Focused adversarial tests for the future O-008 V2 Stage-A evidence packet."""

from __future__ import annotations

import copy
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, NamedTuple, cast

import pytest

from tools.check_global_settlement_abi_v2_o008_evidence_v2 import check_evidence_v2
from tools.global_settlement_abi_v2_o008_evidence_v2 import (
    DEPENDENCY_EXPECTATIONS_V2,
    HISTORICAL_V1_PATHS_V2,
    RESOURCE_LIMITS_V2,
    STAGE_A_PARENT_V2,
    STAGE_A_WRITE_SET_V2,
    WIRE_RECORD_FIELDS_V2,
    build_evidence_v2,
    canonical_json_bytes_v2,
)

ROOT = Path(__file__).resolve().parents[1]


class StageA(NamedTuple):
    root: Path
    commit: str


def _run_git(root: Path, *args: str) -> str:
    completed = subprocess.run(
        ("git", *args),
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    return completed.stdout.strip()


def _make_stage_a(
    destination: Path,
    *,
    omit_path: str | None = None,
    executable_path: str | None = None,
) -> StageA:
    subprocess.run(
        ("git", "clone", "--shared", "--no-checkout", str(ROOT), str(destination)),
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    _run_git(destination, "checkout", "--detach", STAGE_A_PARENT_V2)
    for _status, path in STAGE_A_WRITE_SET_V2:
        if path == omit_path:
            continue
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / path, target)
    _run_git(destination, "add", "--all")
    if executable_path is not None:
        _run_git(destination, "update-index", "--chmod=+x", "--", executable_path)
    _run_git(destination, "config", "user.name", "O008 evidence test")
    _run_git(destination, "config", "user.email", "o008-evidence@example.invalid")
    _run_git(destination, "commit", "-m", "temporary O008 Stage A")
    return StageA(destination.resolve(), _run_git(destination, "rev-parse", "HEAD"))


@pytest.fixture(scope="module")
def stage_a(tmp_path_factory: pytest.TempPathFactory) -> StageA:
    return _make_stage_a(tmp_path_factory.mktemp("o008-stage") / "repo")


def _artifact(tmp_path: Path, stage_a: StageA) -> tuple[Path, dict[str, object]]:
    value = build_evidence_v2(stage_a.root, stage_a.commit)
    path = tmp_path / "o008-v2.json"
    path.write_bytes(canonical_json_bytes_v2(value))
    return path, value


def _check_mutant(tmp_path: Path, stage_a: StageA, mutate: Any) -> dict[str, Any]:
    path, value = _artifact(tmp_path, stage_a)
    mutant = copy.deepcopy(value)
    mutate(mutant)
    path.write_bytes(canonical_json_bytes_v2(mutant))
    return check_evidence_v2(
        path, root=stage_a.root, stage_a_commit=stage_a.commit
    )


def test_stage_a_extractor_binds_topology_and_eleven_wire_dto_field_sets(
    stage_a: StageA,
) -> None:
    value = build_evidence_v2(stage_a.root, stage_a.commit)
    stage = cast(dict[str, object], value["stage_a"])
    assert stage["parent"] == STAGE_A_PARENT_V2
    assert stage["write_set_count"] == len(STAGE_A_WRITE_SET_V2)
    manifest = cast(list[dict[str, object]], value["source_manifest"])
    assert len(manifest) == len(STAGE_A_WRITE_SET_V2)
    assert all(row["mode"] == "100644" for row in manifest)
    assert {row["path"] for row in manifest} == {
        path for _status, path in STAGE_A_WRITE_SET_V2
    }
    assert {path for _status, path in STAGE_A_WRITE_SET_V2} <= set(
        cast(list[str], value["checked_paths"])
    )
    records = value["wire_dtos"]
    assert type(records) is list
    assert len(records) == 11
    assert {row["dto"]: tuple(row["fields"]) for row in records} == WIRE_RECORD_FIELDS_V2
    assert value["resource_limits"] == RESOURCE_LIMITS_V2
    fixture = cast(dict[str, object], value["fixture"])
    parity = cast(dict[str, str], fixture["per_record_parity"])
    assert len(parity) == 11
    assert all(len(digest) == 64 for digest in parity.values())
    assert (
        value["accepted_witness_conversion"]
        == "OPAQUE_NO_WIRE_TO_DOMAIN_CONVERSION"
    )
    assert value["safe_domain_input_conversions"] == ["LaneContext", "Candidate"]
    assert value["candidate_order"] == "SUPPLIED_ORDER_PRESERVED"
    assert value["closed_value_movement_gates"] == 0
    assert value["required_value_movement_gates"] == 12


def test_generated_temp_artifact_checks_with_explicit_root_and_subject(
    tmp_path: Path, stage_a: StageA
) -> None:
    path, value = _artifact(tmp_path, stage_a)
    report = check_evidence_v2(
        path, root=stage_a.root, stage_a_commit=stage_a.commit
    )
    assert report["ok"] is True, report["errors"]
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True
    assert report["status"] == "BOUNDED_CORE_IMPLEMENTED_DEPENDENCY_BLOCKED"
    assert report["release_ready"] is False
    assert report["authority"] == "NONE"
    assert report["closed_value_movement_gates"] == 0
    assert report["required_value_movement_gates"] == 12
    assert set(cast(dict[str, object], value["historical_stage_a_dependencies"])) == {
        "O-006",
        "O-007B",
        "O-007C",
        "O-008A",
    }


def test_relative_root_is_rejected_before_subject_acquisition() -> None:
    with pytest.raises(ValueError, match="explicit absolute"):
        build_evidence_v2(Path("."), "0" * 40)


@pytest.mark.parametrize("symbolic", ["HEAD", "HEAD^", "main", "0" * 40])
def test_symbolic_or_unresolvable_subjects_fail_closed(
    stage_a: StageA, symbolic: str
) -> None:
    with pytest.raises(ValueError):
        build_evidence_v2(stage_a.root, symbolic)


@pytest.mark.parametrize(
    "mutate",
    [
        lambda value: value["stage_a"].__setitem__("commit", "0" * 40),
        lambda value: value["field_profiles"].__setitem__("profile_authentication_shadow", {"value": "ACTIVE"}),
        lambda value: value["resource_limits"].__setitem__("assets", 257),
        lambda value: value["resource_limits"].__setitem__("assets", 0),
        lambda value: value["historical_stage_a_dependencies"]["O-008A"].__setitem__("status", "CLOSED"),
        lambda value: value["source_manifest"][0].__setitem__("sha256", "0" * 64),
        lambda value: value.__setitem__("status", "CLOSED"),
    ],
)
def test_claim_field_profile_limit_dependency_subject_and_source_mutants_fail_closed(
    tmp_path: Path, stage_a: StageA, mutate: Any
) -> None:
    report = _check_mutant(tmp_path, stage_a, mutate)
    assert report["ok"] is False
    assert report["status"] == "INVALID_FAIL_CLOSED"
    assert report["authority"] == "NONE"


def test_historical_v1_blobs_and_current_bytes_are_preserved(stage_a: StageA) -> None:
    value = build_evidence_v2(stage_a.root, stage_a.commit)
    historical = value["historical_v1_preservation"]
    assert type(historical) is dict
    for path in HISTORICAL_V1_PATHS_V2:
        pinned = subprocess.run(
            ["git", "show", f"{stage_a.commit}:{path}"],
            cwd=stage_a.root,
            check=True,
            capture_output=True,
        ).stdout
        assert (stage_a.root / path).read_bytes() == pinned
        assert historical[path]["sha256"] == __import__("hashlib").sha256(pinned).hexdigest()


def test_builder_and_checker_cli_reject_artifact_drift(
    tmp_path: Path, stage_a: StageA
) -> None:
    path, value = _artifact(tmp_path, stage_a)
    markdown = tmp_path / "o008-v2.md"
    builder = ROOT / "tools/build_global_settlement_abi_v2_o008_evidence_v2.py"
    generated = subprocess.run([sys.executable, str(builder), "--root", str(stage_a.root), "--stage-a-commit", stage_a.commit, "--output-json", str(path), "--output-md", str(markdown)], cwd=stage_a.root, text=True, capture_output=True, check=False)
    assert generated.returncode == 0, generated.stderr
    checked = subprocess.run([sys.executable, str(builder), "--root", str(stage_a.root), "--stage-a-commit", stage_a.commit, "--output-json", str(path), "--output-md", str(markdown), "--check"], cwd=stage_a.root, text=True, capture_output=True, check=False)
    assert checked.returncode == 0, checked.stderr
    fixture = cast(dict[str, object], value["fixture"])
    fixture["whole_sha256"] = "0" * 64
    path.write_bytes(canonical_json_bytes_v2(value))
    checker = ROOT / "tools/check_global_settlement_abi_v2_o008_evidence_v2.py"
    rejected = subprocess.run([sys.executable, str(checker), str(path), "--root", str(stage_a.root), "--stage-a-commit", stage_a.commit], cwd=stage_a.root, text=True, capture_output=True, check=False)
    assert rejected.returncode == 1
    assert json.loads(rejected.stdout)["ok"] is False


@pytest.mark.parametrize(
    ("mutation", "expected_error"),
    [
        (
            lambda raw: raw.replace(
                b'"status":"BOUNDED_CORE_IMPLEMENTED_DEPENDENCY_BLOCKED"',
                b'"status":"CLOSED","status":"BOUNDED_CORE_IMPLEMENTED_DEPENDENCY_BLOCKED"',
                1,
            ),
            "duplicate JSON field",
        ),
        (
            lambda raw: json.dumps(json.loads(raw), indent=2, sort_keys=True).encode(),
            "noncanonical JSON encoding",
        ),
        (
            lambda raw: raw.replace(
                b'"closed_value_movement_gates":0',
                b'"closed_value_movement_gates":0.0',
                1,
            ),
            "floating-point JSON number",
        ),
        (
            lambda raw: raw.replace(
                b'"closed_value_movement_gates":0',
                b'"closed_value_movement_gates":false',
                1,
            ),
            "artifact differs",
        ),
    ],
)
def test_duplicate_noncanonical_float_and_bool_json_fail_closed(
    tmp_path: Path,
    stage_a: StageA,
    mutation: Any,
    expected_error: str,
) -> None:
    path, _value = _artifact(tmp_path, stage_a)
    path.write_bytes(mutation(path.read_bytes()))
    report = check_evidence_v2(
        path, root=stage_a.root, stage_a_commit=stage_a.commit
    )
    assert report["ok"] is False
    assert expected_error in " ".join(report["errors"])


def test_wrong_mode_and_missing_stage_donor_fail_closed(tmp_path: Path) -> None:
    wrong_mode_path = "tools/global_settlement_abi_v2_o008_evidence_v2.py"
    wrong_mode = _make_stage_a(
        tmp_path / "wrong-mode",
        executable_path=wrong_mode_path,
    )
    with pytest.raises(ValueError, match="100644"):
        build_evidence_v2(wrong_mode.root, wrong_mode.commit)

    missing = _make_stage_a(
        tmp_path / "missing-donor",
        omit_path="tools/render_global_settlement_abi_v2_wire_records_golden.py",
    )
    with pytest.raises(ValueError, match="write-set drift"):
        build_evidence_v2(missing.root, missing.commit)


def test_missing_dependency_fails_closed(
    stage_a: StageA, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setitem(
        DEPENDENCY_EXPECTATIONS_V2["O-007C"],
        "path",
        "docs/research/DOES_NOT_EXIST_O007C.json",
    )
    with pytest.raises(ValueError, match="missing or ambiguous"):
        build_evidence_v2(stage_a.root, stage_a.commit)


def test_current_drift_does_not_rewrite_historical_validity(
    tmp_path: Path, stage_a: StageA
) -> None:
    path, _value = _artifact(tmp_path, stage_a)
    drift_path = stage_a.root / "src/core/global_settlement_wire_records_v2.py"
    original = drift_path.read_bytes()
    try:
        drift_path.write_bytes(original + b"\n# current drift\n")
        report = check_evidence_v2(
            path, root=stage_a.root, stage_a_commit=stage_a.commit
        )
    finally:
        drift_path.write_bytes(original)
    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False
    assert report["current_source_drift"] == [
        "src/core/global_settlement_wire_records_v2.py"
    ]


def test_later_o007c_refresh_is_outside_o008_source_applicability(
    tmp_path: Path, stage_a: StageA
) -> None:
    path, value = _artifact(tmp_path, stage_a)
    dependency_path = DEPENDENCY_EXPECTATIONS_V2["O-007C"]["path"]
    current_paths = cast(list[str], value["current_applicability_paths"])
    assert dependency_path in cast(list[str], value["checked_paths"])
    assert dependency_path not in current_paths
    target = stage_a.root / dependency_path
    original = target.read_bytes()
    try:
        target.write_bytes(b'{"stage_b_refresh":"independently_checked"}\n')
        report = check_evidence_v2(
            path, root=stage_a.root, stage_a_commit=stage_a.commit
        )
    finally:
        target.write_bytes(original)
    assert report["ok"] is True
    assert report["current_applicable"] is True
    assert report["current_source_drift"] == []


def test_optimized_python_checker_rejects_bool_mutant(
    tmp_path: Path, stage_a: StageA
) -> None:
    path, _value = _artifact(tmp_path, stage_a)
    path.write_bytes(
        path.read_bytes().replace(
            b'"closed_value_movement_gates":0',
            b'"closed_value_movement_gates":false',
            1,
        )
    )
    checker = ROOT / "tools/check_global_settlement_abi_v2_o008_evidence_v2.py"
    rejected = subprocess.run(
        [
            sys.executable,
            "-O",
            str(checker),
            str(path),
            "--root",
            str(stage_a.root),
            "--stage-a-commit",
            stage_a.commit,
        ],
        cwd=stage_a.root,
        text=True,
        capture_output=True,
        check=False,
    )
    assert rejected.returncode == 1
    assert json.loads(rejected.stdout)["ok"] is False
