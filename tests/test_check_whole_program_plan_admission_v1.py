from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable

import pytest

import tools.check_whole_program_plan_admission_v1 as admission_checker
from tools.check_whole_program_plan_admission_v1 import (
    DEFAULT_RECEIPT,
    DEFAULT_REGISTRY,
    PLAN_COMMIT,
    REPO_ROOT,
    check_whole_program_plan_admission_v1,
)


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert type(value) is dict
    return value


def _write(tmp_path: Path, name: str, value: dict[str, Any]) -> Path:
    path = tmp_path / name
    path.write_text(json.dumps(value), encoding="utf-8")
    return path


def test_exact_plan_admission_selects_one_research_plan_without_authority() -> None:
    report = check_whole_program_plan_admission_v1()

    assert report == {
        "schema": "zenodex/plan-admission-check/v1",
        "ok": True,
        "active_research_plan_count": 1,
        "active_plan_commit": PLAN_COMMIT,
        "production_authority": "NONE",
        "settlement_authority": "NONE",
        "closed_value_movement_gate_count": 0,
        "findings": [],
    }


@pytest.mark.parametrize(
    ("mutator", "expected_finding"),
    [
        (
            lambda receipt, _registry: receipt["authority"].update(
                {"production_authority": "ACTIVE"}
            ),
            "admission authority ceiling drift",
        ),
        (
            lambda receipt, _registry: receipt["admitted_plan"].update({"commit": "0" * 40}),
            "admitted plan subject drift",
        ),
        (
            lambda receipt, _registry: receipt["subject_files"][0].update({"sha256": "0" * 64}),
            "admitted subject-file inventory or hash drift",
        ),
        (
            lambda receipt, _registry: receipt["subject_files"][0].update({"unexpected": "field"}),
            "admitted subject-file inventory or hash drift",
        ),
        (
            lambda receipt, _registry: receipt["advisory_review"].update(
                {"artifact_sha256": "0" * 64}
            ),
            "advisory review binding drift",
        ),
        (
            lambda receipt, _registry: receipt["normative_inputs"][0].update({"sha256": "0" * 64}),
            "admission normative-input binding drift",
        ),
        (
            lambda receipt, _registry: receipt["normative_inputs"][0].update(
                {"unexpected": "field"}
            ),
            "admission normative-input binding drift",
        ),
        (
            lambda receipt, _registry: receipt["upstream_dependency_binding"].update(
                {"plan_field_sha256": "0" * 64}
            ),
            "admission upstream-dependency binding drift",
        ),
        (
            lambda receipt, _registry: receipt["selection_premise"].update(
                {"classification": "MACHINE_VERIFIED"}
            ),
            "external user-selection premise drift",
        ),
        (
            lambda receipt, _registry: receipt.update({"receipt_payload_sha256": "0" * 64}),
            "admission receipt payload hash mismatch",
        ),
        (
            lambda _receipt, registry: registry.update({"active_plan_count": 2}),
            "active-plan registry must contain exactly one plan",
        ),
        (
            lambda _receipt, registry: registry.update({"active_plan_count": True}),
            "active-plan registry must contain exactly one plan",
        ),
        (
            lambda _receipt, registry: registry["active_plans"][0].update(
                {"admission_receipt_payload_sha256": "0" * 64}
            ),
            "active-plan registry subject or receipt binding drift",
        ),
        (
            lambda _receipt, registry: registry["authority"].update(
                {"value_movement_authority": "ACTIVE"}
            ),
            "active-plan registry authority ceiling drift",
        ),
        (
            lambda receipt, _registry: receipt.update(
                {"admission_scope": "This plan authorizes settlement."}
            ),
            "admission scope drift",
        ),
        (
            lambda receipt, _registry: receipt.update({"nonclaims": []}),
            "admission nonclaims drift",
        ),
        (
            lambda _receipt, registry: registry.update(
                {"replacement_rule": "Any plan may replace the active plan."}
            ),
            "active-plan registry replacement rule drift",
        ),
        (
            lambda _receipt, registry: registry.update(
                {"nonclaim": "Active grants production authority."}
            ),
            "active-plan registry nonclaim drift",
        ),
    ],
)
def test_plan_admission_semantic_mutants_fail_closed(
    tmp_path: Path,
    mutator: Callable[[dict[str, Any], dict[str, Any]], object],
    expected_finding: str,
) -> None:
    receipt = copy.deepcopy(_load(REPO_ROOT / DEFAULT_RECEIPT))
    registry = copy.deepcopy(_load(REPO_ROOT / DEFAULT_REGISTRY))
    mutator(receipt, registry)

    report = check_whole_program_plan_admission_v1(
        receipt_path=_write(tmp_path, "receipt.json", receipt),
        registry_path=_write(tmp_path, "registry.json", registry),
    )

    assert report["ok"] is False
    findings = report["findings"]
    assert type(findings) is list
    assert expected_finding in findings


def test_plan_admission_rejects_duplicate_receipt_keys(tmp_path: Path) -> None:
    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(
        '{"schema":"zenodex/plan-admission-receipt/v1","schema":"forged"}',
        encoding="utf-8",
    )

    report = check_whole_program_plan_admission_v1(receipt_path=receipt_path)

    assert report["ok"] is False
    assert report["findings"] == ["admission inputs cannot be loaded: JSON_DECODE"]


def test_plan_admission_rejects_duplicate_registry_keys(tmp_path: Path) -> None:
    registry_path = tmp_path / "registry.json"
    registry_path.write_text(
        '{"schema":"zenodex/active-whole-program-plan-registry/v1","schema":"forged"}',
        encoding="utf-8",
    )

    report = check_whole_program_plan_admission_v1(registry_path=registry_path)

    assert report["ok"] is False
    assert report["findings"] == ["admission inputs cannot be loaded: JSON_DECODE"]


def test_plan_admission_rejects_semantically_equal_oversized_receipt(
    tmp_path: Path,
) -> None:
    receipt_path = tmp_path / "receipt.json"
    source = (REPO_ROOT / DEFAULT_RECEIPT).read_text(encoding="utf-8")
    receipt_path.write_text(source + (" " * 65_536), encoding="utf-8")

    report = check_whole_program_plan_admission_v1(receipt_path=receipt_path)

    assert report["ok"] is False
    assert report["findings"] == ["admission inputs cannot be loaded: FILE_SIZE_LIMIT"]


def test_plan_admission_rejects_symlinked_receipt(tmp_path: Path) -> None:
    receipt_path = tmp_path / "receipt.json"
    receipt_path.symlink_to(REPO_ROOT / DEFAULT_RECEIPT)

    report = check_whole_program_plan_admission_v1(receipt_path=receipt_path)

    assert report["ok"] is False
    assert report["findings"] == ["admission inputs cannot be loaded: FILE_SYMLINK"]


def test_plan_admission_ignores_ambient_path_for_git(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_git = tmp_path / "git"
    fake_git.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
    fake_git.chmod(0o700)
    monkeypatch.setenv("PATH", str(tmp_path))

    report = check_whole_program_plan_admission_v1()

    assert report["ok"] is True


def test_plan_admission_rejects_nonstandard_nonfinite_json(tmp_path: Path) -> None:
    receipt_path = tmp_path / "receipt.json"
    source = (REPO_ROOT / DEFAULT_RECEIPT).read_text(encoding="utf-8")
    receipt_path.write_text(
        source.replace('"production_authority": "NONE"', '"production_authority": NaN', 1),
        encoding="utf-8",
    )

    report = check_whole_program_plan_admission_v1(receipt_path=receipt_path)

    assert report["ok"] is False
    assert report["findings"] == ["admission inputs cannot be loaded: JSON_DECODE"]


def test_plan_admission_rejects_excessive_json_depth_without_escaping(
    tmp_path: Path,
) -> None:
    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(("[" * 2_000) + "0" + ("]" * 2_000), encoding="utf-8")

    report = check_whole_program_plan_admission_v1(receipt_path=receipt_path)

    assert report["ok"] is False
    assert report["findings"] == ["admission inputs cannot be loaded: JSON_DEPTH_LIMIT"]


def test_plan_admission_requires_plan_commit_on_current_head_lineage(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_git = admission_checker._git

    def without_ancestry(root: Path, args: list[str]) -> bytes | None:
        if args == ["merge-base", "--is-ancestor", PLAN_COMMIT, "HEAD"]:
            return None
        return original_git(root, args)

    monkeypatch.setattr(admission_checker, "_git", without_ancestry)

    report = check_whole_program_plan_admission_v1()

    assert report["ok"] is False
    assert "admitted plan commit is not on current HEAD lineage" in report["findings"]


def test_plan_admission_replays_normative_input_from_historical_commit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_git = admission_checker._git
    normative_path = "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"

    def forged_normative_blob(root: Path, args: list[str]) -> bytes | None:
        if args == ["show", f"{PLAN_COMMIT}:{normative_path}"]:
            return b"{}"
        return original_git(root, args)

    monkeypatch.setattr(admission_checker, "_git", forged_normative_blob)

    report = check_whole_program_plan_admission_v1()

    assert report["ok"] is False
    assert f"admitted normative input does not replay: {normative_path}" in report["findings"]
