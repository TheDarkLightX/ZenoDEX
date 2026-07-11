from __future__ import annotations

import copy
import json
from datetime import date
from pathlib import Path
from typing import Any

import pytest

from tools import check_zrpf_v3_firecracker_runtime_artifacts as checker


def test_committed_runtime_artifact_package_is_internally_bound() -> None:
    report = checker.build_report(evidence_date=date(2026, 7, 11))

    assert report["ok"] is True
    assert report["errors"] == []
    assert report["supported_on_evidence_date"] is True
    assert all(value is False for value in report["authority"].values())


def test_kernel_support_date_fails_closed_after_minimum_support() -> None:
    report = checker.build_report(evidence_date=date(2026, 9, 3))

    assert report["ok"] is False
    assert report["errors"] == ["guest_kernel_support_expired_for_evidence_date"]
    assert report["supported_on_evidence_date"] is False


def test_cross_check_rejects_kernel_authority_promotion() -> None:
    manifest, kernel_record, image_record, profile = _governed_inputs()
    promoted = copy.deepcopy(kernel_record)
    promoted["authority"]["production_authority"] = True

    errors = checker._cross_check(
        manifest,
        kernel_record=promoted,
        kernel_record_sha256=checker.EXPECTED_KERNEL_RECORD_SHA256,
        image_record=image_record,
        image_recipe_sha256=checker.EXPECTED_IMAGE_RECIPE_SHA256,
        profile=profile,
    )

    assert "kernel_record_authority_mismatch" in errors


def test_build_report_rejects_profile_claim_promotion(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    profile = json.loads(checker.PROFILE_PATH.read_text(encoding="utf-8"))
    profile["claims"]["production_authority"] = True
    promoted_path = tmp_path / "profile.json"
    promoted_path.write_bytes(checker.runtime.canonical_document_bytes(profile))
    monkeypatch.setattr(checker, "PROFILE_PATH", promoted_path)

    report = checker.build_report(evidence_date=date(2026, 7, 11))

    assert report["ok"] is False
    assert "profile_canonical_hash_mismatch" in report["errors"]


def test_cross_check_rejects_receipt_inventory_mutation() -> None:
    manifest, kernel_record, image_record, profile = _governed_inputs()
    mutated = copy.deepcopy(image_record)
    receipt = mutated["input_image"]["filesystem_inventory"]["entries"][2]
    receipt["sha256"] = "12" * 32

    errors = checker._cross_check(
        manifest,
        kernel_record=kernel_record,
        kernel_record_sha256=checker.EXPECTED_KERNEL_RECORD_SHA256,
        image_record=mutated,
        image_recipe_sha256=checker.EXPECTED_IMAGE_RECIPE_SHA256,
        profile=profile,
    )

    assert "input_inventory_root_mismatch" in errors
    assert "receipt_set_root_mismatch" in errors


def _governed_inputs() -> tuple[Any, dict[str, Any], dict[str, Any], dict[str, Any]]:
    manifest = checker.runtime.load_runtime_manifest(
        checker.MANIFEST_PATH,
        expected_canonical_sha256=checker.EXPECTED_MANIFEST_CANONICAL_SHA256,
    )
    kernel_record = json.loads(checker.KERNEL_RECORD_PATH.read_text(encoding="utf-8"))
    image_record = json.loads(checker.IMAGE_RECORD_PATH.read_text(encoding="utf-8"))
    profile = json.loads(checker.PROFILE_PATH.read_text(encoding="utf-8"))
    return manifest, kernel_record, image_record, profile
