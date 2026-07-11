from __future__ import annotations

import copy
import hashlib
import json
import os
import shutil
import subprocess
from datetime import date
from pathlib import Path
from typing import Any

import pytest

from tools import check_zrpf_v3_firecracker_runtime_artifacts as checker


def test_committed_runtime_artifact_package_is_internally_bound() -> None:
    report = checker.build_report()

    assert report["ok"] is True
    assert report["errors"] == []
    assert report["recorded_evidence_date"] == "2026-07-11"
    assert report["historical_evidence_supported_on_recorded_date"] is True
    assert report["current_runtime_eligibility_checked"] is False
    assert report["current_runtime_eligible"] is False
    assert all(value is False for value in report["authority"].values())


def test_current_runtime_eligibility_requirement_fails_closed_without_policy(
    capsys,
) -> None:
    exit_code = checker.main(["--require-current-runtime-eligible"])
    report = json.loads(capsys.readouterr().out)

    assert exit_code == 1
    assert report["ok"] is True
    assert report["current_runtime_eligibility_checked"] is False
    assert report["current_runtime_eligible"] is False


def test_current_runtime_eligibility_accepts_explicit_supported_date() -> None:
    report = checker.build_report(current_release_date=date(2026, 7, 11))

    assert report["ok"] is True
    assert report["current_release_date"] == "2026-07-11"
    assert report["current_runtime_eligibility_checked"] is True
    assert report["current_runtime_eligible"] is True


def test_current_runtime_eligibility_expires_independently_of_history() -> None:
    report = checker.build_report(current_release_date=date(2026, 9, 3))

    assert report["ok"] is False
    assert report["historical_evidence_supported_on_recorded_date"] is True
    assert report["current_runtime_eligibility_checked"] is True
    assert report["current_runtime_eligible"] is False
    assert report["errors"] == [
        "guest_kernel_support_expired_for_current_release_date"
    ]


def test_image_builder_rejects_wrong_readelf_identity_before_inspection(
    tmp_path: Path,
) -> None:
    completed = _run_image_builder_to_readelf_boundary(
        tmp_path,
        readelf_binary=_resolved_readelf(),
        expected_readelf_sha256="00" * 32,
    )

    assert completed.returncode == 2
    assert completed.stdout == b""
    assert completed.stderr == b"error: readelf identity mismatch\n"


def test_image_builder_rejects_readelf_symlink(tmp_path: Path) -> None:
    link = tmp_path / "readelf-link"
    target = _resolved_readelf()
    link.symlink_to(target)
    completed = _run_image_builder_to_readelf_boundary(
        tmp_path,
        readelf_binary=link,
        expected_readelf_sha256=_sha256_path(target),
    )

    assert completed.returncode == 2
    assert completed.stdout == b""
    assert completed.stderr == b"error: readelf binary rejected\n"


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

    report = checker.build_report()

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


def _run_image_builder_to_readelf_boundary(
    tmp_path: Path,
    *,
    readelf_binary: Path,
    expected_readelf_sha256: str,
) -> subprocess.CompletedProcess[bytes]:
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir(exist_ok=True)
    mksquashfs = fake_bin / "mksquashfs"
    mksquashfs.write_bytes(b"#!/bin/sh\nexit 99\n")
    mksquashfs.chmod(0o755)
    guest = tmp_path / "guest"
    guest.write_bytes(b"guest")
    receipts = tmp_path / "receipts"
    receipts.mkdir(exist_ok=True)
    return subprocess.run(
        [
            checker.IMAGE_RECIPE_PATH.as_posix(),
            "--guest-binary",
            guest.as_posix(),
            "--receipt-dir",
            receipts.as_posix(),
            "--output-dir",
            (tmp_path / "output").as_posix(),
            "--expected-guest-sha256",
            _sha256_path(guest),
            "--expected-receipt-set-sha256",
            "11" * 32,
            "--expected-mksquashfs-sha256",
            _sha256_path(mksquashfs),
            "--readelf-binary",
            readelf_binary.as_posix(),
            "--expected-readelf-sha256",
            expected_readelf_sha256,
        ],
        check=False,
        capture_output=True,
        env={"LC_ALL": "C", "PATH": f"{fake_bin}:/usr/bin:/bin", "TZ": "UTC"},
        timeout=10,
    )


def _resolved_readelf() -> Path:
    selected = shutil.which("readelf", path="/usr/bin:/bin")
    if selected is None:
        raise AssertionError("readelf is required by the ZRPF assurance image")
    return Path(os.path.realpath(selected))


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()
