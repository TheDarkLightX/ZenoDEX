from __future__ import annotations

import copy
import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_proof_toolchain_lock", ROOT / "tools/check_proof_toolchain_lock.py"
)
assert SPEC is not None and SPEC.loader is not None
check_proof_toolchain_lock = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check_proof_toolchain_lock
SPEC.loader.exec_module(check_proof_toolchain_lock)


def test_repo_proof_toolchain_lock_check_passes() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)

    assert report["ok"], report["errors"]
    assert report["lock_hash"].startswith("0x")
    assert report["lock_hash"] != "0x" + "00" * 32
    assert {"python", "docker", "lean", "rust-risc0", "rust-tee"} <= set(report["groups"])
    assert "zk/state_proof_risc0/Cargo.lock" in report["paths"]
    assert "zk/state_proof_risc0/patches/ark-relations-0.5.1/Cargo.toml" in report["paths"]
    assert "lean-mathlib/lean-toolchain" in report["paths"]
    assert "lean-mathlib/Proofs.lean" in report["paths"]
    assert "lean-mathlib/Proofs/ZenoLedgerZkTeeProofComposition.lean" in report["paths"]
    assert "lean-mathlib/proof_receipts/zeno_ledger_zk_tee_proof_composition_v1.md" in report["paths"]
    assert "Dockerfile" in report["paths"]


def test_manifest_rejects_missing_risc0_lock_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"] = [
        entry
        for entry in manifest["files"]
        if entry["path"] != "zk/state_proof_risc0/Cargo.lock"
    ]

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert "missing lock paths: zk/state_proof_risc0/Cargo.lock" in validation["errors"]


def test_manifest_rejects_unexpected_toolchain_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    extra = dict(manifest["files"][0])
    extra["path"] = "requirements.txt"
    manifest["files"].append(extra)

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("requirements.txt" in error for error in validation["errors"])


def test_manifest_rejects_duplicate_toolchain_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"].append(dict(manifest["files"][0]))

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("is duplicated" in error for error in validation["errors"])


def test_manifest_rejects_wrong_group_for_toolchain_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"][0]["group"] = "docker"

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("group mismatch" in error for error in validation["errors"])


def test_manifest_rejects_malformed_sha() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"][0]["sha256"] = "not-a-sha"

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert "files[0].sha256 must be sha256:<64 hex>" in validation["errors"]


def test_manifest_rejects_sha_mismatch() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"][0]["sha256"] = "sha256:" + "1" * 64

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("sha256 mismatch" in error for error in validation["errors"])
