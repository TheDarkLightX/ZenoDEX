from __future__ import annotations

import hashlib
import inspect
from pathlib import Path

from experiments import global_economic_object_nullifier_reference_v2 as reference_v2
from tools.build_operator_release_bundle import ROOT as RELEASE_ROOT
from tools.build_operator_release_bundle import _collect_bundle_files

REPO_ROOT = Path(__file__).resolve().parents[2]
REFERENCE_MODULE_NAME = "global_economic_object_nullifier_reference_v2"
REFERENCE_CRATE_NAME = "zenodex-global-economic-object-nullifier-reference-v2"

V1_QUARANTINE_SHA256 = {
    "src/core/global_economic_proof_v1.py": (
        "f9ff27f3d346c2099ab3678ae87961cbc09653b6c641650ea0db0bf3bac23a50"
    ),
    "tests/core/test_global_settlement_abi_v1.py": (
        "4300f87b71a7c9d192ac1b2a5b5fbf62bb7bcb791dd1f824964d9214176c69aa"
    ),
    "tests/integration/test_global_economic_durable_publisher_v1.py": (
        "6156a7ebab7f26697844be8d059d6ee375d9d431bb189fe0fc33ff7f7e1f4d3c"
    ),
    "zk/global_settlement_abi_v1/src/economic_epoch_receipt_verification.rs": (
        "d7b526cf48809ad2544e65e356e5894f6b342cda606a660f6d054f86061505ec"
    ),
    # Re-pinned from 992caaf0... after the V1 perps route-test additions in
    # 0e71359d7, f4f18e7eb, and 07edc70c0. Those commits do not touch the
    # quarantined V2 reference implementation.
    "zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs": (
        "85ff856f3bb6f335f4635780443b436cd9c886c0ecacdf4c0d6b38a61b22623e"
    ),
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_reference_v2_is_absent_from_runtime_import_reexport_release_and_guest_surfaces() -> None:
    # Arrange
    scanned_roots = (
        REPO_ROOT / "src",
        REPO_ROOT / "config",
        REPO_ROOT / "generated",
        REPO_ROOT / "zk",
    )
    allowed = {
        REPO_ROOT / "experiments/global_economic_object_nullifier_reference_v2.py",
        REPO_ROOT / "zk/global_economic_object_nullifier_reference_v2/Cargo.toml",
        REPO_ROOT / "zk/global_economic_object_nullifier_reference_v2/Cargo.lock",
        REPO_ROOT / "zk/global_economic_object_nullifier_reference_v2/src/lib.rs",
        REPO_ROOT / "zk/global_economic_object_nullifier_reference_v2/tests/golden_vectors.rs",
    }

    # Act
    offenders: list[str] = []
    for root in scanned_roots:
        for path in root.rglob("*"):
            if path in allowed or not path.is_file() or path.suffix not in {".py", ".rs", ".toml", ".json"}:
                continue
            text = path.read_text(encoding="utf-8", errors="strict")
            if REFERENCE_MODULE_NAME in text or REFERENCE_CRATE_NAME in text:
                offenders.append(path.relative_to(REPO_ROOT).as_posix())

    # Assert
    assert offenders == []
    assert REFERENCE_MODULE_NAME not in (REPO_ROOT / "src/core/__init__.py").read_text(
        encoding="utf-8"
    )
    bundled = {item.relative_path for item in _collect_bundle_files(RELEASE_ROOT)}
    forbidden_release_artifacts = {
        "experiments/global_economic_object_nullifier_reference_v2.py",
        "experiments/render_global_economic_object_nullifier_reference_v2_golden.py",
    }
    assert bundled.isdisjoint(forbidden_release_artifacts)
    dockerignore = (REPO_ROOT / ".dockerignore").read_text(encoding="utf-8")
    assert "!experiments" not in dockerignore
    for dockerfile in REPO_ROOT.glob("Dockerfile*"):
        assert "COPY experiments" not in dockerfile.read_text(encoding="utf-8")


def test_reference_v2_api_and_digest_expose_no_authority_effect_commit_receipt_or_verified_type() -> None:
    # Arrange
    forbidden_symbol_parts = (
        "Authority",
        "Commit",
        "Effect",
        "Image",
        "Publisher",
        "Receipt",
        "Release",
        "StateRoot",
        "Verified",
    )

    # Act
    exported = tuple(reference_v2.__all__)
    source = inspect.getsource(reference_v2)

    # Assert
    assert all(
        name.startswith("Reference")
        or name.startswith("REFERENCE_")
        or name.startswith("MAX_REFERENCE")
        or name.startswith("CanonicalReference")
        or name.startswith("apply_reference")
        or name.startswith("canonical_reference")
        or name.startswith("reference_archive")
        for name in exported
    )
    assert not any(part in name for name in exported for part in forbidden_symbol_parts)
    assert "nullifier_set_root" not in source
    assert "state_root" not in source
    assert "production_authority" not in source


def test_reference_v2_rust_crate_is_nonpublishable_unmounted_and_not_a_dependency() -> None:
    # Arrange
    crate_root = REPO_ROOT / "zk/global_economic_object_nullifier_reference_v2"
    manifest = (crate_root / "Cargo.toml").read_text(encoding="utf-8")

    # Act
    dependent_manifests = []
    for path in REPO_ROOT.rglob("Cargo.toml"):
        if path == crate_root / "Cargo.toml":
            continue
        if REFERENCE_CRATE_NAME in path.read_text(encoding="utf-8"):
            dependent_manifests.append(path.relative_to(REPO_ROOT).as_posix())

    # Assert
    assert "publish = false" in manifest
    assert 'unsafe_code = "forbid"' in manifest
    assert dependent_manifests == []
    assert not (crate_root / "src/main.rs").exists()
    assert "[[bin]]" not in manifest
    assert "cdylib" not in manifest


def test_reference_v2_leaves_v1_quarantine_artifacts_byte_identical() -> None:
    # Arrange / Act
    observed = {
        path: _sha256(REPO_ROOT / path) for path in V1_QUARANTINE_SHA256
    }

    # Assert
    assert observed == V1_QUARANTINE_SHA256
