from __future__ import annotations

import gzip
import io
import json
import os
import subprocess
import sys
import tarfile
from pathlib import Path

import pytest

import tools.build_operator_release_bundle as release_builder
from tools.build_operator_release_bundle import (
    OperatorReleaseAdmissionRejectV1,
    build_operator_candidate_bundle,
    build_operator_release_bundle,
    main,
    verify_operator_candidate_manifest,
)


def _write(path: Path, text: str = "x\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _minimal_repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    for relpath in (
        "bin/zenoctl",
        "bin/zenodex-local-testnet",
        "bin/zenodex-public-testnet",
        "bin/zenodex-public-testnet.command",
        "scripts/install_zenodex.sh",
        "scripts/install_zenodex.ps1",
        "src/__init__.py",
        "src/integration/__init__.py",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "tools/autogovnext_governance_lane_assurance_manifest.json",
        "tools/build_app_root_jmt_evidence.py",
        "tools/build_autotrader_evidence.py",
        "tools/build_confidential_runtime_evidence.py",
        "tools/build_hardware_wallet_evidence.py",
        "tools/build_oracle_authority_evidence.py",
        "tools/build_operator_release_bundle.py",
        "tools/build_production_promotion_evidence_manifest.py",
        "tools/build_zk_wrapping_evidence_from_risc0_bundle.py",
        "tools/check_autogovnext_governance_lane_assurance_manifest.py",
        "tools/check_production_promotion_evidence_manifest.py",
        "tools/production_promotion_evidence_manifest.json",
        "tools/run_autogovnext_governance_lane_assurance_gate.sh",
        "tools/run_production_promotion_evidence_gate.sh",
        "config/deploy/local-dev.yaml",
        ".docker/entrypoint.sh",
        "Dockerfile",
        "Dockerfile.hashlocked",
        "Dockerfile.operator-tools",
        "Dockerfile.production-hashlocked",
        "docker-compose.yml",
        "docker-compose.local.yml",
        "docker-compose.local-testnet.yml",
        "docker-compose.two-node.yml",
        "docker-compose.multimachine.yml",
        "docker-compose.permissionless.yml",
        "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
        "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py",
        "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
        "generated/perp_python/perp_epoch_isolated_v2_ref.py",
        "generated/perp_python/perp_epoch_isolated_v3_ref.py",
        "packages/zeno-proof-client/package.json",
        "packages/zeno-proof-client/src/index.js",
        "requirements-core.lock.txt",
        "requirements-dev.lock.txt",
        "requirements-agents.lock.txt",
        "pyproject.toml",
        "pytest.ini",
        "README.md",
        "src/integration/production_promotion_evidence.py",
        "docs/DEPLOYMENT_QUICKSTART.md",
        "docs/DOCKER_HASHLOCKED_DEPLOYMENT.md",
        "docs/LOCAL_TESTNET_QUICKSTART.md",
        "docs/AUTOGOVNEXT_AND_ZENODEX_PRODUCTION_READINESS_PLAN_2026_06_10.md",
        "docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md",
        "docs/PUBLIC_TESTNET_V0_1_16.md",
        "docs/PERMISSIONLESS_HOSTING.md",
        "docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md",
        "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json",
        "docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md",
        "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
        "docs/assurance/README.md",
        "docs/claims_registry.yaml",
        "docs/tau_supported_runtime_contract.json",
    ):
        _write(root / relpath, f"{relpath}\n")
    _write(root / "internal/secret.txt", "do not package\n")
    _write(root / "tests/test_not_packaged.py", "do not package\n")
    _write(root / "tools/_secbin/trivy", "local downloaded scanner\n")
    _write(root / "tools/confidential_attestation_verifier_rust/target/debug/build-output", "local rust build\n")
    _write(root / "src/tau_specs/.tau_history", "local tau history\n")
    _write(root / "packages/zeno-proof-client/node_modules/.package-lock.json", "local node install\n")
    return root


def _archive_manifest(
    version: str,
    payload: bytes = b"x",
    *,
    path: str = "expected.txt",
) -> release_builder._CandidateManifestV1:
    import hashlib

    return release_builder._CandidateManifestV1(
        version=version,
        archive_sha256="0" * 64,
        files=(
            release_builder._CandidateManifestFileV1(
                path=path,
                size_bytes=len(payload),
                sha256=hashlib.sha256(payload).hexdigest(),
            ),
        ),
    )


def _add_regular_member(tar: tarfile.TarFile, name: str, payload: bytes = b"x") -> None:
    info = tarfile.TarInfo(name)
    info.size = len(payload)
    tar.addfile(info, io.BytesIO(payload))


def _bind_manifest_to_archive(manifest_path: Path, archive_path: Path) -> None:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["archive_sha256"] = release_builder._sha256_file(archive_path)
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _write_canonical_gzip(path: Path, payload: bytes) -> None:
    with path.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
            compressed.write(payload)


def _expected_parse_rejection(manifest_path: Path, error: str) -> dict[str, object]:
    return {
        "schema": "zenodex.operator_candidate_bundle.verify_report.v1",
        "ok": False,
        "status": "REJECTED_UNADMITTED_CANDIDATE",
        "errors": [error],
        "authority": "NONE",
        "release_eligible": False,
        "vm_gates_closed": [],
        "current_profile_id": "local-testnet-retired-bridge-quarantine-v1",
        "version": None,
        "archive_name": None,
        "archive_sha256": None,
        "manifest_sha256": release_builder._sha256_file(manifest_path),
    }


def test_current_profile_rejects_release_bundle_before_filesystem_effect(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "release-output"

    with pytest.raises(OperatorReleaseAdmissionRejectV1):
        build_operator_release_bundle(
            root=_minimal_repo(tmp_path),
            out_dir=out_dir,
            version="blocked",
        )

    assert not out_dir.exists()


def test_standalone_release_builder_rejects_without_pythonpath_bootstrap(
    tmp_path: Path,
) -> None:
    # Arrange.
    script = Path(__file__).resolve().parents[1] / "tools" / "build_operator_release_bundle.py"
    out_dir = tmp_path / "release-output"

    # Act.
    result = subprocess.run(
        [sys.executable, str(script), "build", "--out-dir", str(out_dir)],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    # Assert.
    assert result.returncode == 2
    report = json.loads(result.stdout)
    assert report["status"] == "blocked_current_profile"
    assert report["authority"] == "NONE"
    assert report["vm_gates_closed"] == []
    assert "ModuleNotFoundError" not in result.stderr
    assert not out_dir.exists()


def test_build_operator_candidate_bundle_writes_unadmitted_archive_and_manifest(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="test"
    )

    assert report["ok"] is True
    assert report["status"] == "UNADMITTED_CANDIDATE_NO_RELEASE_AUTHORITY"
    assert report["release_eligible"] is False
    assert report["authority"] == "NONE"
    assert report["vm_gates_closed"] == []
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    assert archive_path.is_file()
    assert manifest_path.is_file()

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    paths = {item["path"] for item in manifest["files"]}
    assert "bin/zenoctl" in paths
    assert "bin/zenodex-local-testnet" in paths
    assert "bin/zenodex-public-testnet" in paths
    assert "bin/zenodex-public-testnet.command" in paths
    assert "scripts/install_zenodex.sh" in paths
    assert "tools/zenoctl.py" in paths
    assert "tools/check_zeno_ledger_light_client_checkpoint.py" in paths
    assert "tools/autogovnext_governance_lane_assurance_manifest.json" in paths
    assert "tools/check_autogovnext_governance_lane_assurance_manifest.py" in paths
    assert "tools/run_autogovnext_governance_lane_assurance_gate.sh" in paths
    assert "tools/build_production_promotion_evidence_manifest.py" in paths
    assert "tools/check_production_promotion_evidence_manifest.py" in paths
    assert "tools/run_production_promotion_evidence_gate.sh" in paths
    assert "tools/build_operator_release_bundle.py" in paths
    assert "Dockerfile.hashlocked" in paths
    assert "docker-compose.local-testnet.yml" in paths
    assert "docs/LOCAL_TESTNET_QUICKSTART.md" in paths
    assert "docs/AUTOGOVNEXT_AND_ZENODEX_PRODUCTION_READINESS_PLAN_2026_06_10.md" in paths
    assert "docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md" in paths
    assert "docs/PUBLIC_TESTNET_V0_1_16.md" in paths
    assert "docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md" in paths
    assert "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json" in paths
    assert "docs/claims_registry.yaml" in paths
    assert "packages/zeno-proof-client/package.json" in paths
    assert "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py" in paths
    assert "docs/assurance/README.md" in paths
    assert all(not path.startswith("tests/") for path in paths)
    assert all("internal/" not in path for path in paths)
    assert all("_secbin/" not in path for path in paths)
    assert all("/target/" not in path for path in paths)
    assert all("node_modules/" not in path for path in paths)
    assert all(not path.endswith(".tau_history") for path in paths)

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)
    assert verify["ok"] is True


def test_operator_candidate_bundle_archive_members_are_prefixed(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="prefixed"
    )
    archive_path = Path(report["archive_path"])

    with tarfile.open(archive_path, "r:gz") as tar:
        names = [member.name for member in tar.getmembers() if member.isfile()]

    assert names
    assert all(name.startswith("zenodex-operator-candidate-prefixed/") for name in names)
    assert "zenodex-operator-candidate-prefixed/bin/zenoctl" in names
    assert "zenodex-operator-candidate-prefixed/bin/zenodex-local-testnet" in names
    assert "zenodex-operator-candidate-prefixed/bin/zenodex-public-testnet" in names


def test_operator_candidate_bundle_is_deterministic_for_same_checkout(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    out_a = tmp_path / "a"
    out_b = tmp_path / "b"
    report_a = build_operator_candidate_bundle(root=root, out_dir=out_a, version="stable")
    report_b = build_operator_candidate_bundle(root=root, out_dir=out_b, version="stable")

    assert report_a["archive_sha256"] == report_b["archive_sha256"]


def test_candidate_bundle_replaces_output_symlinks_without_following_them(
    tmp_path: Path,
) -> None:
    # Arrange: both predictable output names point at unrelated writable files.
    root = _minimal_repo(tmp_path)
    out_dir = tmp_path / "out"
    out_dir.mkdir()
    archive_path = out_dir / "zenodex-operator-candidate-symlink.tar.gz"
    manifest_path = out_dir / f"{archive_path.name}.manifest.json"
    archive_victim = tmp_path / "archive-victim"
    manifest_victim = tmp_path / "manifest-victim"
    archive_victim.write_bytes(b"archive victim must remain unchanged")
    manifest_victim.write_bytes(b"manifest victim must remain unchanged")
    archive_path.symlink_to(archive_victim)
    manifest_path.symlink_to(manifest_victim)

    # Act.
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=out_dir,
        version="symlink",
    )

    # Assert: atomic replacement replaced each directory entry, not its target.
    assert archive_victim.read_bytes() == b"archive victim must remain unchanged"
    assert manifest_victim.read_bytes() == b"manifest victim must remain unchanged"
    assert archive_path.is_file() and not archive_path.is_symlink()
    assert manifest_path.is_file() and not manifest_path.is_symlink()
    assert verify_operator_candidate_manifest(
        manifest_path=Path(report["manifest_path"])
    )["ok"] is True


def test_candidate_verifier_rejects_archive_path_swap_between_hash_and_parse(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange: prepare a byte-distinct gzip stream with the same tar payload.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="path-swap",
    )
    archive_path = Path(report["archive_path"])
    alternate_path = tmp_path / "alternate.tar.gz"
    original_bytes = archive_path.read_bytes()
    alternate_path.write_bytes(
        gzip.compress(gzip.decompress(original_bytes), mtime=1)
    )
    assert alternate_path.read_bytes() != original_bytes
    real_hash = release_builder._sha256_file_bounded

    def hash_then_replace(subject: object, limit: int) -> str:
        digest = real_hash(subject, limit)  # type: ignore[arg-type]
        alternate_path.replace(archive_path)
        return digest

    monkeypatch.setattr(
        release_builder,
        "_sha256_file_bounded",
        hash_then_replace,
    )

    # Act.
    verify = verify_operator_candidate_manifest(
        manifest_path=Path(report["manifest_path"])
    )

    # Assert.
    assert verify["ok"] is False
    assert verify["errors"] == ["archive path changed during verification"]


def test_candidate_verifier_rejects_same_inode_rewrite_after_snapshot_hash(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange: a hardlink permits an in-place rewrite without changing inode.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="inode-rewrite",
    )
    archive_path = Path(report["archive_path"])
    hardlink_path = tmp_path / "archive-hardlink.tar.gz"
    os.link(archive_path, hardlink_path)
    original_bytes = archive_path.read_bytes()
    alternate_bytes = gzip.compress(gzip.decompress(original_bytes), mtime=1)
    assert alternate_bytes != original_bytes
    real_hash = release_builder._sha256_file_bounded

    def hash_then_rewrite(subject: object, limit: int) -> str:
        digest = real_hash(subject, limit)  # type: ignore[arg-type]
        with hardlink_path.open("r+b") as rewritten:
            rewritten.write(alternate_bytes)
            rewritten.truncate()
        return digest

    monkeypatch.setattr(
        release_builder,
        "_sha256_file_bounded",
        hash_then_rewrite,
    )

    # Act.
    verify = verify_operator_candidate_manifest(
        manifest_path=Path(report["manifest_path"])
    )

    # Assert.
    assert verify["ok"] is False
    assert verify["errors"] == ["archive changed during verification"]


def test_candidate_builder_rejects_symlink_output_directory(tmp_path: Path) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    target = tmp_path / "output-target"
    target.mkdir()
    out_dir = tmp_path / "output-link"
    out_dir.symlink_to(target, target_is_directory=True)

    # Act and assert.
    with pytest.raises(ValueError, match="output directory must be a stable regular directory"):
        build_operator_candidate_bundle(root=root, out_dir=out_dir, version="out-link")

    assert not any(target.iterdir())


def test_candidate_builder_rejects_symlink_source_file(tmp_path: Path) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    external = tmp_path / "external-readme"
    external.write_bytes(b"external bytes must not enter the bundle")
    readme = root / "README.md"
    readme.unlink()
    readme.symlink_to(external)

    # Act and assert.
    with pytest.raises(ValueError, match="bundle source must be a stable regular file"):
        build_operator_candidate_bundle(
            root=root,
            out_dir=tmp_path / "out",
            version="source-link",
        )


def test_operator_candidate_bundle_verify_rejects_tampered_archive(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(root=root, out_dir=tmp_path / "out", version="tamper")
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    with archive_path.open("ab") as fh:
        fh.write(b"tamper")

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "archive_sha256 mismatch" in verify["errors"]


def test_operator_candidate_verifier_rejects_hash_bound_trailing_payload(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="trailing"
    )
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    with archive_path.open("ab") as fh:
        fh.write(b"ZENODEX-UNVERIFIED-TRAILING-PAYLOAD")
    _bind_manifest_to_archive(manifest_path, archive_path)

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "archive contains trailing data" in verify["errors"]


def test_operator_candidate_verifier_rejects_concatenated_gzip_member(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="concatenated"
    )
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    with archive_path.open("ab") as fh:
        fh.write(gzip.compress(b"", mtime=0))
    _bind_manifest_to_archive(manifest_path, archive_path)

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert verify["errors"] == ["archive contains trailing data"]


def test_operator_candidate_verifier_rejects_covert_tar_tail_inside_gzip(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="covert-tail"
    )
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    tar_payload = gzip.decompress(archive_path.read_bytes())
    _write_canonical_gzip(archive_path, tar_payload + b"covert-after-tar-end")
    _bind_manifest_to_archive(manifest_path, archive_path)

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert verify["errors"] == ["archive contains trailing data"]


def test_operator_candidate_verifier_rejects_release_looking_archive_override(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="rename"
    )
    release_looking = tmp_path / "zenodex-operator-release-rename.tar.gz"
    release_looking.write_bytes(Path(report["archive_path"]).read_bytes())

    verify = verify_operator_candidate_manifest(
        manifest_path=Path(report["manifest_path"]),
        archive_path=release_looking,
    )

    assert verify["ok"] is False
    assert verify["errors"] == ["archive basename does not match candidate manifest"]


def test_operator_candidate_verification_receipt_binds_subject_and_non_authority(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="receipt"
    )
    manifest_path = Path(report["manifest_path"])

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify == {
        "schema": "zenodex.operator_candidate_bundle.verify_report.v1",
        "ok": True,
        "status": "VERIFIED_UNADMITTED_CANDIDATE_NO_RELEASE_AUTHORITY",
        "errors": [],
        "authority": "NONE",
        "release_eligible": False,
        "vm_gates_closed": [],
        "current_profile_id": "local-testnet-retired-bridge-quarantine-v1",
        "version": "receipt",
        "archive_name": "zenodex-operator-candidate-receipt.tar.gz",
        "archive_sha256": release_builder._sha256_file(Path(report["archive_path"])),
        "manifest_sha256": release_builder._sha256_file(manifest_path),
    }


def test_operator_candidate_verifier_rejects_symlink_manifest(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="manifest-link"
    )
    manifest_path = Path(report["manifest_path"])
    manifest_link = tmp_path / "manifest-link.json"
    manifest_link.symlink_to(manifest_path)

    verify = verify_operator_candidate_manifest(manifest_path=manifest_link)

    assert verify["ok"] is False
    assert verify["errors"] == ["manifest cannot be read as a stable regular file"]


def test_operator_candidate_verifier_rejects_manifest_path_swap_during_read(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="manifest-swap"
    )
    manifest_path = Path(report["manifest_path"])
    alternate = tmp_path / "alternate-manifest.json"
    alternate.write_text("{}\n", encoding="utf-8")
    real_status = release_builder._opened_path_status
    swapped = False

    def swap_then_check(path: Path, file: object, identity: object) -> str:
        nonlocal swapped
        if path == manifest_path and not swapped:
            alternate.replace(manifest_path)
            swapped = True
        return real_status(path, file, identity)  # type: ignore[arg-type]

    monkeypatch.setattr(release_builder, "_opened_path_status", swap_then_check)

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert verify["errors"] == ["manifest cannot be read as a stable regular file"]


def test_archive_member_verifier_rejects_duplicate_regular_member(tmp_path: Path) -> None:
    # Arrange.
    archive = tmp_path / "duplicate.tar.gz"
    prefix = "zenodex-operator-candidate-duplicate/"
    with tarfile.open(archive, "w:gz") as tar:
        _add_regular_member(tar, f"{prefix}expected.txt")
        _add_regular_member(tar, f"{prefix}expected.txt")

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=_archive_manifest("duplicate"),
    )

    # Assert.
    assert f"archive contains duplicate member: {prefix}expected.txt" in errors
    assert "archive member count differs from manifest" in errors


def test_archive_member_verifier_rejects_canonical_alias_duplicate(
    tmp_path: Path,
) -> None:
    # Arrange: both names address the same canonical path.
    archive = tmp_path / "canonical-duplicate.tar.gz"
    prefix = "zenodex-operator-candidate-canonical/"
    manifest = _archive_manifest("canonical", path="collision/value")
    with tarfile.open(archive, "w:gz") as tar:
        _add_regular_member(tar, f"{prefix}collision/value")
        _add_regular_member(tar, f"{prefix}collision/./value")

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=manifest,
    )

    # Assert.
    assert "archive contains non-canonical member path: collision/./value" in errors


def test_archive_member_verifier_rejects_noncanonical_member_order(
    tmp_path: Path,
) -> None:
    # Arrange.
    payload_a = b"a"
    payload_b = b"b"
    manifest = release_builder._CandidateManifestV1(
        version="order",
        archive_sha256="0" * 64,
        files=(
            _archive_manifest("order", payload_a, path="a.txt").files[0],
            _archive_manifest("order", payload_b, path="b.txt").files[0],
        ),
    )
    archive = tmp_path / "order.tar.gz"
    prefix = "zenodex-operator-candidate-order/"
    with tarfile.open(archive, "w:gz") as tar:
        _add_regular_member(tar, f"{prefix}b.txt", payload_b)
        _add_regular_member(tar, f"{prefix}a.txt", payload_a)

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=manifest,
    )

    # Assert.
    assert "archive members are not in canonical manifest order" in errors


def test_archive_member_verifier_rejects_noncanonical_metadata(tmp_path: Path) -> None:
    # Arrange.
    archive = tmp_path / "metadata.tar.gz"
    member_name = "zenodex-operator-candidate-metadata/expected.txt"
    with tarfile.open(archive, "w:gz") as tar:
        info = tarfile.TarInfo(member_name)
        info.size = 1
        info.mode = 0o777
        info.uid = 456
        info.gid = 789
        info.uname = "mallory"
        info.gname = "mallory"
        info.mtime = 123
        tar.addfile(info, io.BytesIO(b"x"))

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=_archive_manifest("metadata"),
    )

    # Assert.
    assert "archive member metadata is non-canonical: expected.txt" in errors


def test_archive_member_verifier_rejects_nonregular_member(tmp_path: Path) -> None:
    # Arrange.
    archive = tmp_path / "nonregular.tar.gz"
    member_name = "zenodex-operator-candidate-nonregular/../../outside"
    with tarfile.open(archive, "w:gz") as tar:
        info = tarfile.TarInfo(member_name)
        info.type = tarfile.SYMTYPE
        info.linkname = "../../outside"
        tar.addfile(info)

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=_archive_manifest("nonregular"),
    )

    # Assert.
    assert f"archive contains non-regular member: {member_name}" in errors
    assert "archive missing manifest file: expected.txt" in errors


def test_archive_member_verifier_rejects_before_read_above_resource_ceiling(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange.
    archive = tmp_path / "bounded.tar.gz"
    prefix = "zenodex-operator-candidate-bounded/"
    with tarfile.open(archive, "w:gz") as tar:
        _add_regular_member(tar, f"{prefix}expected.txt")
    monkeypatch.setattr(release_builder, "MAX_ARCHIVE_MEMBER_BYTES_V1", 0)

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=_archive_manifest("bounded"),
    )

    # Assert.
    assert "archive member exceeds resource ceiling: expected.txt" in errors


def test_archive_member_verifier_stops_before_advancing_past_oversize_member(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange: advancing the parser would consume the rejected member body.
    class OversizeMember:
        name = "zenodex-operator-candidate-bounded/expected.txt"
        size = 2

        @staticmethod
        def isfile() -> bool:
            return True

    class StopBeforeBodyArchive:
        def __enter__(self) -> StopBeforeBodyArchive:
            return self

        def __exit__(self, *_args: object) -> None:
            return None

        def __iter__(self) -> StopBeforeBodyArchive:
            return self

        def __next__(self) -> OversizeMember:
            if hasattr(self, "_yielded"):
                pytest.fail("archive parser advanced into an oversize member body")
            self._yielded = True
            return OversizeMember()

    monkeypatch.setattr(release_builder, "MAX_ARCHIVE_MEMBER_BYTES_V1", 1)
    archive = tmp_path / "bounded.tar.gz"
    with tarfile.open(archive, "w:gz"):
        pass
    monkeypatch.setattr(
        release_builder.tarfile,
        "open",
        lambda *_args, **_kwargs: StopBeforeBodyArchive(),
    )

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=_archive_manifest("bounded", b"xx"),
    )

    # Assert.
    assert errors == ["archive member exceeds resource ceiling: expected.txt"]


def test_operator_candidate_bundle_verify_rejects_unsafe_version_without_throwing(
    tmp_path: Path,
) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="safe",
    )
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["version"] = "../../../escaped"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["ok"] is False
    assert "manifest version is invalid" in verify["errors"]


def test_operator_candidate_bundle_verify_rejects_non_list_files_without_throwing(
    tmp_path: Path,
) -> None:
    # Arrange.
    manifest_path = tmp_path / "hostile.manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "archive_name": "zenodex-operator-candidate-hostile.tar.gz",
                "archive_sha256": "0" * 64,
                "file_count": 1,
                "files": 1,
                "schema": release_builder.SCHEMA,
                "total_size_bytes": 0,
                "version": "hostile",
            }
        ),
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["ok"] is False
    assert "manifest files must be a non-empty list" in verify["errors"]
    assert "manifest file_count mismatch" in verify["errors"]


def test_operator_candidate_bundle_verify_rejects_lone_surrogate_path_without_throwing(
    tmp_path: Path,
) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="surrogate",
    )
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"][0]["path"] = "\ud800"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["ok"] is False
    assert "files[0].path is unsafe or non-canonical" in verify["errors"]


@pytest.mark.parametrize(
    "hostile_path",
    (
        "docs/right-to-left-\u202ereport.md",
        "docs/decomposed-e\u0301.md",
    ),
)
def test_operator_candidate_bundle_verify_rejects_unicode_path_ambiguity(
    tmp_path: Path,
    hostile_path: str,
) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="unicode-path",
    )
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"][0]["path"] = hostile_path
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["ok"] is False
    assert "files[0].path is unsafe or non-canonical" in verify["errors"]


def test_operator_candidate_bundle_verify_rejects_noncanonical_manifest_row_order(
    tmp_path: Path,
) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="manifest-order",
    )
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"].reverse()
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["ok"] is False
    assert "manifest file rows are not in canonical order" in verify["errors"]


def test_operator_candidate_bundle_verify_rejects_excessive_json_nesting(
    tmp_path: Path,
) -> None:
    # Arrange.
    manifest_path = tmp_path / "deep.manifest.json"
    manifest_path.write_text("[" * 10_000 + "0" + "]" * 10_000, encoding="utf-8")

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify == _expected_parse_rejection(
        manifest_path,
        "manifest cannot be parsed within structural resource ceiling",
    )


def test_operator_candidate_bundle_verify_rejects_duplicate_manifest_key(
    tmp_path: Path,
) -> None:
    # Arrange.
    manifest_path = tmp_path / "duplicate-key.manifest.json"
    manifest_path.write_text(
        '{"schema":"first","schema":"second"}',
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify == _expected_parse_rejection(
        manifest_path,
        "manifest cannot be parsed within resource ceiling",
    )


def test_operator_candidate_bundle_verify_rejects_manifest_above_byte_ceiling(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange.
    manifest_path = tmp_path / "oversize.manifest.json"
    manifest_path.write_text("{}", encoding="utf-8")
    monkeypatch.setattr(release_builder, "MAX_MANIFEST_BYTES_V1", 1)

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["errors"] == ["manifest cannot be parsed within resource ceiling"]


def test_operator_candidate_bundle_verify_rejects_archive_above_compressed_ceiling(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="compressed-ceiling",
    )
    monkeypatch.setattr(release_builder, "MAX_ARCHIVE_COMPRESSED_BYTES_V1", 1)
    monkeypatch.setattr(
        release_builder,
        "_verify_archive_members",
        lambda **_kwargs: pytest.fail("archive parser must not run above compressed ceiling"),
    )

    # Act.
    verify = verify_operator_candidate_manifest(
        manifest_path=Path(report["manifest_path"]),
    )

    # Assert.
    assert verify["errors"] == ["archive cannot be read within resource ceiling"]


def test_archive_member_verifier_rejects_uncompressed_stream_above_ceiling(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange.
    payload = b"x" * 2048
    archive = tmp_path / "decompression-ceiling.tar.gz"
    prefix = "zenodex-operator-candidate-decompression-ceiling/"
    with tarfile.open(archive, "w:gz") as tar:
        _add_regular_member(tar, f"{prefix}expected.txt", payload)
    monkeypatch.setattr(release_builder, "MAX_ARCHIVE_UNCOMPRESSED_BYTES_V1", 1024)

    # Act.
    errors = release_builder._verify_archive_members(
        archive=archive,
        manifest=_archive_manifest("decompression-ceiling", payload),
    )

    # Assert.
    assert errors[-1] == "archive decompression exceeds resource ceiling"


def test_operator_candidate_bundle_verify_rejects_hash_matching_invalid_gzip(
    tmp_path: Path,
) -> None:
    # Arrange.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="invalid-gzip",
    )
    manifest_path = Path(report["manifest_path"])
    archive_path = Path(report["archive_path"])
    archive_path.write_bytes(b"not a gzip archive")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["archive_sha256"] = release_builder._sha256_file(archive_path)
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["ok"] is False
    assert verify["errors"] == ["archive gzip header is non-canonical"]


def test_operator_candidate_bundle_verify_rejects_noncanonical_gzip_header(
    tmp_path: Path,
) -> None:
    # Arrange: recompress the exact tar payload with a nonzero gzip timestamp.
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root,
        out_dir=tmp_path / "out",
        version="gzip-header",
    )
    manifest_path = Path(report["manifest_path"])
    archive_path = Path(report["archive_path"])
    archive_path.write_bytes(
        gzip.compress(gzip.decompress(archive_path.read_bytes()), mtime=1)
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["archive_sha256"] = release_builder._sha256_file(archive_path)
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    # Act.
    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Assert.
    assert verify["ok"] is False
    assert verify["errors"] == ["archive gzip header is non-canonical"]


def test_operator_candidate_bundle_verify_rejects_invalid_file_size(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(root=root, out_dir=tmp_path / "out", version="bad-size")
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"][0]["size_bytes"] = True
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    # Review finding (grade B -> A-): the verifier compared a maybe-missing
    # JSON field directly against zero. This now rejects bool/missing/negative
    # sizes through an explicit type narrow before archive-member checks.
    assert verify["ok"] is False
    assert any(error.startswith("invalid file size:") for error in verify["errors"])


def test_operator_candidate_bundle_verify_rejects_bool_file_count(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="bad-file-count"
    )
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"] = manifest["files"][:1]
    manifest["file_count"] = True
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "manifest file_count mismatch" in verify["errors"]


def test_operator_candidate_bundle_verify_rejects_missing_required_operator_file(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="missing-required"
    )
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"] = [
        item
        for item in manifest["files"]
        if item["path"] != "docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md"
    ]
    manifest["file_count"] = len(manifest["files"])
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert (
        "missing required operator file: docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md"
        in verify["errors"]
    )


def test_operator_candidate_bundle_verify_rejects_missing_autogovnext_gate(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_candidate_bundle(
        root=root, out_dir=tmp_path / "out", version="missing-autogov"
    )
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"] = [
        item
        for item in manifest["files"]
        if item["path"] != "tools/run_autogovnext_governance_lane_assurance_gate.sh"
    ]
    manifest["file_count"] = len(manifest["files"])
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_candidate_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert (
        "missing required operator file: tools/run_autogovnext_governance_lane_assurance_gate.sh"
        in verify["errors"]
    )


def test_operator_bundle_cli_blocks_release_and_verifies_unadmitted_candidate(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    root = _minimal_repo(tmp_path)
    code = main(["build", "--repo-root", str(root), "--out-dir", str(tmp_path / "out"), "--version", "cli"])
    blocked = json.loads(capsys.readouterr().out)
    assert code == 2
    assert blocked["ok"] is False
    assert blocked["status"] == "blocked_current_profile"
    assert blocked["current_release_eligible"] is False
    assert blocked["authority"] == "NONE"
    assert blocked["vm_gates_closed"] == []

    code = main(
        [
            "candidate",
            "--repo-root",
            str(root),
            "--out-dir",
            str(tmp_path / "candidate"),
            "--version",
            "cli",
        ]
    )
    build_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert build_out["status"] == "UNADMITTED_CANDIDATE_NO_RELEASE_AUTHORITY"

    code = main(["verify", "--manifest", build_out["manifest_path"]])
    verify_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert verify_out["ok"] is True
