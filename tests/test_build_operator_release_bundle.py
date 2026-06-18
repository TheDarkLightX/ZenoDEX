from __future__ import annotations

import json
import tarfile
from pathlib import Path

from tools.build_operator_release_bundle import (
    build_operator_release_bundle,
    main,
    verify_operator_release_manifest,
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


def test_build_operator_release_bundle_writes_archive_and_manifest(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="test")

    assert report["ok"] is True
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

    verify = verify_operator_release_manifest(manifest_path=manifest_path)
    assert verify["ok"] is True


def test_operator_release_bundle_archive_members_are_prefixed(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="prefixed")
    archive_path = Path(report["archive_path"])

    with tarfile.open(archive_path, "r:gz") as tar:
        names = [member.name for member in tar.getmembers() if member.isfile()]

    assert names
    assert all(name.startswith("zenodex-operator-prefixed/") for name in names)
    assert "zenodex-operator-prefixed/bin/zenoctl" in names
    assert "zenodex-operator-prefixed/bin/zenodex-local-testnet" in names
    assert "zenodex-operator-prefixed/bin/zenodex-public-testnet" in names


def test_operator_release_bundle_is_deterministic_for_same_checkout(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    out_a = tmp_path / "a"
    out_b = tmp_path / "b"
    report_a = build_operator_release_bundle(root=root, out_dir=out_a, version="stable")
    report_b = build_operator_release_bundle(root=root, out_dir=out_b, version="stable")

    assert report_a["archive_sha256"] == report_b["archive_sha256"]


def test_operator_release_bundle_verify_rejects_tampered_archive(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="tamper")
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    with archive_path.open("ab") as fh:
        fh.write(b"tamper")

    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "archive_sha256 mismatch" in verify["errors"]


def test_operator_release_bundle_verify_rejects_invalid_file_size(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="bad-size")
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"][0]["size_bytes"] = True
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    # Review finding (grade B -> A-): the verifier compared a maybe-missing
    # JSON field directly against zero. This now rejects bool/missing/negative
    # sizes through an explicit type narrow before archive-member checks.
    assert verify["ok"] is False
    assert any(error.startswith("invalid file size:") for error in verify["errors"])


def test_operator_release_bundle_verify_rejects_bool_file_count(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="bad-file-count")
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"] = manifest["files"][:1]
    manifest["file_count"] = True
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "manifest file_count mismatch" in verify["errors"]


def test_operator_release_bundle_verify_rejects_missing_required_operator_file(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="missing-required")
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"] = [
        item
        for item in manifest["files"]
        if item["path"] != "docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md"
    ]
    manifest["file_count"] = len(manifest["files"])
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert (
        "missing required operator file: docs/PRODUCTION_PROMOTION_EVIDENCE_REQUIREMENTS.md"
        in verify["errors"]
    )


def test_operator_release_bundle_verify_rejects_missing_autogovnext_gate(
    tmp_path: Path,
) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="missing-autogov")
    manifest_path = Path(report["manifest_path"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"] = [
        item
        for item in manifest["files"]
        if item["path"] != "tools/run_autogovnext_governance_lane_assurance_gate.sh"
    ]
    manifest["file_count"] = len(manifest["files"])
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert (
        "missing required operator file: tools/run_autogovnext_governance_lane_assurance_gate.sh"
        in verify["errors"]
    )


def test_operator_release_bundle_cli_build_and_verify(tmp_path: Path, capsys) -> None:
    root = _minimal_repo(tmp_path)
    code = main(["build", "--repo-root", str(root), "--out-dir", str(tmp_path / "out"), "--version", "cli"])
    build_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert build_out["ok"] is True

    code = main(["verify", "--manifest", build_out["manifest_path"]])
    verify_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert verify_out["ok"] is True
