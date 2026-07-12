from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

from tools.check_zeno_oracle_rc_package import check_package

ROOT = Path(__file__).resolve().parents[1]


def _build_package(version: str) -> tuple[Path, Path, Path]:
    proc = subprocess.run(
        ["bash", "scripts/package_zeno_oracle_rc.sh", version],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    return (
        ROOT / "dist" / version,
        ROOT / "dist" / f"{version}.receipt.json",
        ROOT / "dist" / f"{version}.sig",
    )


def test_check_zeno_oracle_rc_package_accepts_built_devnet_bundle() -> None:
    package_dir, receipt_path, sig_path = _build_package("zeno-oracle-package-check-pytest-rc")

    report = check_package(package_dir=package_dir, receipt_path=receipt_path, sig_path=sig_path)

    assert report["schema"] == "zenodex.oracle.rc_package_check.v1"
    assert report["status"] == "accepted"
    assert report["ok"] is True
    assert report["manifest"]["entrypoint"] == "bin/zenodex-oracle"
    assert report["manifest"]["required_file_count"] >= 10
    assert report["receipt_checked"] is True
    assert report["signature_checked"] is True
    assert report["errors"] == []
    assert (package_dir / ".github" / "workflows" / "zeno-oracle-mvp.yml").is_file()
    assert (package_dir / "docs" / "claims_registry.yaml").is_file()
    assert (package_dir / "scripts" / "check_zeno_oracle_rc_bundle.sh").is_file()
    assert (package_dir / "src" / "state" / "canonical.py").is_file()
    assert (package_dir / "tests" / "integration" / "test_dex_snapshot.py").is_file()
    assert (package_dir / "formal" / "tla" / "OracleRecoveryLifecycle.tla").is_file()
    assert (package_dir / "generated" / "perp_python" / "perp_epoch_clearinghouse_2p_v0_1_ref.py").is_file()
    assert (package_dir / "lean-mathlib" / "Proofs" / "ZenoOracleMathWitness.lean").is_file()
    assert (package_dir / "tools" / "check_claims_registry.py").is_file()
    assert (package_dir / "tools" / "check_cross_module_oracle_split_brain_v1.py").is_file()
    assert (package_dir / "tools" / "check_zeno_oracle_rc_package.py").is_file()
    assert (package_dir / "tools" / "check_disaster_obligation_certificate.py").is_file()
    assert (package_dir / "tools" / "check_zeno_oracle_disaster_frontier.py").is_file()
    assert (package_dir / "tools" / "check_zeno_oracle_frontier_obligation_projection.py").is_file()
    assert (package_dir / "tools" / "check_zeno_oracle_goal_completion_audit.py").is_file()
    assert (package_dir / "tools" / "check_zeno_oracle_live_economics_policy.py").is_file()
    assert (package_dir / "tools" / "check_zenoproof_production_governance_policy.py").is_file()
    assert (package_dir / "tools" / "zeno_oracle_disaster_class_corpus.py").is_file()
    assert (package_dir / "tools" / "zeno_oracle_esso_zusd_recovery_replay.py").is_file()
    assert (package_dir / "tools" / "zeno_oracle_tla_recovery_replay.py").is_file()
    assert (package_dir / "tools" / "zeno_oracle_ltlf_recovery_replay.py").is_file()
    assert (package_dir / "tools" / "zeno_oracle_o3_receipt_flow_replay.py").is_file()
    assert (package_dir / "tools" / "zeno_oracle_disaster_obligation_certificate_manifest.json").is_file()
    assert (package_dir / "tools" / "zeno_oracle_math_witness_sweep.jl").is_file()
    assert (package_dir / "tools" / "zenodex_oracle_reporter_economics_replay.py").is_file()
    assert (package_dir / "tools" / "zenodex_oracle_reporter_token_settlement_replay.py").is_file()
    assert (package_dir / "tools" / "macos_scout" / "build_witness_space_receipt.py").is_file()
    assert (package_dir / "tools" / "macos_scout" / "check_scout_regression_gate.py").is_file()
    assert (package_dir / "tools" / "macos_scout" / "witness_space_atlas.json").is_file()
    assert (package_dir / "tools" / "macos_scout" / "scout_regression_manifest.json").is_file()


def test_check_zeno_oracle_rc_package_rejects_manifest_hash_drift(tmp_path: Path) -> None:
    package_dir, receipt_path, sig_path = _build_package("zeno-oracle-package-drift-pytest-rc")
    copied = tmp_path / "package"
    subprocess.run(["cp", "-R", str(package_dir), str(copied)], check=True)
    manifest_path = copied / "ZEN_ORACLE_RC_MANIFEST.json"
    manifest: dict[str, Any] = json.loads(manifest_path.read_text(encoding="utf-8"))
    for row in manifest["files"]:
        if row["path"] == "docs/ZENO_ORACLE_DEVNET_ALPHA.md":
            row["sha256"] = "0" * 64
            break
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    report = check_package(package_dir=copied, receipt_path=receipt_path, sig_path=sig_path)

    assert report["status"] == "rejected"
    assert "manifest_file_sha256_mismatch:docs/ZENO_ORACLE_DEVNET_ALPHA.md" in report["errors"]


def test_check_zeno_oracle_rc_package_rejects_missing_claims_registry_evidence(tmp_path: Path) -> None:
    package_dir, receipt_path, sig_path = _build_package("zeno-oracle-package-claim-evidence-pytest-rc")
    copied = tmp_path / "package"
    subprocess.run(["cp", "-R", str(package_dir), str(copied)], check=True)
    missing = copied / "tests" / "integration" / "test_dex_snapshot.py"
    missing.unlink()

    report = check_package(package_dir=copied, receipt_path=receipt_path, sig_path=sig_path)

    assert report["status"] == "rejected"
    assert "manifest_file_missing_on_disk:tests/integration/test_dex_snapshot.py" in report["errors"]
    assert "claims_registry_file_missing_on_disk:tests/integration/test_dex_snapshot.py" in report["errors"]


def test_check_zeno_oracle_rc_package_rejects_receipt_for_different_package() -> None:
    _, receipt_path, sig_path = _build_package("zeno-oracle-package-auth-a-pytest-rc")
    other_package_dir, _, _ = _build_package("zeno-oracle-package-auth-b-pytest-rc")

    report = check_package(
        package_dir=other_package_dir,
        receipt_path=receipt_path,
        sig_path=sig_path,
    )

    assert report["status"] == "rejected"
    assert any(
        error.startswith("authenticated_package_file_sha256_mismatch:")
        for error in report["errors"]
    )


def test_check_zeno_oracle_rc_package_cli_rejects_missing_authentication() -> None:
    package_dir, _, _ = _build_package("zeno-oracle-package-cli-auth-pytest-rc")

    proc = subprocess.run(
        [
            "python3",
            "tools/check_zeno_oracle_rc_package.py",
            "--package-dir",
            str(package_dir),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stdout)
    assert report["status"] == "rejected"
    assert report["authenticated_mode"] is True
    assert "receipt_and_sig_required_unless_local_only" in report["errors"]


def test_check_zeno_oracle_rc_package_cli_allows_explicit_local_only_manifest_check() -> None:
    package_dir, _, _ = _build_package("zeno-oracle-package-cli-local-pytest-rc")

    proc = subprocess.run(
        [
            "python3",
            "tools/check_zeno_oracle_rc_package.py",
            "--package-dir",
            str(package_dir),
            "--local-only-manifest-check",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0
    report = json.loads(proc.stdout)
    assert report["status"] == "accepted"
    assert report["authenticated_mode"] is False
    assert report["receipt_checked"] is False
    assert report["signature_checked"] is False
    assert report["errors"] == []
