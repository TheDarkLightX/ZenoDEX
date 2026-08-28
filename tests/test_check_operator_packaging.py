from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

import tools.check_operator_packaging as packaging_module
from tools.check_operator_packaging import check_operator_packaging, main

ROOT = Path(__file__).resolve().parents[1]


def test_operator_packaging_integrity_passes_while_current_release_admission_stays_blocked() -> None:
    report = check_operator_packaging(ROOT)

    assert report["schema"] == "zenodex/operator_packaging_readiness/v1"
    assert report["packaging_integrity_ok"] is True
    assert report["ok"] is False
    assert report["status"] == "blocked_current_profile"
    assert report["current_release_eligible"] is False
    assert report["authority"] == "NONE"
    assert report["vm_gates_closed"] == []
    assert report["repository_controls_verified"] is False
    assert report["external_release_blockers"] == [
        packaging_module.HISTORICAL_RELEASE_REF_BLOCKER_V1
    ]
    assert "light-client-checkpoint-verifier" in report["supported_operator_paths"]
    assert "single-command-local-testnet" in report["supported_operator_paths"]
    assert "single-click-public-testnet" not in report["supported_operator_paths"]
    assert "single-click-public-testnet" in report["retained_blocked_operator_paths"]


def test_restored_public_testnet_support_claim_mutant_fails_packaging_integrity(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        packaging_module,
        "SUPPORTED_OPERATOR_PATHS_V1",
        (*packaging_module.SUPPORTED_OPERATOR_PATHS_V1, "single-click-public-testnet"),
    )

    report = check_operator_packaging(ROOT)

    assert report["packaging_integrity_ok"] is False
    assert report["ok"] is False
    assert any(
        "retained blocked operator paths advertised as supported" in error
        for error in report["errors"]
    )


def test_release_workflow_with_restored_publication_capability_mutant_fails_quarantine_gate(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / ".github/workflows/release-integrity.yml"
    workflow.parent.mkdir(parents=True)
    source = (ROOT / ".github/workflows/release-integrity.yml").read_text(encoding="utf-8")
    workflow.write_text(source + "\npermissions:\n  contents: write\n", encoding="utf-8")
    checks: list[dict[str, object]] = []
    errors: list[str] = []

    packaging_module._check_release_integrity_blocks_publication(
        tmp_path, checks, errors
    )

    assert any("publication capability" in error for error in errors)
    assert any(
        check["id"] == "release_integrity_omits:contents: write"
        and check["ok"] is False
        for check in checks
    )


def test_operator_packaging_check_rejects_missing_wrapper(tmp_path: Path) -> None:
    for relpath in (
        "scripts/install_zenodex.sh",
        "scripts/install_zenodex.ps1",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "tools/build_operator_release_bundle.py",
        "Dockerfile.hashlocked",
        "Dockerfile.operator-tools",
        ".docker/Dockerfile.tau-local",
        ".docker/nginx.local-testnet.conf.template",
        "docker-compose.local-testnet.yml",
        "docker-compose.two-node.yml",
        "docker-compose.multimachine.yml",
        ".github/workflows/release-integrity.yml",
        "docs/DEPLOYMENT_QUICKSTART.md",
        "docs/LOCAL_TESTNET_QUICKSTART.md",
        "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
    ):
        src = ROOT / relpath
        dst = tmp_path / relpath
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)

    report = check_operator_packaging(tmp_path)

    assert report["ok"] is False
    assert "missing required packaging file: bin/zenoctl" in report["errors"]


def test_operator_packaging_cli_outputs_json(capsys) -> None:
    code = main(["--repo-root", str(ROOT)])
    out = capsys.readouterr().out

    assert code == 1
    assert "zenodex/operator_packaging_readiness/v1" in out


def test_posix_installer_dry_run() -> None:
    proc = subprocess.run(
        [str(ROOT / "scripts" / "install_zenodex.sh"), "--dry-run", "--bin-dir", "/tmp/zenodex-bin"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 0
    assert "would install /tmp/zenodex-bin/zenoctl" in proc.stdout
    assert "would install /tmp/zenodex-bin/zenodex-node" in proc.stdout
    assert "would install /tmp/zenodex-bin/zenodex-local-testnet" in proc.stdout
