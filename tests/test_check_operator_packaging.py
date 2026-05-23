from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

from tools.check_operator_packaging import check_operator_packaging, main


ROOT = Path(__file__).resolve().parents[1]


def test_operator_packaging_check_passes_current_checkout() -> None:
    report = check_operator_packaging(ROOT)

    assert report["schema"] == "zenodex.operator_packaging_readiness.v0"
    assert report["ok"] is True
    assert "light-client-checkpoint-verifier" in report["supported_operator_paths"]


def test_operator_packaging_check_rejects_missing_wrapper(tmp_path: Path) -> None:
    for relpath in (
        "scripts/install_zenodex.sh",
        "scripts/install_zenodex.ps1",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "Dockerfile.hashlocked",
        "Dockerfile.operator-tools",
        "docker-compose.two-node.yml",
        "docker-compose.multimachine.yml",
        "docs/DEPLOYMENT_QUICKSTART.md",
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

    assert code == 0
    assert "zenodex.operator_packaging_readiness.v0" in out


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
