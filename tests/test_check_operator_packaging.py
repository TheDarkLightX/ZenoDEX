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
    assert "single-command-local-testnet" in report["supported_operator_paths"]
    assert "native-launcher" in report["supported_operator_paths"]


def test_operator_packaging_check_rejects_missing_wrapper(tmp_path: Path) -> None:
    for relpath in (
        "scripts/install_zenodex.sh",
        "scripts/install_zenodex.ps1",
        "scripts/zenodex_testnet_demo.sh",
        "scripts/zenodex_testnet_demo.ps1",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "Dockerfile.hashlocked",
        "Dockerfile.operator-tools",
        ".dockerignore",
        ".docker/entrypoint.sh",
        ".docker/nginx.conf",
        ".docker/Dockerfile.tau-local",
        ".docker/nginx.local-testnet.conf.template",
        "docker-compose.local-testnet.yml",
        "docker-compose.two-node.yml",
        "docker-compose.multimachine.yml",
        "docker-compose.testnet-demo.yml",
        ".github/workflows/native-launcher.yml",
        ".github/workflows/release-integrity.yml",
        ".github/workflows/release-publish.yml",
        "tools/check_release_publication_workflow.py",
        "tools/build_release_sboms.py",
        "tools/dex-ui/src/lib/api.js",
        "tools/dex-ui/public/zenodex-config.json",
        "docs/DEPLOYMENT_QUICKSTART.md",
        "docs/LOCAL_TESTNET_QUICKSTART.md",
        "docs/NATIVE_INSTALLER_PLAN.md",
        "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
        "rust-runtime/Cargo.toml",
        "rust-runtime/crates/zenodex-launcher/Cargo.toml",
        "rust-runtime/crates/zenodex-launcher/src/main.rs",
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
    assert "would install /tmp/zenodex-bin/zenodex-local-testnet" in proc.stdout


def test_testnet_demo_script_dry_run() -> None:
    proc = subprocess.run(
        [str(ROOT / "scripts" / "zenodex_testnet_demo.sh"), "up", "--dry-run", "--ui-port", "3999"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 0
    assert "docker-compose.testnet-demo.yml" in proc.stdout
    assert "UI:       http://127.0.0.1:3999" in proc.stdout


def test_testnet_demo_script_dry_run_redacts_custom_token() -> None:
    proc = subprocess.run(
        [
            str(ROOT / "scripts" / "zenodex_testnet_demo.sh"),
            "up",
            "--dry-run",
            "--api-token",
            "super-sensitive-demo-token",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 0
    assert "super-sensitive-demo-token" not in proc.stdout
    assert "DEMO_API_TOKEN=\\<redacted\\>" in proc.stdout
