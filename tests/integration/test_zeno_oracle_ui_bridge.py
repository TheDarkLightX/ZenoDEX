from __future__ import annotations

import json
import os
import shutil
import socket
import subprocess
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import urlopen

import pytest

from src.integration.zeno_key_manager import KeyRef, ZenoKeyManager
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_oracle_authority import ORACLE_AUTHORITY_PAYLOAD_KIND


ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"
ORACLE_CLI = ROOT / "tools" / "zenodex_oracle.py"
PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48


def _chrome_binary() -> str | None:
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _wait_for_http(url: str, *, timeout_s: float = 30) -> None:
    import time

    deadline = time.monotonic() + timeout_s
    last_error: Exception | None = None
    while time.monotonic() < deadline:
        try:
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test server
                response.read(1)
            return
        except Exception as exc:
            last_error = exc
            time.sleep(0.2)
    raise AssertionError(f"server did not become ready at {url}: {last_error}")


def _provision_ready_authority_profile(home: Path, tmp_path: Path) -> None:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="oracle-authority-a", public_key=PUBKEY_A),
            KeyRef(key_id="oracle-authority-b", public_key=PUBKEY_B),
        )
    ).public_dict()
    signer_registry = build_signer_registry_v0(
        registry_id="zenooracle-prod-authority-v1",
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
        threshold=2,
        signers=(
            {
                "signer_id": "operator-a",
                "key_id": "oracle-authority-a",
                "public_key": PUBKEY_A,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "operator-b",
                "key_id": "oracle-authority-b",
                "public_key": PUBKEY_B,
                "weight": 1,
                "status": "active",
            },
        ),
    )
    key_manager_path = tmp_path / "oracle-authority-key-manager.json"
    signer_registry_path = tmp_path / "oracle-authority-signer-registry.json"
    key_manager_path.write_text(json.dumps(key_manager, sort_keys=True), encoding="utf-8")
    signer_registry_path.write_text(json.dumps(signer_registry, sort_keys=True), encoding="utf-8")
    provision = subprocess.run(
        [
            "python3",
            str(ORACLE_CLI),
            "--json",
            "authority",
            "provision-profile",
            "--home",
            str(home),
            "--authority-id",
            "zenooracle-mainnet-authority-v1",
            "--chain-id",
            "zeno-ledger-mainnet",
            "--key-manager",
            str(key_manager_path),
            "--signer-registry",
            str(signer_registry_path),
            "--runtime-proof-profile",
            "zenooracle-o3-replay-zk-profile-v1",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert provision.returncode == 0, provision.stderr


def test_oracle_ui_smoke_loads_local_service(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode({"tab": "oracle", "oracleView": "Verify", "demo": "false"})
        chrome_profile = tmp_path / "chrome-profile"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=15000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert ("Local API connected" in dom) or ("Local API replay warning" in dom)
        assert "Authority blocked" in dom
        assert "Verify" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


def test_oracle_ui_smoke_reports_ready_authority_profile(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home-authority"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr
    _provision_ready_authority_profile(home, tmp_path)

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        assert ready["production_authority"] is True
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode({"tab": "oracle", "oracleView": "Governance", "demo": "false"})
        chrome_profile = tmp_path / "chrome-profile-authority"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=15000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "Production authority ready" in dom
        assert "Authority Profile" in dom
        assert "Key Manager" in dom
        assert "oracle-authority-a" in dom
        assert "External signer" in dom
        assert "zenooracle-o3-replay-zk-profile-v1" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


def test_oracle_ui_smoke_runs_write_enabled_receipt_flow(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home-write"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
            "--allow-writes",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        assert ready["write_paths_enabled"] is True
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode(
            {
                "tab": "oracle",
                "oracleView": "Receipts",
                "demo": "false",
                "zenodexUiSmokeOracleWrites": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile-write"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=25000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "oracle write smoke accepted" in dom
        assert "sha256:" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)


def test_oracle_ui_smoke_reports_write_disabled_for_read_only_service(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    home = tmp_path / "oracle-home-read-only"
    init_proc = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_proc.returncode == 0, init_proc.stderr

    oracle_port = _free_port()
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "VITE_DEMO_MODE": "false",
        "VITE_ZENO_ORACLE_API_URL": f"http://127.0.0.1:{oracle_port}",
    }
    vite_proc = None
    try:
        assert oracle_proc.stdout is not None
        ready_line = oracle_proc.stdout.readline()
        ready = json.loads(ready_line)
        assert ready["ok"] is True
        assert ready["write_paths_enabled"] is False
        _wait_for_http(f"http://127.0.0.1:{oracle_port}/api/oracle/health", timeout_s=30)

        vite_proc = subprocess.Popen(
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(vite_base, timeout_s=30)

        query = urlencode(
            {
                "tab": "oracle",
                "oracleView": "Receipts",
                "demo": "false",
                "zenodexUiSmokeOracleWrites": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile-read-only"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=25000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "ZenoOracle" in dom
        assert "oracle write smoke failed write_api_disabled" in dom
    finally:
        if vite_proc is not None:
            vite_proc.terminate()
            try:
                vite_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                vite_proc.kill()
                vite_proc.wait(timeout=5)
        oracle_proc.terminate()
        try:
            oracle_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            oracle_proc.kill()
            oracle_proc.wait(timeout=5)
