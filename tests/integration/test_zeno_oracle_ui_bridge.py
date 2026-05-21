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


ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"
ORACLE_CLI = ROOT / "tools" / "zenodex_oracle.py"


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
