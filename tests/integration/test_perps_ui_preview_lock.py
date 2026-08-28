from __future__ import annotations

import os
import shutil
import socket
import subprocess
import time
from pathlib import Path
from typing import cast
from urllib.parse import urlencode
from urllib.request import urlopen

import pytest

ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"


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
    deadline = time.monotonic() + timeout_s
    last_error: Exception | None = None
    while time.monotonic() < deadline:
        try:
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test servers
                response.read(1)
            return
        except Exception as exc:
            last_error = exc
            time.sleep(0.2)
    raise AssertionError(f"server did not become ready at {url}: {last_error}")


def test_perps_ui_defaults_to_quarantined_preview_in_non_demo_mode(tmp_path: Path) -> None:
    chrome_candidate = _chrome_binary()
    if chrome_candidate is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    chrome = cast(str, chrome_candidate)
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    api_port = _free_port()
    vite_port = _free_port()
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env={
            **os.environ,
            "API_HOST": "127.0.0.1",
            "API_PORT": str(api_port),
            "PERPS_API_ENABLED": "true",
            "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": f"http://127.0.0.1:{api_port}",
            "VITE_DEMO_MODE": "false",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(f"http://127.0.0.1:{api_port}/health", timeout_s=30)
        _wait_for_http(f"http://127.0.0.1:{vite_port}", timeout_s=30)

        query = urlencode({"tab": "perps", "demo": "false"})
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
                f"http://127.0.0.1:{vite_port}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Perpetuals" in dom
        assert "Read-only · route quarantined" in dom
        assert "Perpetuals value actions are quarantined" in dom
        assert "Operator console" not in dom
        assert "Local-testnet writes enabled" not in dom
    finally:
        vite_proc.terminate()
        api_proc.terminate()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_ui_query_cannot_override_current_route_quarantine(tmp_path: Path) -> None:
    chrome_candidate = _chrome_binary()
    if chrome_candidate is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    chrome = cast(str, chrome_candidate)
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    api_port = _free_port()
    vite_port = _free_port()
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env={
            **os.environ,
            "API_HOST": "127.0.0.1",
            "API_PORT": str(api_port),
            "PERPS_API_ENABLED": "true",
            "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": f"http://127.0.0.1:{api_port}",
            "VITE_DEMO_MODE": "false",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    config_file = DEX_UI / "public" / "zenodex-config.json"
    original_config = config_file.read_text(encoding="utf-8") if config_file.exists() else None
    try:
        config_file.write_text(
            '{"apiBase":"","demoMode":false,"deployment":"local-testnet",'
            '"chainId":"zeno-ledger-localtest-v0","perpsWalletUiEnabled":false,'
            '"zusdTauWalletUiEnabled":false,"zusdMonetaryWalletUiEnabled":false}\n',
            encoding="utf-8",
        )
        _wait_for_http(f"http://127.0.0.1:{api_port}/health", timeout_s=30)
        _wait_for_http(f"http://127.0.0.1:{vite_port}", timeout_s=30)

        query = urlencode({"tab": "perps", "demo": "false", "perpsPreviewWrites": "true"})
        chrome_profile = tmp_path / "chrome-profile-localtest"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=15000",
                "--dump-dom",
                f"http://127.0.0.1:{vite_port}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=45,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Perpetuals" in dom
        assert "Read-only · route quarantined" in dom
        assert "Perpetuals value actions are quarantined" in dom
        assert "Local-testnet writes enabled" not in dom
        assert "Operator console" not in dom
    finally:
        if original_config is not None:
            config_file.write_text(original_config, encoding="utf-8")
        elif config_file.exists():
            config_file.unlink()
        vite_proc.terminate()
        api_proc.terminate()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
