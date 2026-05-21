from __future__ import annotations

import json
import os
import shutil
import socket
import socketserver
import subprocess
import threading
import time
from pathlib import Path
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
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test server only
                response.read(1)
            return
        except Exception as exc:
            last_error = exc
            time.sleep(0.2)
    raise AssertionError(f"server did not become ready at {url}: {last_error}")


class _TauRpcState:
    def __init__(self) -> None:
        self.sent: list[dict[str, object]] = []
        self.blocks = 0


class _TauRpcHandler(socketserver.BaseRequestHandler):
    def handle(self) -> None:
        data = bytearray()
        while b"\n" not in data:
            chunk = self.request.recv(65536)
            if not chunk:
                break
            data.extend(chunk)
        command = data.decode("utf-8", errors="replace").strip()
        state = self.server.state  # type: ignore[attr-defined]
        if command.startswith("getsequence "):
            response = "SEQUENCE: 9\n"
        elif command.startswith("sendtx "):
            payload = json.loads(command.removeprefix("sendtx ").strip())
            state.sent.append(payload)
            response = "SUCCESS: Transaction queued.\n"
        elif command == "createblock":
            state.blocks += 1
            response = "SUCCESS: Block created.\n"
        else:
            response = f"ERROR: unexpected command {command}\n"
        self.request.sendall(response.encode("utf-8"))


def test_autotrader_live_prepare_ui_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_ENV": "local",
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "AUTOTRADER_LIVE_API_ENABLED": "true",
        "AUTOTRADER_LIVE_CHAIN_ID": "tau-local",
        "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING": "true",
    }
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "API_PROXY_TARGET": api_base,
        "VITE_DEMO_MODE": "false",
    }
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env=vite_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "strategy",
                "demo": "false",
                "zenodexUiSmokeStrategyLive": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile"
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
        assert "AutoTrader Live Prepare" in dom
        assert "Receipt-backed prepare" in dom
        assert "submit" in dom
        assert "accepted" in dom
        assert "SWAP_EXACT_IN" in dom
        assert "production_chain_submission" in dom
    finally:
        vite_proc.terminate()
        try:
            vite_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite_proc.kill()
            vite_proc.wait(timeout=5)
        api_proc.terminate()
        try:
            api_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            api_proc.kill()
            api_proc.wait(timeout=5)


def test_autotrader_live_submit_ui_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState()  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_ENV": "local",
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "AUTOTRADER_LIVE_API_ENABLED": "true",
        "AUTOTRADER_LIVE_CHAIN_ID": "tau-local",
        "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING": "true",
        "AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION": "true",
        "AUTOTRADER_LIVE_AUTO_MINE": "true",
        "AUTOTRADER_LIVE_TAU_HOST": "127.0.0.1",
        "AUTOTRADER_LIVE_TAU_PORT": str(tau_port),
    }
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_env = {
        **os.environ,
        "API_PROXY_TARGET": api_base,
        "VITE_DEMO_MODE": "false",
    }
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env=vite_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "strategy",
                "demo": "false",
                "zenodexUiSmokeStrategyLiveSubmit": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile-submit"
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
        assert "AutoTrader Live Prepare" in dom
        assert "submitted" in dom
        assert "SUCCESS: Transaction queued." in dom
        assert "SUCCESS: Block created." in dom
        assert "SWAP_EXACT_IN" in dom
        assert len(tau_server.state.sent) == 1  # type: ignore[attr-defined]
        sent = tau_server.state.sent[0]  # type: ignore[attr-defined]
        assert sent["sequence_number"] == 9
        assert "2" in sent["operations"]
        assert tau_server.state.blocks == 1  # type: ignore[attr-defined]
    finally:
        vite_proc.terminate()
        try:
            vite_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite_proc.kill()
            vite_proc.wait(timeout=5)
        api_proc.terminate()
        try:
            api_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            api_proc.kill()
            api_proc.wait(timeout=5)
        tau_server.shutdown()
        tau_server.server_close()
