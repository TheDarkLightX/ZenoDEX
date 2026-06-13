from __future__ import annotations

import json
import os
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import urlopen

import pytest

from tests.integration.vite_test_server import vite_dev_command

ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"
NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
MEASUREMENT = f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"
POLICY_DIGEST = "0x" + ("d" * 64)


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


def _verifier_cmd_json() -> str:
    code = (
        "import json,sys;"
        "json.load(sys.stdin);"
        "print(json.dumps({'ok': True, 'result': "
        f"{{'measurement': {MEASUREMENT!r}, 'policy_digest': {POLICY_DIGEST!r}, 'attestation_epoch': 9}}"
        "}))"
    )
    return json.dumps([sys.executable, "-c", code])


def test_confidential_ui_loads_live_status_surface(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
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
            "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
            "CONFIDENTIAL_FEATURE_STAGE": "beta",
            "CONFIDENTIAL_OPERATOR_CONTACT": "https://ops.zenodex.test",
            "CONFIDENTIAL_APPROVED_MEASUREMENTS": MEASUREMENT,
            "CONFIDENTIAL_FHE_ALPHA_ENABLED": "false",
            "CONFIDENTIAL_SEALED_BID_ENABLED": "true",
            "CONFIDENTIAL_TEE_ENABLED": "true",
            "CONFIDENTIAL_ATTESTATION_API_ENABLED": "true",
            "CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED": "true",
            "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON": _verifier_cmd_json(),
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    vite_proc = subprocess.Popen(
        vite_dev_command(DEX_UI, vite_port),
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

        query = urlencode({"tab": "confidential", "demo": "false", "zenodexUiSmokeConfidentialVerify": "1"})
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
        assert "CONFIDENTIAL TRADING" in dom
        assert "Hide large orders inside a trusted enclave" in dom
        assert "stage · beta" in dom
        assert "Operator details" in dom
        assert "Approved measurements · operator contact · status" in dom
        assert "Approved measurements" in dom
        assert "Accepted" in dom
        assert "execution admitted" in dom
        assert "Request" in dom
        assert "consumed" in dom
        assert "Ready" in dom
        assert "result redacted" in dom
        assert "Public effect digest" in dom
        assert "Operator status hash" in dom
        assert "Allowlist hash" in dom
        assert "Verifier binding" in dom
        assert NITRO_PCR0 not in dom
        assert NITRO_PCR8 not in dom
        assert POLICY_DIGEST not in dom
    finally:
        vite_proc.terminate()
        api_proc.terminate()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
