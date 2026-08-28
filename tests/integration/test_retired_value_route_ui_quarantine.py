from __future__ import annotations

import os
import shutil
import socket
import subprocess
import time
from pathlib import Path
from typing import cast

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
    from urllib.request import urlopen

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
    raise AssertionError(f"UI server did not become ready at {url}: {last_error}")


def _dump_dom(chrome: str, *, profile: Path, url: str) -> str:
    result = subprocess.run(
        [
            chrome,
            "--headless=new",
            "--disable-gpu",
            "--no-sandbox",
            f"--user-data-dir={profile}",
            "--virtual-time-budget=10000",
            "--dump-dom",
            url,
        ],
        check=False,
        capture_output=True,
        text=True,
        timeout=35,
    )
    assert result.returncode == 0, result.stderr[-2000:]
    return result.stdout


def test_current_profile_hides_quarantined_value_route_controls(tmp_path: Path) -> None:
    """Given hostile UI overrides, retired routes remain visibly read-only."""

    chrome_candidate = _chrome_binary()
    if chrome_candidate is None:
        pytest.skip("Chrome/Chromium is required for the browser UI quarantine test")
    chrome = cast(str, chrome_candidate)
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI quarantine test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": "", "VITE_DEMO_MODE": "false"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(vite_base, timeout_s=30)

        perps_dom = _dump_dom(
            chrome,
            profile=tmp_path / "chrome-perps",
            url=(
                f"{vite_base}/?tab=perps&demo=false&perpsPreviewWrites=true"
                "&zenodexUiSmokePerpsWallet=1#operatorPrivkey=hostile-override"
            ),
        )
        assert "Read-only · route quarantined" in perps_dom
        assert "Perpetuals value actions are quarantined" in perps_dom
        assert "Local-testnet writes enabled" not in perps_dom
        assert "Operator console" not in perps_dom

        zusd_dom = _dump_dom(
            chrome,
            profile=tmp_path / "chrome-zusd",
            url=(
                f"{vite_base}/?tab=zusd&demo=false&zenodexUiSmokeZusd=1"
                "&zenodexUiSmokeZusdQuickMint=1#signerPrivkey=hostile-override"
            ),
        )
        assert "zUSD value routes are quarantined" in zusd_dom
        assert "Submit transfer" not in zusd_dom
        assert "Signer credential" not in zusd_dom
        assert "Quick Mint zUSD" not in zusd_dom
        assert "Submit transaction" not in zusd_dom
    finally:
        vite_proc.terminate()
        try:
            vite_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite_proc.kill()
            vite_proc.wait(timeout=5)
