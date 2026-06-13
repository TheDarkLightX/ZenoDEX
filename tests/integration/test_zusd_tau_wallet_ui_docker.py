from __future__ import annotations

import json
import os
import shutil
import socket
import subprocess
import time
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import urlopen

import pytest

from src.integration.tau_net_client import (
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from tests.integration.vite_test_server import vite_dev_command

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


def _wait_for_tau_hello(*, host: str, port: int, timeout_s: float = 240) -> TauNetTcpClient:
    deadline = time.monotonic() + timeout_s
    last_error: Exception | None = None
    client = TauNetTcpClient(TauNetTcpConfig(host=host, port=port, timeout_s=3.0))
    while time.monotonic() < deadline:
        try:
            if client.rpc("hello version=1").strip():
                return client
        except Exception as exc:
            last_error = exc
        time.sleep(1.0)
    raise AssertionError(f"Tau node did not become ready on {host}:{port}: {last_error}")


def _read_app_state(client: TauNetTcpClient) -> dict[str, object]:
    payload = json.loads(client.getappstate(full=True))
    assert isinstance(payload, dict)
    return payload


def _balance_for_asset(app_state: dict[str, object], *, pubkey: str, asset_id: str) -> int:
    raw = app_state.get("app_state")
    if not isinstance(raw, dict):
        return 0
    balances = raw.get("balances")
    if not isinstance(balances, list):
        return 0
    for row in balances:
        if not isinstance(row, dict):
            continue
        if str(row.get("pubkey", "")).strip().lower() != pubkey.strip().lower():
            continue
        if str(row.get("asset", "")).strip().lower() != asset_id.strip().lower():
            continue
        return int(row.get("amount", 0))
    return 0


def _wait_for_asset_balance(
    client: TauNetTcpClient,
    *,
    pubkey: str,
    asset_id: str,
    expected: int,
    timeout_s: float = 10.0,
) -> int:
    deadline = time.monotonic() + timeout_s
    last_balance = 0
    while time.monotonic() < deadline:
        app_state = _read_app_state(client)
        last_balance = _balance_for_asset(app_state, pubkey=pubkey, asset_id=asset_id)
        if last_balance == expected:
            return last_balance
        time.sleep(0.25)
    return last_balance


def test_zusd_tau_wallet_ui_smoke_through_docker_tau_node(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if shutil.which("docker") is None:
        pytest.skip("docker is required for the Docker Tau-node acceptance test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")
    if not (ROOT / "external" / "tau-testnet" / "server.py").exists():
        pytest.skip("external/tau-testnet checkout is required")

    operator_privkey = 41
    operator_pubkey = "0x" + bls_pubkey_hex_from_privkey(operator_privkey)
    recipient_pubkey = "0x" + bls_pubkey_hex_from_privkey(42)
    tau_port = _free_port()
    api_port = _free_port()
    vite_port = _free_port()
    chain_id = f"tau-ui-zusd-docker-{tau_port}"
    project_name = "zenodex-zusd-docker"
    db_volume = f"{project_name}_tau-local-db"
    asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)

    compose_env = {
        **os.environ,
        "TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_FORCE_TEST": "1",
        "TAU_ENABLE_FAUCET": "0",
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY": operator_pubkey,
    }
    compose_up = [
        "docker",
        "compose",
        "-p",
        project_name,
        "-f",
        "docker-compose.yml",
        "-f",
        "docker-compose.permissionless.yml",
        "--profile",
        "local-node",
        "up",
        "-d",
        "tau-local",
    ]
    compose_down = [
        "docker",
        "compose",
        "-p",
        project_name,
        "-f",
        "docker-compose.yml",
        "-f",
        "docker-compose.permissionless.yml",
        "down",
    ]

    api_proc = None
    vite_proc = None
    subprocess.run(compose_up, cwd=ROOT, env=compose_env, check=True, capture_output=True, text=True)
    try:
        tau_client = _wait_for_tau_hello(host="127.0.0.1", port=tau_port, timeout_s=240)

        api_env = {
            **os.environ,
            "API_HOST": "127.0.0.1",
            "API_PORT": str(api_port),
            "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
            "ZUSD_TAU_WALLET_API_ENABLED": "true",
            "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING": "true",
            "ZUSD_TAU_WALLET_AUTO_MINE": "true",
            "ZUSD_TAU_WALLET_CHAIN_ID": chain_id,
            "ZUSD_TAU_WALLET_TAU_HOST": "127.0.0.1",
            "ZUSD_TAU_WALLET_TAU_PORT": str(tau_port),
            "TAU_DEX_TOKEN_OPERATOR_PUBKEY": operator_pubkey,
        }
        api_proc = subprocess.Popen(
            ["python3", "-m", "src.integration.api_server"],
            cwd=ROOT,
            env=api_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(f"http://127.0.0.1:{api_port}/health", timeout_s=30)

        vite_env = {
            **os.environ,
            "API_PROXY_TARGET": f"http://127.0.0.1:{api_port}",
            "VITE_DEMO_MODE": "false",
        }
        vite_proc = subprocess.Popen(
            vite_dev_command(DEX_UI, vite_port),
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(f"http://127.0.0.1:{vite_port}", timeout_s=30)

        query = urlencode(
            {
                "tab": "zusd",
                "demo": "false",
                "zenodexUiSmokeZusd": "1",
                "zusdAction": "mint",
                "operatorPubkey": operator_pubkey,
                "recipientPubkey": recipient_pubkey,
                "signerPrivkey": str(operator_privkey),
                "zusdAmount": "5",
                "zusdDeadline": str(int(time.time()) + 3600),
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
                "--virtual-time-budget=20000",
                "--dump-dom",
                f"http://127.0.0.1:{vite_port}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        assert "SUCCESS" in result.stdout

        recipient_balance = _wait_for_asset_balance(
            tau_client,
            pubkey=recipient_pubkey,
            asset_id=asset_id,
            expected=5,
            timeout_s=10.0,
        )
        assert recipient_balance == 5
    finally:
        for proc in (vite_proc, api_proc):
            if proc is None:
                continue
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
        subprocess.run(compose_down, cwd=ROOT, env=compose_env, check=False, capture_output=True, text=True)
        subprocess.run(
            ["docker", "volume", "rm", "-f", db_volume],
            cwd=ROOT,
            env=compose_env,
            check=False,
            capture_output=True,
            text=True,
        )
