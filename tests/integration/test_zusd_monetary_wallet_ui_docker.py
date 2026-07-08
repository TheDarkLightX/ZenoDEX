from __future__ import annotations

import json
import os
import shutil
import socket
import subprocess
import time
import urllib.error
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import Request, urlopen

import pytest

from src.core.zusd import E8
from src.integration.tau_net_client import (
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id


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


def _http_post_json(url: str, payload: dict[str, object]) -> dict[str, object]:
    request = Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urlopen(request, timeout=8) as response:  # noqa: S310 - local test servers
        return json.loads(response.read().decode("utf-8"))


def _http_post_json_status(url: str, payload: dict[str, object]) -> tuple[int, dict[str, object]]:
    request = Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=8) as response:  # noqa: S310 - local test servers
            return response.status, json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return exc.code, json.loads(exc.read().decode("utf-8"))


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
    app_state = payload.get("app_state")
    assert isinstance(app_state, dict)
    return app_state


def _balance_for_asset(app_state: dict[str, object], *, pubkey: str, asset_id: str) -> int:
    dex_state = app_state.get("dex_state")
    if isinstance(dex_state, dict):
        state_view = dex_state
    else:
        state_view = app_state
    balances = state_view.get("balances")
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


def _zusd_core(app_state: dict[str, object]) -> dict[str, int]:
    monetary = app_state.get("zusd_monetary")
    assert isinstance(monetary, dict)
    core = monetary.get("core")
    assert isinstance(core, dict)
    return {str(k): int(v) for k, v in core.items() if isinstance(v, int) and not isinstance(v, bool)}


def _perps_market(app_state: dict[str, object], *, market_id: str) -> dict[str, object]:
    dex_state = app_state.get("dex_state")
    assert isinstance(dex_state, dict)
    perps = dex_state.get("perps")
    assert isinstance(perps, dict)
    markets = perps.get("markets")
    assert isinstance(markets, list)
    for row in markets:
        if isinstance(row, dict) and row.get("market_id") == market_id:
            return row
    raise AssertionError(f"missing perps market {market_id!r}")


def _create_block_checked(client: TauNetTcpClient, *, label: str) -> None:
    response = client.createblock()
    assert "ERROR" not in response.upper(), f"{label} createblock failed: {response}"


def _prepare_external_signed_zusd_payload(
    *,
    api_base: str,
    privkey: int,
    body: dict[str, object],
) -> dict[str, object]:
    prepared = _http_post_json(f"{api_base}/api/zusd/monetary/prepare", body)
    assert prepared["ok"] is True
    transport = prepared["transport"]
    report = prepared["report"]
    assert isinstance(transport, dict)
    assert isinstance(report, dict)
    return build_signed_tau_transaction(
        privkey=privkey,
        sequence_number=int(transport["tx_sequence_number"]),
        expiration_time=int(body["deadline"]),
        operations=report["operations"],
        fee_limit=0,
    )


def _prepare_external_signed_perps_payload(
    *,
    api_base: str,
    privkey: int,
    body: dict[str, object],
) -> dict[str, object]:
    prepared = _http_post_json(f"{api_base}/api/perps/wallet/prepare", body)
    assert prepared["ok"] is True
    transport = prepared["transport"]
    report = prepared["report"]
    assert isinstance(transport, dict)
    assert isinstance(report, dict)
    return build_signed_tau_transaction(
        privkey=privkey,
        sequence_number=int(transport["tx_sequence_number"]),
        expiration_time=int(body["deadline"]),
        operations=report["operations"],
        fee_limit=int(str(transport["tx_fee_limit"])),
    )


def _prepare_zusd_monetary_state(
    client: TauNetTcpClient,
    *,
    owner_privkey: int,
    owner_pubkey: str,
    price_e8: int,
) -> None:
    owner_raw = owner_pubkey[2:]
    send_resp = client.send_signed_tx(
        privkey=owner_privkey,
        operations={"1": [[owner_raw, owner_raw, "1"]]},
        expiration_seconds=3600,
    )
    assert "SUCCESS" in send_resp
    _create_block_checked(client, label="native materialization")

    deadline = int(time.time()) + 3600
    send_resp = client.send_signed_tx(
        privkey=owner_privkey,
        operations={
            "25": [
                {
                    "module": "ZUSDFinance",
                    "version": "0.1",
                    "action": "bootstrap_oracle",
                    "price_e8": int(price_e8),
                    "nonce": 1,
                    "deadline": deadline,
                },
                {
                    "module": "ZUSDFinance",
                    "version": "0.1",
                    "action": "deposit_collateral",
                    "owner_pubkey": owner_pubkey,
                    "amount_e8": 1_000,
                    "nonce": 2,
                    "deadline": deadline,
                },
            ]
        },
        expiration_seconds=3600,
    )
    assert "SUCCESS" in send_resp
    _create_block_checked(client, label="zUSD monetary bootstrap")

    core = _zusd_core(_read_app_state(client))
    assert core["collateral_e8"] == 1_000
    assert core["price_e8"] == int(price_e8)


def test_zusd_monetary_wallet_ui_smoke_through_docker_tau_node(tmp_path: Path) -> None:
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

    owner_privkey = 82
    counterparty_privkey = 83
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)
    counterparty_pubkey = "0x" + bls_pubkey_hex_from_privkey(counterparty_privkey)
    tau_port = _free_port()
    api_port = _free_port()
    vite_port = _free_port()
    chain_id = f"tau-ui-zusd-money-docker-{tau_port}"
    project_name = f"zenodex-zusd-money-{tau_port}"
    db_volume = f"{project_name}_tau-local-db"
    asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = f"perp:ch2p:zusd-docker-{tau_port}"
    price_e8 = 20_000_000 * E8

    compose_env = {
        **os.environ,
        "TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_FORCE_TEST": "1",
        "TAU_ENABLE_FAUCET": "0",
        "TAU_APP_BRIDGE_ALLOW_BALANCE_PATCH": "1",
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
    compose_restart_tau = [
        "docker",
        "compose",
        "-p",
        project_name,
        "-f",
        "docker-compose.yml",
        "-f",
        "docker-compose.permissionless.yml",
        "restart",
        "tau-local",
    ]
    compose_pause_tau = [
        "docker",
        "compose",
        "-p",
        project_name,
        "-f",
        "docker-compose.yml",
        "-f",
        "docker-compose.permissionless.yml",
        "pause",
        "tau-local",
    ]
    compose_unpause_tau = [
        "docker",
        "compose",
        "-p",
        project_name,
        "-f",
        "docker-compose.yml",
        "-f",
        "docker-compose.permissionless.yml",
        "unpause",
        "tau-local",
    ]

    api_proc = None
    vite_proc = None
    subprocess.run(compose_up, cwd=ROOT, env=compose_env, check=True, capture_output=True, text=True)
    try:
        tau_client = _wait_for_tau_hello(host="127.0.0.1", port=tau_port, timeout_s=240)
        _prepare_zusd_monetary_state(
            tau_client,
            owner_privkey=owner_privkey,
            owner_pubkey=owner_pubkey,
            price_e8=price_e8,
        )

        api_env = {
            **os.environ,
            "API_HOST": "127.0.0.1",
            "API_PORT": str(api_port),
            "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
            "ZUSD_MONETARY_WALLET_API_ENABLED": "true",
            "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING": "false",
            "ZUSD_MONETARY_WALLET_AUTO_MINE": "true",
            "ZUSD_MONETARY_WALLET_CHAIN_ID": chain_id,
            "ZUSD_MONETARY_WALLET_TAU_HOST": "127.0.0.1",
            "ZUSD_MONETARY_WALLET_TAU_PORT": str(tau_port),
            "PERPS_WALLET_API_ENABLED": "true",
            "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
            "PERPS_WALLET_AUTO_MINE": "true",
            "PERPS_WALLET_CHAIN_ID": chain_id,
            "PERPS_WALLET_TAU_HOST": "127.0.0.1",
            "PERPS_WALLET_TAU_PORT": str(tau_port),
            "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
            ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
            cwd=DEX_UI,
            env=vite_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _wait_for_http(f"http://127.0.0.1:{vite_port}", timeout_s=30)

        zusd_deadline = int(time.time()) + 3600
        zusd_body = {
            "action": "mint_zusd",
            "owner_pubkey": owner_pubkey,
            "sender_pubkey": owner_pubkey,
            "amount": 100,
            "deadline": zusd_deadline,
            "tx_fee_limit": "0",
        }
        signed_zusd_payload = _prepare_external_signed_zusd_payload(
            api_base=f"http://127.0.0.1:{api_port}",
            privkey=owner_privkey,
            body=zusd_body,
        )
        query = urlencode(
            {
                "tab": "zusd",
                "demo": "false",
                "zenodexUiSmokeZusdMonetary": "1",
                "zusdMonetaryAction": "mint_zusd",
                "actorPubkey": owner_pubkey,
                "zusdAmount": "100",
                "zusdDeadline": str(zusd_deadline),
                "signedTauTxPayload": json.dumps(signed_zusd_payload, sort_keys=True, separators=(",", ":")),
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
        assert "zUSD Monetary Vault" in result.stdout
        assert "Tau node connected" in result.stdout
        assert "SUCCESS: Transaction queued." in result.stdout, result.stdout[-8000:]
        assert "SUCCESS: Block" in result.stdout, result.stdout[-8000:]
        assert "external_signed_payload" in result.stdout, result.stdout[-8000:]
        assert '"action": "mint_zusd"' in result.stdout, result.stdout[-8000:]

        app_state = _read_app_state(tau_client)
        core = _zusd_core(app_state)
        assert core["debt_e8"] == 100 * E8
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 100
        state_after_mint = app_state

        status, replay_rejected = _http_post_json_status(
            f"http://127.0.0.1:{api_port}/api/zusd/monetary/submit",
            {**zusd_body, "signed_tau_tx_payload": signed_zusd_payload},
        )
        assert status == 400
        assert replay_rejected["ok"] is False
        replay_error = str(replay_rejected["error"])
        assert replay_error == "signed_tau_tx_payload sequence mismatch" or replay_error.startswith(
            "preflight_failed:"
        )
        assert _read_app_state(tau_client) == state_after_mint

        init_query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "init_market_2p",
                "marketId": market_id,
                "quoteAsset": asset_id,
                "accountAPrivkey": str(owner_privkey),
                "accountBPrivkey": str(counterparty_privkey),
                "perpsDeadline": str(int(time.time()) + 3600),
            }
        )
        init_result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={tmp_path / 'chrome-profile-perps-init'}",
                "--virtual-time-budget=20000",
                "--dump-dom",
                f"http://127.0.0.1:{vite_port}/?{init_query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert init_result.returncode == 0, init_result.stderr[-2000:]
        assert "Live Perps Wallet" in init_result.stdout
        assert "submit accepted" in init_result.stdout, init_result.stdout[-8000:]
        assert "preflight ok" in init_result.stdout, init_result.stdout[-8000:]
        assert market_id in init_result.stdout, init_result.stdout[-8000:]

        perps_deposit_deadline = int(time.time()) + 3600
        perps_deposit_body = {
            "action": "deposit_collateral",
            "market_id": market_id,
            "account_pubkey": owner_pubkey,
            "amount": 25,
            "deadline": perps_deposit_deadline,
            "tx_fee_limit": "0",
        }
        signed_perps_deposit_payload = _prepare_external_signed_perps_payload(
            api_base=f"http://127.0.0.1:{api_port}",
            privkey=owner_privkey,
            body=perps_deposit_body,
        )
        state_before_perps_interruption = _read_app_state(tau_client)
        subprocess.run(compose_pause_tau, cwd=ROOT, env=compose_env, check=True, capture_output=True, text=True)
        try:
            status, perps_outage_rejected = _http_post_json_status(
                f"http://127.0.0.1:{api_port}/api/perps/wallet/submit",
                {**perps_deposit_body, "signed_tau_tx_payload": signed_perps_deposit_payload},
            )
        finally:
            subprocess.run(compose_unpause_tau, cwd=ROOT, env=compose_env, check=False, capture_output=True, text=True)
        assert status == 502
        assert perps_outage_rejected["ok"] is False
        assert perps_outage_rejected["error"] == "tau_rpc_error"
        tau_client = _wait_for_tau_hello(host="127.0.0.1", port=tau_port, timeout_s=240)
        assert _read_app_state(tau_client) == state_before_perps_interruption

        deposit_query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "deposit_collateral",
                "marketId": market_id,
                "accountPubkey": owner_pubkey,
                "amount": "25",
                "perpsDeadline": str(perps_deposit_deadline),
                "signedTauTxPayload": json.dumps(
                    signed_perps_deposit_payload,
                    sort_keys=True,
                    separators=(",", ":"),
                ),
            }
        )
        deposit_result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={tmp_path / 'chrome-profile-perps-deposit'}",
                "--virtual-time-budget=20000",
                "--dump-dom",
                f"http://127.0.0.1:{vite_port}/?{deposit_query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert deposit_result.returncode == 0, deposit_result.stderr[-2000:]
        assert "Live Perps Wallet" in deposit_result.stdout
        assert "Deposit Collateral" in deposit_result.stdout
        assert "submit accepted" in deposit_result.stdout, deposit_result.stdout[-8000:]
        assert "preflight ok" in deposit_result.stdout, deposit_result.stdout[-8000:]
        assert "signing external_signed_payload" in deposit_result.stdout, deposit_result.stdout[-8000:]

        app_state = _read_app_state(tau_client)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 75
        assert _balance_for_asset(app_state, pubkey=counterparty_pubkey, asset_id=asset_id) == 0
        market = _perps_market(app_state, market_id=market_id)
        assert market["quote_asset"] == asset_id
        state = market["state"]
        assert isinstance(state, dict)
        assert int(state["collateral_e8_a"]) == 25 * E8
        assert int(state["collateral_e8_b"]) == 0
        state_after_perps_deposit = app_state

        status, perps_replay_rejected = _http_post_json_status(
            f"http://127.0.0.1:{api_port}/api/perps/wallet/submit",
            {**perps_deposit_body, "signed_tau_tx_payload": signed_perps_deposit_payload},
        )
        assert status == 400
        assert perps_replay_rejected["ok"] is False
        assert perps_replay_rejected["error"] == "signed_tau_tx_payload sequence mismatch"
        assert _read_app_state(tau_client) == state_after_perps_deposit

        subprocess.run(compose_restart_tau, cwd=ROOT, env=compose_env, check=True, capture_output=True, text=True)
        tau_client = _wait_for_tau_hello(host="127.0.0.1", port=tau_port, timeout_s=240)
        assert _read_app_state(tau_client) == state_after_perps_deposit
        status, perps_replay_after_restart = _http_post_json_status(
            f"http://127.0.0.1:{api_port}/api/perps/wallet/submit",
            {**perps_deposit_body, "signed_tau_tx_payload": signed_perps_deposit_payload},
        )
        assert status == 400
        assert perps_replay_after_restart["ok"] is False
        assert perps_replay_after_restart["error"] == "signed_tau_tx_payload sequence mismatch"
        assert _read_app_state(tau_client) == state_after_perps_deposit
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
