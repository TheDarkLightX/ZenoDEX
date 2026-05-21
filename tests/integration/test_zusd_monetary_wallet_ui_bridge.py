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
from urllib.request import Request, urlopen

import pytest

from src.core.dex import DexState
from src.core.zusd import E8, ZUSDCommand, init_state, step
from src.integration import tau_testnet_dex_plugin as plugin
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryState,
    zusd_monetary_state_to_obj,
)
from src.state import BalanceTable, LPTable


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
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test servers only
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
    with urlopen(request, timeout=8) as response:  # noqa: S310 - local test servers only
        return json.loads(response.read().decode("utf-8"))


def _ok(core, tag: str, **kwargs):
    res = step(core, ZUSDCommand(tag=tag, args=kwargs))
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _initial_app_state_json(*, owner_pubkey: str) -> str:
    core = init_state()
    core = _ok(core, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    core = _ok(core, "deposit_collateral", amount_e8=20 * E8)
    dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    payload = {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": zusd_monetary_state_to_obj(
            ZUSDMonetaryState(
                core=core,
                vault_owner_pubkey=owner_pubkey,
                sp_deposits_e8={},
                sp_collateral_claims_e8={},
            )
        ),
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


class _TauRpcState:
    def __init__(self, *, owner_pubkey: str, chain_id: str) -> None:
        self.owner_pubkey = owner_pubkey.lower()
        self.chain_id = chain_id
        self.app_state_json = _initial_app_state_json(owner_pubkey=owner_pubkey)
        self.app_hash = "ab" * 32
        self.pending_tx: dict[str, object] | None = None
        self.sequences: dict[str, int] = {self.owner_pubkey[2:]: 7}
        self.native_balances: dict[str, int] = {self.owner_pubkey: 0}
        self.lock = threading.Lock()

    def app_state_payload(self) -> dict[str, object]:
        return {
            "app_hash": self.app_hash,
            "app_state": json.loads(self.app_state_json),
        }

    def apply_pending(self) -> None:
        with self.lock:
            if self.pending_tx is None:
                return
            payload = dict(self.pending_tx)
            sender_wire = str(payload["sender_pubkey"]).lower()
            sender = sender_wire if sender_wire.startswith("0x") else f"0x{sender_wire}"
            sequence_number = int(payload["sequence_number"])
            ops = payload["operations"]
            assert isinstance(ops, dict)
            ok, next_json, app_hash, _patch, err = plugin.apply_app_tx(
                app_state_json=self.app_state_json,
                chain_balances=dict(self.native_balances),
                operations=ops,
                tx_sender_pubkey=sender,
                block_timestamp=int(time.time()),
            )
            assert ok, err
            self.app_state_json = next_json
            self.app_hash = app_hash
            self.sequences[sender_wire] = sequence_number + 1
            self.pending_tx = None


class _TauRpcHandler(socketserver.StreamRequestHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        state: _TauRpcState = self.server.state  # type: ignore[attr-defined]
        if line == "hello version=1":
            self.wfile.write(b"HELLO: ok\n")
            return
        if line.startswith("getsequence "):
            pubkey = line.split(" ", 1)[1].strip().lower()
            self.wfile.write(f"SEQUENCE: {state.sequences.get(pubkey, 0)}\n".encode("utf-8"))
            return
        if line.startswith("getbalance "):
            pubkey = line.split(" ", 1)[1].strip().lower()
            account = pubkey if pubkey.startswith("0x") else f"0x{pubkey}"
            self.wfile.write(f"BALANCE: {state.native_balances.get(account, 0)}\n".encode("utf-8"))
            return
        if line == "getappstate full":
            self.wfile.write((json.dumps(state.app_state_payload(), sort_keys=True) + "\n").encode("utf-8"))
            return
        if line.startswith("sendtx "):
            payload = json.loads(line.split(" ", 1)[1])
            with state.lock:
                state.pending_tx = payload
            self.wfile.write(b"SUCCESS tx accepted\n")
            return
        if line == "createblock":
            state.apply_pending()
            self.wfile.write(b"BLOCK created\n")
            return
        self.wfile.write(b"ERR unsupported\n")


def test_zusd_monetary_wallet_ui_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-zusd-monetary-ui"
    owner_privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(owner_pubkey=owner_pubkey, chain_id=chain_id)  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
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
        "TAU_DEX_CHAIN_ID": chain_id,
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
        deadline = int(time.time()) + 3600
        prepare_body = {
            "action": "mint_zusd",
            "owner_pubkey": owner_pubkey,
            "amount": 1000,
            "deadline": deadline,
            "tx_fee_limit": "0",
        }
        prepared = _http_post_json(api_base + "/api/zusd/monetary/prepare", prepare_body)
        assert prepared["ok"] is True
        signed_payload = build_signed_tau_transaction(
            privkey=owner_privkey,
            sequence_number=int(prepared["transport"]["tx_sequence_number"]),
            expiration_time=deadline,
            operations=prepared["report"]["operations"],
            fee_limit=0,
        )
        query = urlencode(
            {
                "tab": "zusd",
                "demo": "false",
                "zenodexUiSmokeZusdMonetary": "1",
                "zusdMonetaryAction": "mint_zusd",
                "actorPubkey": owner_pubkey,
                "zusdAmount": "1000",
                "zusdDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
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
        assert "zUSD Monetary Vault" in dom
        assert "Tau node connected" in dom
        assert "SUCCESS tx accepted" in dom
        assert "external_signed_payload" in dom
        assert '"action": "mint_zusd"' in dom
        assert '"debt_e8": 100000000000' in dom
    finally:
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
