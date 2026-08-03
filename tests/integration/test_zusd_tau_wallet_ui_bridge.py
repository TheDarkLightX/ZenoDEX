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

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id, token_sender_nonce_key

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


class _TauRpcState:
    def __init__(
        self,
        *,
        operator_pubkey: str,
        sender_pubkey: str,
        recipient_pubkey: str,
        asset_id: str,
    ) -> None:
        self.operator_pubkey = operator_pubkey.lower()
        self.sender_pubkey = sender_pubkey.lower()
        self.recipient_pubkey = recipient_pubkey.lower()
        self.asset_id = asset_id.lower()
        self.pending_tx: dict[str, object] | None = None
        self.sequences: dict[str, int] = {
            self.operator_pubkey[2:]: 9,
            self.sender_pubkey[2:]: 7,
        }
        self.balances: dict[tuple[str, str], int] = {
            (self.sender_pubkey, self.asset_id): 400,
            (self.recipient_pubkey, self.asset_id): 10,
        }
        self.nonces: dict[str, int] = {
            token_sender_nonce_key(self.operator_pubkey).lower(): 2,
            token_sender_nonce_key(self.sender_pubkey).lower(): 4,
        }
        self.lock = threading.Lock()

    def app_state_payload(self) -> dict[str, object]:
        balances = [
            {"pubkey": pubkey, "asset": asset, "amount": amount}
            for (pubkey, asset), amount in sorted(self.balances.items())
        ]
        nonces = [{"pubkey": pubkey, "last_nonce": last_nonce} for pubkey, last_nonce in sorted(self.nonces.items())]
        return {
            "app_hash": "sha256:" + "ab" * 32,
            "app_state": {
                "balances": balances,
                "nonces": nonces,
            },
        }

    def apply_pending(self) -> None:
        with self.lock:
            if self.pending_tx is None:
                return
            payload = dict(self.pending_tx)
            sender_pubkey = str(payload["sender_pubkey"]).lower()
            balance_sender_pubkey = sender_pubkey if sender_pubkey.startswith("0x") else f"0x{sender_pubkey}"
            sequence_number = int(payload["sequence_number"])
            ops = payload["operations"]
            assert isinstance(ops, dict)
            token_stream = ops["9"]
            token_ops = json.loads(token_stream) if isinstance(token_stream, str) else token_stream
            assert isinstance(token_ops, list) and token_ops
            op = dict(token_ops[0])
            action = str(op["action"])
            asset = str(op["asset"]).lower()
            amount = int(op["amount"])
            if action == "transfer":
                recipient = str(op["to_pubkey"]).lower()
                sender_current = int(self.balances.get((balance_sender_pubkey, asset), 0))
                recipient_current = int(self.balances.get((recipient, asset), 0))
                self.balances[(balance_sender_pubkey, asset)] = sender_current - amount
                self.balances[(recipient, asset)] = recipient_current + amount
            else:
                raise AssertionError(f"managed zUSD supply action reached smoke server: {action}")
            nonce_key = token_sender_nonce_key("0x" + sender_pubkey).lower()
            self.nonces[nonce_key] = int(op["nonce"])
            self.sequences[sender_pubkey] = sequence_number + 1
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
            value = state.sequences.get(pubkey, 0)
            self.wfile.write(f"SEQUENCE: {value}\n".encode("utf-8"))
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


class _AccountStatusFakeClient:
    """Minimal in-process Tau client serving a balances-only app_state.

    Exercises the account-aware token-wallet status handler end-to-end without a
    live Tau node or Chrome (the browser tests below need both).
    """

    asset_id: str = ""
    holder_pubkey: str = ""
    holder_balance: int = 0

    def __init__(self, _cfg=None) -> None:
        self.app_hash = "sha256:" + "ab" * 32

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        payload = {
            "app_hash": self.app_hash,
            "app_state": {
                "balances": [
                    {"pubkey": self.holder_pubkey, "asset": self.asset_id, "amount": self.holder_balance},
                ],
                "nonces": [],
            },
        }
        return json.dumps(payload, sort_keys=True)


def test_zusd_tau_wallet_status_propagates_account_end_to_end(monkeypatch) -> None:
    import src.integration.zusd_tau_wallet_api as wallet_api

    chain_id = "tau-test-wallet-bridge"
    holder = "0x" + bls_pubkey_hex_from_privkey(11)
    asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)
    _AccountStatusFakeClient.asset_id = asset_id
    _AccountStatusFakeClient.holder_pubkey = holder
    _AccountStatusFakeClient.holder_balance = 400
    monkeypatch.setenv("ZUSD_TAU_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setattr(wallet_api, "TauNetTcpClient", _AccountStatusFakeClient)

    status_code, payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET", f"/api/zusd/wallet/status?account={holder}", None
    )
    assert status_code == 200
    view = payload["status"]["account_view"]
    assert view["account"] == holder
    assert view["balance"] == 400

    # Malformed account fails closed.
    bad_code, bad_payload = wallet_api.handle_zusd_tau_wallet_request(
        "GET", "/api/zusd/wallet/status?account=not-a-pubkey", None
    )
    assert bad_code == 400
    assert bad_payload["ok"] is False


def test_zusd_tau_wallet_ui_smoke_ignores_supply_action_query(
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    operator_privkey = 11
    operator_pubkey = "0x" + bls_pubkey_hex_from_privkey(operator_privkey)
    sender_privkey = 13
    sender_pubkey = "0x" + bls_pubkey_hex_from_privkey(sender_privkey)
    recipient_pubkey = "0x" + bls_pubkey_hex_from_privkey(12)
    asset_id = derive_zusd_tau_asset_id(chain_id="tau-test-wallet")

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(  # type: ignore[attr-defined]
        operator_pubkey=operator_pubkey,
        sender_pubkey=sender_pubkey,
        recipient_pubkey=recipient_pubkey,
        asset_id=asset_id,
    )
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "ZUSD_TAU_WALLET_API_ENABLED": "true",
        "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "ZUSD_TAU_WALLET_AUTO_MINE": "true",
        "ZUSD_TAU_WALLET_CHAIN_ID": "tau-test-wallet",
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
                "tab": "zusd",
                "demo": "false",
                "zenodexUiSmokeZusd": "1",
                # A stale or crafted link cannot turn this transfer surface into
                # a generic zUSD supply-changing client.
                "zusdAction": "mint",
                "operatorPubkey": operator_pubkey,
                "senderPubkey": sender_pubkey,
                "recipientPubkey": recipient_pubkey,
                "signerPrivkey": str(sender_privkey),
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
        assert "Network connected" in dom
        assert "SUCCESS tx accepted" in dom
        for needle in (
            '"action": "transfer"',
            '"sender_balance_after": 395',
            '"recipient_balance_after": 15',
            '"supply_after": 410',
        ):
            assert needle in dom
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
