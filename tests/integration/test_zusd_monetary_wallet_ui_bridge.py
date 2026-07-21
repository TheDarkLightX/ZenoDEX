from __future__ import annotations

import json
import os
import shutil
import socket
import socketserver
import subprocess
import threading
import time
from dataclasses import replace
from pathlib import Path
from urllib.error import HTTPError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

import pytest

from src.core.dex import DexState
from src.core.zusd import E8, ZUSDCommand, step
from src.integration import tau_testnet_dex_plugin as plugin
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from src.integration.zusd_monetary_bridge import (
    init_monetary_state,
    stability_pool_pubkey,
    zusd_monetary_state_to_obj,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
from tests.chaos.conftest import requires_toxiproxy
from tests.consensus_clock import execution_clock_v1
from tests.integration.tau_rpc_fault_proxy import TauRpcFaultProxy
from tools.chaos.toxiproxy_harness import ToxiproxyHarness

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


def _http_post_json_status(url: str, payload: dict[str, object]) -> tuple[int, dict[str, object]]:
    request = Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=8) as response:  # noqa: S310 - local test servers only
            return int(response.status), json.loads(response.read().decode("utf-8"))
    except HTTPError as exc:
        return int(exc.code), json.loads(exc.read().decode("utf-8"))


def _app_state_from_tau_server(tau_server: socketserver.ThreadingTCPServer) -> dict[str, object]:
    state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
    payload = json.loads(state.app_state_json)
    assert isinstance(payload, dict)
    return payload


def _tau_command_count(tau_server: socketserver.ThreadingTCPServer, command: str) -> int:
    state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
    with state.lock:
        return int(state.command_counts.get(command, 0))


def _wait_for_tau_command_count(
    tau_server: socketserver.ThreadingTCPServer,
    command: str,
    minimum: int,
    *,
    timeout_s: float = 10.0,
) -> None:
    deadline = time.monotonic() + float(timeout_s)
    while time.monotonic() < deadline:
        if _tau_command_count(tau_server, command) >= int(minimum):
            return
        time.sleep(0.05)
    raise AssertionError(f"tau command {command!r} did not reach count {minimum}")


def _zusd_core(app_state: dict[str, object]) -> dict[str, int]:
    monetary = app_state.get("zusd_monetary")
    assert isinstance(monetary, dict)
    core = monetary.get("core")
    assert isinstance(core, dict)
    return {
        str(k): int(v) for k, v in core.items() if isinstance(v, int) and not isinstance(v, bool)
    }


def _balance_for_asset(app_state: dict[str, object], *, pubkey: str, asset_id: str) -> int:
    dex_state = app_state.get("dex_state")
    state_view = dex_state if isinstance(dex_state, dict) else app_state
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


def _sp_claims(app_state: dict[str, object]) -> dict[str, int]:
    monetary = app_state.get("zusd_monetary")
    assert isinstance(monetary, dict)
    claims = monetary.get("sp_collateral_claims")
    assert isinstance(claims, list)
    out: dict[str, int] = {}
    for row in claims:
        assert isinstance(row, dict)
        out[str(row["pubkey"])] = int(row["amount_e8"])
    return out


def _ok(core, tag: str, **kwargs):
    res = step(core, ZUSDCommand(tag=tag, args=kwargs))
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _initial_app_state_json(*, owner_pubkey: str, chain_id: str) -> str:
    monetary = init_monetary_state(
        plugin._build_zusd_monetary_config(chain_id=chain_id)  # noqa: SLF001
    )
    core = monetary.core
    core = _ok(core, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    core = _ok(core, "deposit_collateral", amount_e8=20 * E8)
    dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    payload = {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": zusd_monetary_state_to_obj(
            replace(
                monetary,
                core=core,
                vault_owner_pubkey=owner_pubkey,
            )
        ),
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


class _TauRpcState:
    def __init__(self, *, owner_pubkey: str, chain_id: str) -> None:
        self.owner_pubkey = owner_pubkey.lower()
        self.chain_id = chain_id
        self.app_state_json = _initial_app_state_json(
            owner_pubkey=owner_pubkey,
            chain_id=chain_id,
        )
        self.app_hash = "ab" * 32
        self.pending_tx: dict[str, object] | None = None
        self.sequences: dict[str, int] = {self.owner_pubkey[2:]: 7}
        self.native_balances: dict[str, int] = {self.owner_pubkey: 5 * E8}
        self.command_counts: dict[str, int] = {}
        self.block_height = 0
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
            old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
            old_oracle = os.environ.get("TAU_DEX_ZUSD_ORACLE_PUBKEY")
            os.environ["TAU_DEX_CHAIN_ID"] = self.chain_id
            os.environ["TAU_DEX_ZUSD_ORACLE_PUBKEY"] = self.owner_pubkey
            try:
                height = self.block_height
                ok, next_json, app_hash, _patch, err = plugin.apply_app_tx(
                    app_state_json=self.app_state_json,
                    chain_balances=dict(self.native_balances),
                    operations=ops,
                    tx_sender_pubkey=sender,
                    block_timestamp=height,
                    execution_clock=execution_clock_v1(
                        chain_id=self.chain_id,
                        height=height,
                    ),
                )
            finally:
                if old_chain_id is None:
                    os.environ.pop("TAU_DEX_CHAIN_ID", None)
                else:
                    os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
                if old_oracle is None:
                    os.environ.pop("TAU_DEX_ZUSD_ORACLE_PUBKEY", None)
                else:
                    os.environ["TAU_DEX_ZUSD_ORACLE_PUBKEY"] = old_oracle
            assert ok, err
            self.app_state_json = next_json
            self.app_hash = app_hash
            self.block_height += 1
            if isinstance(_patch, dict):
                for pubkey, amount in _patch.items():
                    self.native_balances[str(pubkey).strip().lower()] = int(amount)
            self.sequences[sender_wire] = sequence_number + 1
            self.pending_tx = None


class _TauRpcHandler(socketserver.StreamRequestHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        state: _TauRpcState = self.server.state  # type: ignore[attr-defined]
        command = line.split(" ", 1)[0] if line else ""
        with state.lock:
            state.command_counts[command] = int(state.command_counts.get(command, 0)) + 1
        self._dispatch_line(line)

    def _dispatch_line(self, line: str) -> None:
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
            self.wfile.write(
                (json.dumps(state.app_state_payload(), sort_keys=True) + "\n").encode("utf-8")
            )
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


class _TauRpcGatedSendSuccessHandler(_TauRpcHandler):
    def _dispatch_line(self, line: str) -> None:
        if line.startswith("sendtx "):
            state: _TauRpcState = self.server.state  # type: ignore[attr-defined]
            payload = json.loads(line.split(" ", 1)[1])
            with state.lock:
                state.pending_tx = payload
            gate = getattr(self.server, "send_response_event", None)
            if gate is not None:
                assert gate.wait(timeout=10.0)
            self.wfile.write(b"SUCCESS tx accepted\n")
            return
        super()._dispatch_line(line)


class _TauRpcPartialSendTimeoutHandler(_TauRpcHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        if line.startswith("sendtx "):
            self.wfile.write(b"PARTIAL_PRIVATE_RESPONSE")
            self.wfile.flush()
            time.sleep(1.0)
            return
        self._dispatch_line(line)

    def _dispatch_line(self, line: str) -> None:
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
            self.wfile.write(
                (json.dumps(state.app_state_payload(), sort_keys=True) + "\n").encode("utf-8")
            )
            return
        if line == "createblock":
            state.apply_pending()
            self.wfile.write(b"BLOCK created\n")
            return
        self.wfile.write(b"ERR unsupported\n")


class _TauRpcSendDropBeforeResponseHandler(_TauRpcPartialSendTimeoutHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        if line.startswith("sendtx "):
            return
        self._dispatch_line(line)


class _TauRpcDelayedSendSuccessHandler(_TauRpcPartialSendTimeoutHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        if line.startswith("sendtx "):
            time.sleep(float(getattr(self.server, "send_delay_s", 0.0)))
            state: _TauRpcState = self.server.state  # type: ignore[attr-defined]
            payload = json.loads(line.split(" ", 1)[1])
            with state.lock:
                state.pending_tx = payload
            self.wfile.write(b"SUCCESS tx accepted\n")
            return
        self._dispatch_line(line)


def _prepare_external_signed_zusd_payload(
    *,
    api_base: str,
    privkey: int,
    body: dict[str, object],
) -> dict[str, object]:
    prepared = _http_post_json(api_base + "/api/zusd/monetary/prepare", body)
    assert prepared["ok"] is True
    transport = prepared["transport"]
    report = prepared["report"]
    assert isinstance(transport, dict)
    assert isinstance(report, dict)
    signed_payload = build_signed_tau_transaction(
        privkey=privkey,
        sequence_number=int(transport["tx_sequence_number"]),
        expiration_time=int(body["deadline"]),
        operations=report["operations"],
        fee_limit=0,
    )
    return signed_payload


def _run_zusd_browser_submit(
    *,
    chrome: str,
    tmp_path: Path,
    vite_base: str,
    api_base: str,
    privkey: int,
    actor_pubkey: str,
    action: str,
    profile_name: str,
    amount: int | None = None,
    amount_e8: int | None = None,
    price_e8: int | None = None,
    deadline: int | None = None,
    expected_snippets: tuple[str, ...] = (),
) -> str:
    actual_deadline = int(deadline if deadline is not None else int(time.time()) + 3600)
    body: dict[str, object] = {
        "action": action,
        "sender_pubkey": actor_pubkey,
        "deadline": actual_deadline,
        "tx_fee_limit": "0",
    }
    query: dict[str, str] = {
        "tab": "zusd",
        "demo": "false",
        "zenodexUiSmokeZusdMonetary": "1",
        "zusdMonetaryAction": action,
        "actorPubkey": actor_pubkey,
        "zusdDeadline": str(actual_deadline),
    }
    if action in {"deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd"}:
        body["owner_pubkey"] = actor_pubkey
    if action in {"deposit_sp", "withdraw_sp", "redeem_zusd", "claim_sp_collateral"}:
        body["account_pubkey"] = actor_pubkey
    if action in {
        "advance_epoch",
        "bootstrap_oracle",
        "oracle_report",
        "oracle_commit",
        "liquidate",
    }:
        body["actor_pubkey"] = actor_pubkey
    if amount is not None:
        body["amount"] = int(amount)
        query["zusdAmount"] = str(int(amount))
    if amount_e8 is not None:
        body["amount_e8"] = int(amount_e8)
        query["zusdAmountE8"] = str(int(amount_e8))
    if price_e8 is not None:
        body["price_e8"] = int(price_e8)
        query["zusdPriceE8"] = str(int(price_e8))

    signed_payload = _prepare_external_signed_zusd_payload(
        api_base=api_base, privkey=privkey, body=body
    )
    query["signedTauTxPayload"] = json.dumps(signed_payload, sort_keys=True, separators=(",", ":"))
    result = subprocess.run(
        [
            chrome,
            "--headless=new",
            "--disable-gpu",
            "--no-sandbox",
            f"--user-data-dir={tmp_path / profile_name}",
            "--virtual-time-budget=15000",
            "--dump-dom",
            f"{vite_base}/?{urlencode(query)}",
        ],
        check=False,
        capture_output=True,
        text=True,
        timeout=45,
    )
    assert result.returncode == 0, result.stderr[-2000:]
    dom = result.stdout
    assert "zUSD Monetary Vault" in dom, dom[-8000:]
    assert "Tau node connected" in dom, dom[-8000:]
    assert "SUCCESS tx accepted" in dom, dom[-8000:]
    assert "external_signed_payload" in dom, dom[-8000:]
    assert f'"action": "{action}"' in dom, dom[-8000:]
    assert "zusd_stream11_live_monetary_v0" in dom, dom[-8000:]
    assert '"zk_proof_verified": false' in dom, dom[-8000:]
    for snippet in expected_snippets:
        assert snippet in dom, dom[-8000:]
    return dom


def test_zusd_monetary_wallet_browser_fails_closed_on_partial_tau_send_timeout(
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-zusd-monetary-ui-chaos"
    owner_privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)
    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(
        ("127.0.0.1", tau_port), _TauRpcPartialSendTimeoutHandler
    )
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
        "ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S": "0.2",
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": api_base,
            "VITE_DEMO_MODE": "false",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)

        deadline = int(time.time()) + 3600
        body = {
            "action": "mint_zusd",
            "owner_pubkey": owner_pubkey,
            "sender_pubkey": owner_pubkey,
            "amount": 100,
            "deadline": deadline,
            "tx_fee_limit": "0",
        }
        signed_payload = _prepare_external_signed_zusd_payload(
            api_base=api_base,
            privkey=owner_privkey,
            body=body,
        )
        state_before = _app_state_from_tau_server(tau_server)
        status, api_rejected = _http_post_json_status(
            api_base + "/api/zusd/monetary/submit",
            {**body, "signed_tau_tx_payload": signed_payload},
        )
        assert status == 502
        assert api_rejected["ok"] is False
        assert api_rejected["error"] == "tau_rpc_error"
        assert "PARTIAL_PRIVATE_RESPONSE" not in json.dumps(api_rejected, sort_keys=True)
        assert _app_state_from_tau_server(tau_server) == state_before
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[owner_pubkey[2:].lower()] == 7

        query = urlencode(
            {
                "tab": "zusd",
                "demo": "false",
                "zenodexUiSmokeZusdMonetary": "1",
                "zusdMonetaryAction": "mint_zusd",
                "actorPubkey": owner_pubkey,
                "zusdAmount": "100",
                "zusdDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(
                    signed_payload, sort_keys=True, separators=(",", ":")
                ),
            }
        )
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={tmp_path / 'chrome-profile-zusd-chaos'}",
                "--virtual-time-budget=20000",
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
        assert "zUSD Monetary Vault" in dom
        assert "Tau node connected" in dom
        assert "tau_rpc_error" in dom, dom[-8000:]
        assert "PARTIAL_PRIVATE_RESPONSE" not in dom
        assert _app_state_from_tau_server(tau_server) == state_before
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[owner_pubkey[2:].lower()] == 7
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


def test_zusd_monetary_wallet_browser_fails_closed_on_tau_send_drop_before_response(
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-zusd-monetary-ui-send-drop"
    owner_privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)
    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(
        ("127.0.0.1", tau_port), _TauRpcSendDropBeforeResponseHandler
    )
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
        "ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S": "0.5",
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": api_base,
            "VITE_DEMO_MODE": "false",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)

        deadline = int(time.time()) + 3600
        body = {
            "action": "mint_zusd",
            "owner_pubkey": owner_pubkey,
            "sender_pubkey": owner_pubkey,
            "amount": 100,
            "deadline": deadline,
            "tx_fee_limit": "0",
        }
        signed_payload = _prepare_external_signed_zusd_payload(
            api_base=api_base,
            privkey=owner_privkey,
            body=body,
        )
        state_before = _app_state_from_tau_server(tau_server)
        status, api_rejected = _http_post_json_status(
            api_base + "/api/zusd/monetary/submit",
            {**body, "signed_tau_tx_payload": signed_payload},
        )
        api_error_text = json.dumps(api_rejected, sort_keys=True)
        assert status == 502
        assert api_rejected["ok"] is False
        assert api_rejected["error"] == "tau_rpc_error"
        assert "mint_zusd" not in api_error_text
        assert "sender_pubkey" not in api_error_text
        assert "signature" not in api_error_text
        assert _app_state_from_tau_server(tau_server) == state_before
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[owner_pubkey[2:].lower()] == 7

        query = urlencode(
            {
                "tab": "zusd",
                "demo": "false",
                "zenodexUiSmokeZusdMonetary": "1",
                "zusdMonetaryAction": "mint_zusd",
                "actorPubkey": owner_pubkey,
                "zusdAmount": "100",
                "zusdDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(
                    signed_payload, sort_keys=True, separators=(",", ":")
                ),
            }
        )
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={tmp_path / 'chrome-profile-zusd-send-drop'}",
                "--virtual-time-budget=20000",
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
        assert "zUSD Monetary Vault" in dom
        assert "Tau node connected" in dom
        assert "tau_rpc_error" in dom, dom[-8000:]
        assert _app_state_from_tau_server(tau_server) == state_before
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[owner_pubkey[2:].lower()] == 7
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


def test_zusd_monetary_wallet_browser_fails_closed_on_truncated_proxy_sendtx_response(
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-zusd-monetary-ui-proxy-truncate"
    owner_privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)
    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(owner_pubkey=owner_pubkey, chain_id=chain_id)  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()
    proxy = TauRpcFaultProxy(
        upstream_host="127.0.0.1",
        upstream_port=tau_port,
        truncate_sendtx_response_bytes=7,
    ).start()

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
        "ZUSD_MONETARY_WALLET_TAU_HOST": proxy.host,
        "ZUSD_MONETARY_WALLET_TAU_PORT": str(proxy.port),
        "ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S": "1.0",
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": api_base,
            "VITE_DEMO_MODE": "false",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)

        deadline = int(time.time()) + 3600
        body = {
            "action": "mint_zusd",
            "owner_pubkey": owner_pubkey,
            "sender_pubkey": owner_pubkey,
            "amount": 100,
            "deadline": deadline,
            "tx_fee_limit": "0",
        }
        signed_payload = _prepare_external_signed_zusd_payload(
            api_base=api_base,
            privkey=owner_privkey,
            body=body,
        )
        state_before = _app_state_from_tau_server(tau_server)
        status, api_rejected = _http_post_json_status(
            api_base + "/api/zusd/monetary/submit",
            {**body, "signed_tau_tx_payload": signed_payload},
        )
        assert status == 502
        assert api_rejected["ok"] is False
        assert api_rejected["error"] == "tau_rpc_error"
        assert _app_state_from_tau_server(tau_server) == state_before
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert rpc_state.pending_tx is not None
        assert rpc_state.sequences[owner_pubkey[2:].lower()] == 7
        stats = proxy.stats()
        assert stats.sendtx_requests == 1
        assert stats.truncated_sendtx_responses == 1

        query = urlencode(
            {
                "tab": "zusd",
                "demo": "false",
                "zenodexUiSmokeZusdMonetary": "1",
                "zusdMonetaryAction": "mint_zusd",
                "actorPubkey": owner_pubkey,
                "zusdAmount": "100",
                "zusdDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(
                    signed_payload, sort_keys=True, separators=(",", ":")
                ),
            }
        )
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={tmp_path / 'chrome-profile-zusd-proxy-truncate'}",
                "--virtual-time-budget=20000",
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
        assert "zUSD Monetary Vault" in dom
        assert "Tau node connected" in dom
        assert "tau_rpc_error" in dom, dom[-8000:]
        assert "SUCCESS tx accepted" not in dom
        assert _app_state_from_tau_server(tau_server) == state_before
        assert rpc_state.pending_tx is not None
        assert rpc_state.sequences[owner_pubkey[2:].lower()] == 7
        stats = proxy.stats()
        assert stats.sendtx_requests == 2
        assert stats.truncated_sendtx_responses == 2
    finally:
        vite_proc.terminate()
        api_proc.terminate()
        proxy.close()
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


@requires_toxiproxy
def test_zusd_monetary_wallet_browser_fails_closed_through_toxiproxy_limit_data(
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-zusd-monetary-ui-toxiproxy"
    owner_privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)
    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(
        ("0.0.0.0", tau_port), _TauRpcGatedSendSuccessHandler
    )
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(owner_pubkey=owner_pubkey, chain_id=chain_id)  # type: ignore[attr-defined]
    tau_server.send_response_event = threading.Event()  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_proc: subprocess.Popen[str] | None = None
    vite_proc: subprocess.Popen[str] | None = None
    chrome_proc: subprocess.Popen[str] | None = None
    try:
        with ToxiproxyHarness(upstream_host="0.0.0.0", upstream_port=tau_port) as toxiproxy:
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
                "ZUSD_MONETARY_WALLET_TAU_HOST": toxiproxy.listen_host,
                "ZUSD_MONETARY_WALLET_TAU_PORT": str(toxiproxy.listen_port),
                "ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S": "1.0",
                "TAU_DEX_CHAIN_ID": chain_id,
                "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
            vite_proc = subprocess.Popen(
                ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
                cwd=DEX_UI,
                env={
                    **os.environ,
                    "API_PROXY_TARGET": api_base,
                    "VITE_DEMO_MODE": "false",
                },
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )

            _wait_for_http(api_base + "/health", timeout_s=30)
            _wait_for_http(vite_base, timeout_s=30)

            deadline = int(time.time()) + 3600
            body = {
                "action": "mint_zusd",
                "owner_pubkey": owner_pubkey,
                "sender_pubkey": owner_pubkey,
                "amount": 100,
                "deadline": deadline,
                "tx_fee_limit": "0",
            }
            signed_payload = _prepare_external_signed_zusd_payload(
                api_base=api_base,
                privkey=owner_privkey,
                body=body,
            )
            state_before = _app_state_from_tau_server(tau_server)
            getappstate_before = _tau_command_count(tau_server, "getappstate")
            query = urlencode(
                {
                    "tab": "zusd",
                    "demo": "false",
                    "zenodexUiSmokeZusdMonetary": "1",
                    "zusdMonetaryAction": "mint_zusd",
                    "actorPubkey": owner_pubkey,
                    "zusdAmount": "100",
                    "zusdDeadline": str(deadline),
                    "signedTauTxPayload": json.dumps(
                        signed_payload, sort_keys=True, separators=(",", ":")
                    ),
                }
            )
            chrome_proc = subprocess.Popen(
                [
                    chrome,
                    "--headless=new",
                    "--disable-gpu",
                    "--no-sandbox",
                    f"--user-data-dir={tmp_path / 'chrome-profile-zusd-toxiproxy-limit-data'}",
                    "--virtual-time-budget=22000",
                    "--dump-dom",
                    f"{vite_base}/?{query}",
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            _wait_for_tau_command_count(tau_server, "getappstate", getappstate_before + 1)
            _wait_for_tau_command_count(tau_server, "sendtx", 1)
            toxiproxy.limit_data(7)
            tau_server.send_response_event.set()  # type: ignore[attr-defined]
            stdout, stderr = chrome_proc.communicate(timeout=70)
            assert chrome_proc.returncode == 0, stderr[-2000:]
            dom = stdout
            assert "zUSD Monetary Vault" in dom
            assert "Tau node connected" in dom
            assert "tau_rpc_error" in dom, dom[-8000:]
            assert "SUCCESS tx accepted" not in dom
            assert _app_state_from_tau_server(tau_server) == state_before
            rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
            assert rpc_state.pending_tx is not None
            assert rpc_state.sequences[owner_pubkey[2:].lower()] == 7
    finally:
        if chrome_proc is not None and chrome_proc.poll() is None:
            chrome_proc.kill()
            chrome_proc.wait(timeout=5)
        for proc in (vite_proc, api_proc):
            if proc is None:
                continue
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)


def test_zusd_monetary_wallet_browser_succeeds_under_bounded_tau_send_jitter(
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-zusd-monetary-ui-jitter"
    owner_privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)
    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(
        ("127.0.0.1", tau_port), _TauRpcDelayedSendSuccessHandler
    )
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(owner_pubkey=owner_pubkey, chain_id=chain_id)  # type: ignore[attr-defined]
    tau_server.send_delay_s = 0.15  # type: ignore[attr-defined]
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
        "ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S": "2.0",
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": api_base,
            "VITE_DEMO_MODE": "false",
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)

        state_before = _app_state_from_tau_server(tau_server)
        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="mint_zusd",
            amount=100,
            profile_name="chrome-profile-zusd-jitter",
            expected_snippets=('"debt_e8": 10000000000',),
        )
        state_after = _app_state_from_tau_server(tau_server)
        assert _zusd_core(state_after)["debt_e8"] == _zusd_core(state_before)["debt_e8"] + (
            100 * E8
        )
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[owner_pubkey[2:].lower()] == 8
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
    keeper_privkey = 83
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(owner_privkey)
    keeper_pubkey = "0x" + bls_pubkey_hex_from_privkey(keeper_privkey)
    asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)
    sp_pubkey = stability_pool_pubkey(chain_id=chain_id)

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
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": owner_pubkey,
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
        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="deposit_collateral",
            profile_name="chrome-profile-deposit-collateral",
            amount_e8=E8,
            expected_snippets=('"action": "deposit_collateral"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _zusd_core(app_state)["collateral_e8"] == 21 * E8
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert rpc_state.native_balances[owner_pubkey.lower()] == 4 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="withdraw_collateral",
            profile_name="chrome-profile-withdraw-collateral",
            amount_e8=E8,
            expected_snippets=('"action": "withdraw_collateral"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _zusd_core(app_state)["collateral_e8"] == 20 * E8
        assert rpc_state.native_balances[owner_pubkey.lower()] == 5 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="mint_zusd",
            profile_name="chrome-profile-mint",
            amount=1000,
            expected_snippets=('"debt_e8": 100000000000',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 1000
        assert _zusd_core(app_state)["debt_e8"] == 1000 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="redeem_zusd",
            profile_name="chrome-profile-redeem",
            amount=100,
            expected_snippets=('"action": "redeem_zusd"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 900
        assert _zusd_core(app_state)["debt_e8"] == 900 * E8
        assert _zusd_core(app_state)["collateral_e8"] == 19 * E8
        assert rpc_state.native_balances[owner_pubkey.lower()] == 6 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="mint_zusd",
            profile_name="chrome-profile-post-redeem-remint",
            amount=100,
            expected_snippets=('"debt_e8": 100000000000',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 1000
        assert _zusd_core(app_state)["debt_e8"] == 1000 * E8
        assert _zusd_core(app_state)["collateral_e8"] == 19 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="repay_zusd",
            profile_name="chrome-profile-repay",
            amount=100,
            expected_snippets=('"action": "repay_zusd"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 900
        assert _zusd_core(app_state)["debt_e8"] == 900 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="mint_zusd",
            profile_name="chrome-profile-remint",
            amount=100,
            expected_snippets=('"debt_e8": 100000000000',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 1000
        assert _zusd_core(app_state)["debt_e8"] == 1000 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="deposit_sp",
            profile_name="chrome-profile-deposit-sp",
            amount=1000,
            expected_snippets=('"action": "deposit_sp"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 0
        assert _balance_for_asset(app_state, pubkey=sp_pubkey, asset_id=asset_id) == 1000
        assert _zusd_core(app_state)["sp_debt_e8"] == 1000 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="withdraw_sp",
            profile_name="chrome-profile-withdraw-sp",
            amount=100,
            expected_snippets=('"action": "withdraw_sp"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 100
        assert _balance_for_asset(app_state, pubkey=sp_pubkey, asset_id=asset_id) == 900
        assert _zusd_core(app_state)["sp_debt_e8"] == 900 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="deposit_sp",
            profile_name="chrome-profile-redeposit-sp",
            amount=100,
            expected_snippets=('"action": "deposit_sp"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _balance_for_asset(app_state, pubkey=owner_pubkey, asset_id=asset_id) == 0
        assert _balance_for_asset(app_state, pubkey=sp_pubkey, asset_id=asset_id) == 1000
        assert _zusd_core(app_state)["sp_debt_e8"] == 1000 * E8

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="oracle_report",
            profile_name="chrome-profile-oracle-report",
            price_e8=50 * E8,
            expected_snippets=('"price_e8": 5000000000',),
        )

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=keeper_privkey,
            actor_pubkey=keeper_pubkey,
            action="liquidate",
            profile_name="chrome-profile-liquidate",
            expected_snippets=('"action": "liquidate"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        core = _zusd_core(app_state)
        assert core["debt_e8"] == 0
        assert core["sp_debt_e8"] == 0
        assert _balance_for_asset(app_state, pubkey=sp_pubkey, asset_id=asset_id) == 0
        assert _sp_claims(app_state) == {owner_pubkey: 19 * E8}

        _run_zusd_browser_submit(
            chrome=chrome,
            tmp_path=tmp_path,
            vite_base=vite_base,
            api_base=api_base,
            privkey=owner_privkey,
            actor_pubkey=owner_pubkey,
            action="claim_sp_collateral",
            profile_name="chrome-profile-claim-sp",
            amount_e8=19 * E8,
            expected_snippets=('"action": "claim_sp_collateral"',),
        )
        app_state = _app_state_from_tau_server(tau_server)
        assert _zusd_core(app_state)["sp_coll_e8"] == 0
        assert _sp_claims(app_state) == {}
        assert rpc_state.native_balances[owner_pubkey.lower()] == 25 * E8
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
