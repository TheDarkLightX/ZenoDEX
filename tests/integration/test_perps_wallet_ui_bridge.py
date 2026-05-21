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

from src.core.dex import DexState
from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
from src.integration import tau_testnet_dex_plugin as plugin
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.perp_engine import PerpEngineConfig, _kernel_initial_global_state, apply_perp_ops
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction, sign_perp_op_for_engine
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
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


def _initial_app_state_json(dex_state: DexState | None = None) -> str:
    if dex_state is None:
        dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    payload = {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": None,
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def _advanced_market_state(
    *,
    chain_id: str,
    market_id: str,
    quote_asset: str,
    account_a_privkey: int,
    account_b_privkey: int,
    oracle_pubkey: str,
) -> DexState:
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    init_op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": account_a_pubkey,
        "account_b_pubkey": account_b_pubkey,
        "deadline": 999_999_999,
        "nonce_a": 1,
        "nonce_b": 1,
    }
    init_op["sig_a"] = sign_perp_op_for_engine(
        init_op,
        privkey=account_a_privkey,
        chain_id=chain_id,
        signer_pubkey=account_a_pubkey,
        nonce=1,
    )
    init_op["sig_b"] = sign_perp_op_for_engine(
        init_op,
        privkey=account_b_privkey,
        chain_id=chain_id,
        signer_pubkey=account_b_pubkey,
        nonce=1,
    )
    cfg = PerpEngineConfig(chain_id=chain_id, oracle_pubkey=oracle_pubkey)
    res1 = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [init_op]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=1,
    )
    assert res1.ok, res1.error
    assert res1.state is not None
    res2 = apply_perp_ops(
        config=cfg,
        state=res1.state,
        operations={"5": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "advance_epoch", "delta": 1}]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=2,
    )
    assert res2.ok, res2.error
    assert res2.state is not None
    return res2.state


def _settle_ready_market_state(
    *,
    chain_id: str,
    market_id: str,
    quote_asset: str,
    account_a_privkey: int,
    account_b_privkey: int,
    oracle_privkey: int,
) -> DexState:
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "publish_clearing_price",
        "price_e8": 100_000_000,
        "deadline": 999_999_999,
        "oracle_nonce": 1,
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=oracle_privkey,
        chain_id=chain_id,
        signer_pubkey=oracle_pubkey,
        nonce=1,
    )
    cfg = PerpEngineConfig(chain_id=chain_id, oracle_pubkey=oracle_pubkey)
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [op]},
        tx_sender_pubkey=oracle_pubkey,
        block_timestamp=3,
    )
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _signed_set_position_pair(
    *,
    chain_id: str,
    market_id: str,
    account_a_privkey: int,
    account_b_privkey: int,
    new_a: int,
    new_b: int,
    nonce_a: int,
    nonce_b: int,
) -> dict[str, object]:
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "set_position_pair",
        "account_a_pubkey": account_a_pubkey,
        "account_b_pubkey": account_b_pubkey,
        "new_position_base_a": int(new_a),
        "new_position_base_b": int(new_b),
        "deadline": 999_999_999,
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(
        op,
        privkey=account_a_privkey,
        chain_id=chain_id,
        signer_pubkey=account_a_pubkey,
        nonce=nonce_a,
    )
    op["sig_b"] = sign_perp_op_for_engine(
        op,
        privkey=account_b_privkey,
        chain_id=chain_id,
        signer_pubkey=account_b_pubkey,
        nonce=nonce_b,
    )
    return op


def _signed_publish_price(
    *,
    chain_id: str,
    market_id: str,
    oracle_privkey: int,
    price_e8: int,
    oracle_nonce: int,
) -> dict[str, object]:
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "publish_clearing_price",
        "price_e8": int(price_e8),
        "deadline": 999_999_999,
        "oracle_nonce": int(oracle_nonce),
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=oracle_privkey,
        chain_id=chain_id,
        signer_pubkey=oracle_pubkey,
        nonce=oracle_nonce,
    )
    return op


def _liquidation_ready_market_state(
    *,
    chain_id: str,
    market_id: str,
    quote_asset: str,
    account_a_privkey: int,
    account_b_privkey: int,
    oracle_privkey: int,
) -> DexState:
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    cfg = PerpEngineConfig(chain_id=chain_id, oracle_pubkey=oracle_pubkey)
    state = _settle_ready_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_privkey=oracle_privkey,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "settle_epoch"}]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=4,
    )
    assert res.ok, res.error
    assert res.state is not None
    state = res.state
    state.balances.set(account_a_pubkey, quote_asset, 1000)
    state.balances.set(account_b_pubkey, quote_asset, 1000)
    for sender, op in (
        (
            account_a_pubkey,
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": market_id,
                "action": "deposit_collateral",
                "account_pubkey": account_a_pubkey,
                "amount": 100,
            },
        ),
        (
            account_b_pubkey,
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": market_id,
                "action": "deposit_collateral",
                "account_pubkey": account_b_pubkey,
                "amount": 100,
            },
        ),
    ):
        res = apply_perp_ops(config=cfg, state=state, operations={"5": [op]}, tx_sender_pubkey=sender, block_timestamp=5)
        assert res.ok, res.error
        assert res.state is not None
        state = res.state
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "5": [
                _signed_set_position_pair(
                    chain_id=chain_id,
                    market_id=market_id,
                    account_a_privkey=account_a_privkey,
                    account_b_privkey=account_b_privkey,
                    new_a=1000,
                    new_b=-1000,
                    nonce_a=2,
                    nonce_b=2,
                )
            ]
        },
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=6,
    )
    assert res.ok, res.error
    assert res.state is not None
    state = res.state
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "advance_epoch", "delta": 1}]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=7,
    )
    assert res.ok, res.error
    assert res.state is not None
    res = apply_perp_ops(
        config=cfg,
        state=res.state,
        operations={
            "5": [
                _signed_publish_price(
                    chain_id=chain_id,
                    market_id=market_id,
                    oracle_privkey=oracle_privkey,
                    price_e8=105_000_000,
                    oracle_nonce=2,
                )
            ]
        },
        tx_sender_pubkey=oracle_pubkey,
        block_timestamp=8,
    )
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _isolated_liquidation_ready_market_state(
    *,
    market_id: str,
    quote_asset: str,
    account_privkey: int,
) -> DexState:
    account_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_privkey)
    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 5,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 10_000_000_000,
            "max_oracle_staleness_epochs": 100,
            "max_oracle_move_bps": 500,
            "initial_margin_bps": 1000,
            "maintenance_margin_bps": 500,
            "depeg_buffer_bps": 100,
            "liquidation_penalty_bps": 50,
            "max_position_abs": 1_000_000,
            "fee_pool_quote": 0,
            "fee_income": 0,
            "insurance_balance": 100_000,
            "initial_insurance": 100_000,
            "claims_paid": 0,
            "min_notional_for_bounty": 100_000_000,
        }
    )
    market = PerpMarketState(
        quote_asset=quote_asset,
        global_state=global_state,
        accounts={
            account_pubkey: PerpAccountState(
                position_base=100,
                entry_price_e8=10_000_000_000,
                collateral_quote=300,
                funding_paid_cumulative=0,
                funding_last_applied_epoch=0,
                liquidated_this_step=False,
            )
        },
    )
    return DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={market_id: market}),
    )


class _TauRpcState:
    def __init__(self, *, app_state_json: str | None = None) -> None:
        self.app_state_json = app_state_json or _initial_app_state_json()
        self.app_hash = "ef" * 32
        self.pending_tx: dict[str, object] | None = None
        self.sequences: dict[str, int] = {}
        self.native_balances: dict[str, int] = {}
        self.lock = threading.Lock()

    def app_state_payload(self) -> dict[str, object]:
        return {"app_hash": self.app_hash, "app_state": json.loads(self.app_state_json)}

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
            self.wfile.write(f"BALANCE: {state.native_balances.get(pubkey, 0)}\n".encode("utf-8"))
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


def test_perps_wallet_ui_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui"
    account_a_privkey = 83
    account_b_privkey = 84
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui"

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState()  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = 4  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
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
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "init_market_2p",
                "marketId": market_id,
                "quoteAsset": quote_asset,
                "accountAPrivkey": str(account_a_privkey),
                "accountBPrivkey": str(account_b_privkey),
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
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
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=50,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Stream" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "fee limit 2" in dom
        assert "fee covered yes" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_accepts_external_signed_payload_without_local_signing(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-external"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(85)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-external"
    deadline = int(time.time()) + 3600
    sequence_number = 7
    deposit_amount = 125

    dex_state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    dex_state.balances.set(account_a_pubkey, quote_asset, 1000)
    app_state_json = _initial_app_state_json(dex_state)
    signed_payload = build_signed_tau_transaction(
        privkey=account_a_privkey,
        sequence_number=sequence_number,
        expiration_time=deadline,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": account_a_pubkey,
                    "amount": deposit_amount,
                }
            ]
        },
        fee_limit=2,
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = sequence_number  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "false",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
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
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "deposit_collateral",
                "marketId": market_id,
                "accountPubkey": account_a_pubkey,
                "amount": str(deposit_amount),
                "txFeeLimit": "2",
                "perpsDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
            }
        )
        chrome_profile = tmp_path / "chrome-profile-external-signed"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=20000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=50,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Deposit Collateral" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "fee limit 2" in dom
        assert "fee covered yes" in dom
        assert "signing external_signed_payload" in dom
        assert "posted A 12500000000" in dom
        assert "quote A 875" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_publish_price_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-price"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_privkey = 85
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-price"
    app_state_json = _initial_app_state_json(
        _advanced_market_state(
            chain_id=chain_id,
            market_id=market_id,
            quote_asset=quote_asset,
            account_a_privkey=account_a_privkey,
            account_b_privkey=account_b_privkey,
            oracle_pubkey=oracle_pubkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[oracle_pubkey[2:].lower()] = 6  # type: ignore[attr-defined]
    tau_server.state.native_balances[oracle_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_PERP_ORACLE_PUBKEY": oracle_pubkey,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_oracle = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_PERP_ORACLE_PUBKEY"] = oracle_pubkey
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
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "publish_clearing_price",
                "marketId": market_id,
                "oraclePrivkey": str(oracle_privkey),
                "priceE8": "100000000",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            }
        )
        chrome_profile = tmp_path / "chrome-profile-price"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=20000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=50,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Publish Price" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "fee limit 2" in dom
        assert "fee covered yes" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_oracle is None:
            os.environ.pop("TAU_DEX_PERP_ORACLE_PUBKEY", None)
        else:
            os.environ["TAU_DEX_PERP_ORACLE_PUBKEY"] = old_oracle
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-settle"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_privkey = 85
    operator_privkey = 86
    operator_pubkey = "0x" + bls_pubkey_hex_from_privkey(operator_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-settle"
    app_state_json = _initial_app_state_json(
        _settle_ready_market_state(
            chain_id=chain_id,
            market_id=market_id,
            quote_asset=quote_asset,
            account_a_privkey=account_a_privkey,
            account_b_privkey=account_b_privkey,
            oracle_privkey=oracle_privkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[operator_pubkey[2:].lower()] = 8  # type: ignore[attr-defined]
    tau_server.state.native_balances[operator_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_OPERATOR_PUBKEY": operator_pubkey,
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH": "1",
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_operator = os.environ.get("TAU_DEX_OPERATOR_PUBKEY")
    old_require = os.environ.get("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_OPERATOR_PUBKEY"] = operator_pubkey
    os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = "1"
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
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "settle_epoch",
                "marketId": market_id,
                "operatorPrivkey": str(operator_privkey),
                "perpsUseOracleFixture": "1",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            }
        )
        chrome_profile = tmp_path / "chrome-profile-settle"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
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
        assert "Live Perps Wallet" in dom
        assert "Settle Epoch" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "oracle bridge sha256:" in dom
        assert "oracle evidence accepted" in dom
        assert "oracle action settle_epoch" in dom
        assert "oracle value 100000000" in dom
        assert "oracle reports 3" in dom
        assert "oracle production local" in dom
        assert "fee covered yes" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_operator is None:
            os.environ.pop("TAU_DEX_OPERATOR_PUBKEY", None)
        else:
            os.environ["TAU_DEX_OPERATOR_PUBKEY"] = old_operator
        if old_require is None:
            os.environ.pop("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", None)
        else:
            os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = old_require
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-partial-liquidate"
    account_privkey = 87
    account_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:isolated:ui-liquidation"
    app_state_json = _initial_app_state_json(
        _isolated_liquidation_ready_market_state(
            market_id=market_id,
            quote_asset=quote_asset,
            account_privkey=account_privkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_pubkey[2:].lower()] = 6  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_ALLOW_ISOLATED_PERPS": "1",
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE": "1",
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_allow_isolated = os.environ.get("TAU_DEX_ALLOW_ISOLATED_PERPS")
    old_require = os.environ.get("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_ALLOW_ISOLATED_PERPS"] = "1"
    os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE"] = "1"
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
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "partial_liquidate",
                "marketId": market_id,
                "accountPrivkey": str(account_privkey),
                "fractionBps": "0",
                "perpsUseOracleFixture": "1",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            }
        )
        chrome_profile = tmp_path / "chrome-profile-partial-liquidation"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
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
        assert "Live Perps Wallet" in dom
        assert "Partial Liquidate" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "oracle bridge sha256:" in dom
        assert "partial liquidation fraction 0 bps" in dom
        assert "isolated liquidated yes" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_allow_isolated is None:
            os.environ.pop("TAU_DEX_ALLOW_ISOLATED_PERPS", None)
        else:
            os.environ["TAU_DEX_ALLOW_ISOLATED_PERPS"] = old_allow_isolated
        if old_require is None:
            os.environ.pop("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE", None)
        else:
            os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE"] = old_require
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_settle_epoch_reports_liquidation_evidence(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-liquidation"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_privkey = 85
    operator_privkey = 86
    operator_pubkey = "0x" + bls_pubkey_hex_from_privkey(operator_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-liquidation"
    app_state_json = _initial_app_state_json(
        _liquidation_ready_market_state(
            chain_id=chain_id,
            market_id=market_id,
            quote_asset=quote_asset,
            account_a_privkey=account_a_privkey,
            account_b_privkey=account_b_privkey,
            oracle_privkey=oracle_privkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[operator_pubkey[2:].lower()] = 9  # type: ignore[attr-defined]
    tau_server.state.native_balances[operator_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_OPERATOR_PUBKEY": operator_pubkey,
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH": "1",
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_operator = os.environ.get("TAU_DEX_OPERATOR_PUBKEY")
    old_require = os.environ.get("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_OPERATOR_PUBKEY"] = operator_pubkey
    os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = "1"
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
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "settle_epoch",
                "marketId": market_id,
                "operatorPrivkey": str(operator_privkey),
                "perpsUseOracleFixture": "1",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            }
        )
        chrome_profile = tmp_path / "chrome-profile-liquidation"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
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
        assert "Live Perps Wallet" in dom
        assert "Settle Epoch" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "oracle bridge sha256:" in dom
        assert "liquidated yes" in dom
        assert "fee pool 525000000" in dom
        assert "positions 0/0" in dom
        assert "quote A 900" in dom
        assert "quote B 900" in dom
        assert "posted A 15000000000" in dom
        assert "posted B 4475000000" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_operator is None:
            os.environ.pop("TAU_DEX_OPERATOR_PUBKEY", None)
        else:
            os.environ["TAU_DEX_OPERATOR_PUBKEY"] = old_operator
        if old_require is None:
            os.environ.pop("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", None)
        else:
            os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = old_require
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
