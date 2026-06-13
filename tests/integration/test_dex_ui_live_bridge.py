from __future__ import annotations

import json
import os
import shutil
import socket
import subprocess
import threading
import time
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import Request, urlopen

import pytest

from tests.integration.vite_test_server import vite_dev_command
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_ASSET0,
    DEFAULT_ASSET1,
    DEFAULT_BOOTSTRAP_SENDER,
)
from tools.zeno_ledger_node import make_node_http_server_v0, run_node_once_v0

ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"
LIVE_BRIDGE_CHAIN_ID = "zenodex-ui-live-bridge-testnet"
LIVE_BRIDGE_SIGNER_PRIVKEY = 17


def _read_url_json(url: str, *, timeout: float = 5) -> dict[str, object]:
    with urlopen(url, timeout=timeout) as response:  # noqa: S310 - local test server
        payload = response.read().decode("utf-8")
    obj = json.loads(payload)
    assert isinstance(obj, dict)
    return obj


def _post_url_json(url: str, value: dict[str, object], *, timeout: float = 5) -> dict[str, object]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    request = Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urlopen(request, timeout=timeout) as response:  # noqa: S310 - local test server
        body = response.read().decode("utf-8")
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj


def _signed_swap_fields(
    *,
    pool: dict[str, object],
    sender_pubkey: str,
    privkey: int,
    nonce: int,
    amount_in: int,
    min_amount_out: int,
    deadline: int,
) -> dict[str, object]:
    from src.integration.tau_net_client import sign_dex_intent_for_engine
    from src.integration.zeno_ledger_v0 import hash_v0

    pool_id = str(pool["pool_id"])
    intent_payload = {
        "sender_pubkey": sender_pubkey,
        "recipient": sender_pubkey,
        "pool_id": pool_id,
        "asset_in": DEFAULT_ASSET0,
        "asset_out": DEFAULT_ASSET1,
        "amount_in": amount_in,
        "min_amount_out": min_amount_out,
        "nonce": nonce,
    }
    operation = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": hash_v0("ui_swap_intent_v0", intent_payload),
        "sender_pubkey": sender_pubkey,
        "deadline": deadline,
        "nonce": nonce,
        "pool_id": pool_id,
        "asset_in": DEFAULT_ASSET0,
        "asset_out": DEFAULT_ASSET1,
        "amount_in": amount_in,
        "min_amount_out": min_amount_out,
        "recipient": sender_pubkey,
    }
    return {
        "nonce": nonce,
        "deadline": deadline,
        "signature": sign_dex_intent_for_engine(
            operation,
            privkey=privkey,
            chain_id=LIVE_BRIDGE_CHAIN_ID,
        ),
    }


def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _wait_for_http(url: str, *, timeout_s: float = 30) -> None:
    deadline = time.monotonic() + timeout_s
    last_error: Exception | None = None
    while time.monotonic() < deadline:
        try:
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test server
                response.read(1)
            return
        except Exception as exc:  # pragma: no cover - failure path reports last error
            last_error = exc
            time.sleep(0.2)
    raise AssertionError(f"server did not become ready at {url}: {last_error}")


def _live_height(node_base_url: str) -> int:
    live = _read_url_json(f"{node_base_url}/live")
    if live.get("live") is True:
        state = live.get("state")
        assert isinstance(state, dict)
        return int(state["latest_height"])
    status = _read_url_json(f"{node_base_url}/status")
    return int(status["latest_height"])


def _wait_for_live_height(node_base_url: str, *, min_height: int, timeout_s: float = 20) -> int:
    deadline = time.monotonic() + timeout_s
    last_height = -1
    while time.monotonic() < deadline:
        last_height = _live_height(node_base_url)
        if last_height >= min_height:
            return last_height
        time.sleep(0.25)
    raise AssertionError(f"node height did not reach {min_height}; last_height={last_height}")


def _chrome_binary() -> str | None:
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


@pytest.fixture(scope="module")
def live_node(tmp_path_factory: pytest.TempPathFactory) -> tuple[str, Path]:
    tmp_path = tmp_path_factory.mktemp("dex-ui-live-bridge")
    bundle_root = tmp_path / "bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=bundle_root,
        network_id=LIVE_BRIDGE_CHAIN_ID,
        chain_id=LIVE_BRIDGE_CHAIN_ID,
        sequencer_id="sequencer-ui-live-bridge",
        time_ms=1_778_740_000_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    node_dir = tmp_path / "node"
    peer_attestation = bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    node_report = run_node_once_v0(
        bundle_root=bundle_root,
        node_id="ui-live-bridge-node",
        data_dir=node_dir,
        peer_watcher_attestation_paths=[peer_attestation],
    )
    assert node_report["ok"] is True

    server = make_node_http_server_v0(
        data_dir=node_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        expose_testnet_faucet_http=True,
        allow_unauthenticated_testnet_writes=True,
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address
    try:
        yield f"http://{host}:{port}", node_dir
    finally:
        server.shutdown()
        server.server_close()


def _fund_smoke_sender(node_base_url: str, *, tx_id: str, to_pubkey: str = DEFAULT_BOOTSTRAP_SENDER) -> dict[str, object]:
    return _post_url_json(
        f"{node_base_url}/faucet",
        {
            "to_pubkey": to_pubkey,
            "asset": DEFAULT_ASSET0,
            "amount": 10_000,
            "local_fixture_mode": True,
            "time_ms": 1_778_740_100_000,
            "tx_id": tx_id,
        },
    )


def test_live_node_serves_ui_pools_and_accepts_ui_swap(live_node: tuple[str, Path]) -> None:
    pytest.importorskip("py_ecc.bls")
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey

    node_base_url, _node_dir = live_node
    sender_pubkey = "0x" + bls_pubkey_hex_from_privkey(LIVE_BRIDGE_SIGNER_PRIVKEY)
    faucet_report = _fund_smoke_sender(
        node_base_url,
        tx_id="ui-live-bridge-api-faucet-v0",
        to_pubkey=sender_pubkey,
    )
    assert faucet_report["ok"] is True

    pools = _read_url_json(f"{node_base_url}/api/pools?{urlencode({'account': sender_pubkey})}")
    assert pools["ok"] is True
    pool_rows = pools["pools"]
    assert isinstance(pool_rows, list)
    assert len(pool_rows) >= 1
    first_pool = pool_rows[0]
    assert isinstance(first_pool, dict)
    assert first_pool["token0"] == "AGRS"
    assert first_pool["token1"] == "zDEX"
    assert first_pool["asset0"] == DEFAULT_ASSET0
    assert first_pool["asset1"] == DEFAULT_ASSET1

    nonce = int(pools.get("account_last_nonce", 0)) + 1
    deadline = 1_999_999_999
    signed = _signed_swap_fields(
        pool=first_pool,
        sender_pubkey=sender_pubkey,
        privkey=LIVE_BRIDGE_SIGNER_PRIVKEY,
        nonce=nonce,
        amount_in=100,
        min_amount_out=1,
        deadline=deadline,
    )
    pre_height = _live_height(node_base_url)
    swap_report = _post_url_json(
        f"{node_base_url}/api/swap",
        {
            "from": "AGRS",
            "to": "zDEX",
            "poolId": first_pool["pool_id"],
            "amountIn": 100,
            "minAmountOut": 1,
            "senderPubkey": sender_pubkey,
            "recipient": sender_pubkey,
            "nonce": signed["nonce"],
            "deadline": signed["deadline"],
            "signature": signed["signature"],
            "time_ms": 1_778_740_101_000,
        },
    )
    assert swap_report["ok"] is True
    assert swap_report["height"] == pre_height + 1
    assert swap_report["tx_accepted"] is True
    receipt = swap_report["receipt"]
    assert isinstance(receipt, dict)
    assert receipt["accepted"] is True


def test_pools_balance_consistency_across_swap_and_pool_surfaces(live_node: tuple[str, Path]) -> None:
    """Regression for the community bug (swap/pool side): a funded account must show the
    SAME token balance on the Pool surface and the Swap surface.

    Both surfaces read the same ``/api/pools?account=`` row. ``PoolDashboard`` reads
    ``accountBalance0 ?? account_balance0`` (and ...1); ``swapData.loadSwapPools`` aggregates
    ``accountBalance0 ?? account_balance0`` into the swap feed's balances. The node derives
    both from the single ledger source ``account_state.balances[account][asset]`` and emits
    snake_case + camelCase mirrors. This asserts (a) the funded balances are present and
    positive after a faucet, and (b) the camelCase mirror exactly equals the snake_case value,
    so the two surfaces cannot diverge.
    """
    pytest.importorskip("py_ecc.bls")
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey

    node_base_url, _node_dir = live_node
    sender_pubkey = "0x" + bls_pubkey_hex_from_privkey(LIVE_BRIDGE_SIGNER_PRIVKEY)
    faucet_report = _fund_smoke_sender(
        node_base_url,
        tx_id="ui-live-bridge-balance-consistency-faucet-v0",
        to_pubkey=sender_pubkey,
    )
    assert faucet_report["ok"] is True

    pools = _read_url_json(f"{node_base_url}/api/pools?{urlencode({'account': sender_pubkey})}")
    assert pools["ok"] is True
    assert pools.get("account") == sender_pubkey
    pool_rows = pools["pools"]
    assert isinstance(pool_rows, list) and pool_rows

    # The faucet funded asset0 for this account, so at least one pool must report a
    # positive account_balance0. Locate it deterministically.
    funded_rows = [
        row
        for row in pool_rows
        if isinstance(row, dict) and int(row.get("account_balance0", 0)) > 0
    ]
    assert funded_rows, "faucet should have funded asset0 for at least one pool's account_balance0"

    for row in pool_rows:
        assert isinstance(row, dict)
        # The node MUST emit every per-account field when an account is supplied, and the
        # camelCase mirror (read by PoolDashboard / the swap normalizer's `?? camelCase`
        # branch) MUST equal the snake_case value the other branch reads. Equal mirrors are
        # exactly what makes the two surfaces observe an identical balance.
        for snake, camel in (
            ("account_balance0", "accountBalance0"),
            ("account_balance1", "accountBalance1"),
            ("account_lp_balance", "accountLpBalance"),
        ):
            assert snake in row, f"live account row missing {snake}"
            assert camel in row, f"live account row missing {camel}"
            assert int(row[snake]) == int(row[camel]), (
                f"snake/camel balance mirror diverged: {snake}={row[snake]} {camel}={row[camel]}"
            )

    # Cross-surface balance: emulate the Pool accessor and the Swap accessor over the SAME
    # row and assert they agree. Pool reads per-token0; Swap aggregates per-symbol balances.
    funded = funded_rows[0]
    pool_balance0 = int(funded["accountBalance0"])  # PoolDashboard.normalizeLivePool
    swap_balance0 = int(funded["account_balance0"])  # swapData.normalizePoolEntry -> accountBalances
    assert pool_balance0 == swap_balance0 > 0


def test_pools_without_account_fabricate_no_balances(live_node: tuple[str, Path]) -> None:
    """Fail-closed: with NO connected wallet (no ``account`` query param), the pool feed must
    not expose any per-account balance fields. Neither the Swap nor the Pool surface can then
    fabricate a funded-looking state. No BLS dependency: this runs even without py_ecc.
    """
    node_base_url, _node_dir = live_node
    pools = _read_url_json(f"{node_base_url}/api/pools")
    assert pools["ok"] is True
    pool_rows = pools["pools"]
    assert isinstance(pool_rows, list) and pool_rows
    for row in pool_rows:
        assert isinstance(row, dict)
        for forbidden in (
            "account",
            "account_balance0",
            "accountBalance0",
            "account_balance1",
            "accountBalance1",
            "account_lp_balance",
            "accountLpBalance",
        ):
            assert forbidden not in row, (
                f"anonymous /api/pools row must not include {forbidden} (would fabricate a balance)"
            )
    # The top-level account echo must also be absent/empty without a connected wallet.
    assert not pools.get("account")


def test_dex_ui_smoke_submits_live_swap_through_browser(
    live_node: tuple[str, Path],
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")
    pytest.importorskip("py_ecc.bls")
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey

    node_base_url, node_dir = live_node
    sender_pubkey = "0x" + bls_pubkey_hex_from_privkey(LIVE_BRIDGE_SIGNER_PRIVKEY)
    faucet_report = _fund_smoke_sender(
        node_base_url,
        tx_id="ui-live-bridge-browser-faucet-v0",
        to_pubkey=sender_pubkey,
    )
    assert faucet_report["ok"] is True
    pools = _read_url_json(f"{node_base_url}/api/pools?{urlencode({'account': sender_pubkey})}")
    pool_rows = pools["pools"]
    assert isinstance(pool_rows, list) and pool_rows
    nonce = int(pools.get("account_last_nonce", 0)) + 1
    deadline = 1_999_999_999
    signed = _signed_swap_fields(
        pool=dict(pool_rows[0]),
        sender_pubkey=sender_pubkey,
        privkey=LIVE_BRIDGE_SIGNER_PRIVKEY,
        nonce=nonce,
        amount_in=100,
        min_amount_out=1,
        deadline=deadline,
    )
    pre_height = _live_height(node_base_url)

    vite_port = _free_port()
    vite_base_url = f"http://127.0.0.1:{vite_port}"
    env = {
        **os.environ,
        "API_PROXY_TARGET": node_base_url,
        "VITE_DEMO_MODE": "false",
    }
    vite = subprocess.Popen(
        vite_dev_command(DEX_UI, vite_port),
        cwd=DEX_UI,
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    try:
        _wait_for_http(vite_base_url, timeout_s=30)
        query = urlencode(
            {
                "tab": "swap",
                "demo": "false",
                "zenodexUiSmokeSwap": "1",
                "walletAddress": sender_pubkey,
                "smokeAmountIn": "100",
                "smokeMinAmountOut": "1",
                "smokeNonce": str(signed["nonce"]),
                "smokeDeadline": str(signed["deadline"]),
                "smokeIntentSignature": str(signed["signature"]),
                "smokeFromSymbol": "AGRS",
                "smokeToSymbol": "zDEX",
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
                f"{vite_base_url}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=40,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        height = _wait_for_live_height(node_base_url, min_height=pre_height + 1, timeout_s=20)
        report_path = node_dir / "append_reports" / f"{height}.json"
        report = json.loads(report_path.read_text(encoding="utf-8"))
        assert report["receipt"]["accepted"] is True
        assert report["height"] == height
    finally:
        vite.terminate()
        try:
            vite.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite.kill()
            vite.wait(timeout=5)
