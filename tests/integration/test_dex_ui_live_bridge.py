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

from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_ASSET0,
    DEFAULT_ASSET1,
    DEFAULT_BOOTSTRAP_SENDER,
)
from tools.zeno_ledger_node import make_node_http_server_v0, run_node_once_v0

ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"


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
        network_id="zenodex-ui-live-bridge-testnet",
        chain_id="zenodex-ui-live-bridge-testnet",
        sequencer_id="sequencer-ui-live-bridge",
        time_ms=1_778_740_000_000,
        token_symbol="tZENO",
    )
    assert build_report["ok"] is True

    node_dir = tmp_path / "node"
    peer_attestation = (
        bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    )
    node_report = run_node_once_v0(
        bundle_root=bundle_root,
        node_id="ui-live-bridge-node",
        data_dir=node_dir,
        peer_watcher_attestation_paths=[peer_attestation],
    )
    assert node_report["ok"] is True

    # The browser fixture has no production credential channel. The node
    # enforces that this explicit unauthenticated mode is loopback-only.
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


def _fund_smoke_sender(node_base_url: str, *, tx_id: str) -> dict[str, object]:
    return _post_url_json(
        f"{node_base_url}/faucet",
        {
            "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
            "asset": DEFAULT_ASSET0,
            "amount": 10_000,
            "time_ms": 1_778_740_100_000,
            "tx_id": tx_id,
            "local_fixture_mode": True,
        },
    )


def test_live_node_serves_ui_pools_and_accepts_ui_swap(live_node: tuple[str, Path]) -> None:
    node_base_url, _node_dir = live_node
    faucet_report = _fund_smoke_sender(node_base_url, tx_id="ui-live-bridge-api-faucet-v0")
    assert faucet_report["ok"] is True

    pools = _read_url_json(f"{node_base_url}/api/pools")
    assert pools["ok"] is True
    pool_rows = pools["pools"]
    assert isinstance(pool_rows, list)
    assert len(pool_rows) >= 1
    target_pool = next(
        (
            row
            for row in pool_rows
            if isinstance(row, dict)
            and row.get("token0") == "tAGRS"
            and row.get("token1") == "tZDEX"
            and row.get("asset0") == DEFAULT_ASSET0
            and row.get("asset1") == DEFAULT_ASSET1
        ),
        None,
    )
    assert isinstance(target_pool, dict)

    pre_height = _live_height(node_base_url)
    swap_report = _post_url_json(
        f"{node_base_url}/api/swap",
        {
            "from": "tAGRS",
            "to": "tZDEX",
            "poolId": target_pool["pool_id"],
            "amountIn": 100,
            "minAmountOut": 1,
            "senderPubkey": DEFAULT_BOOTSTRAP_SENDER,
            "recipient": DEFAULT_BOOTSTRAP_SENDER,
            "time_ms": 1_778_740_101_000,
        },
    )
    assert swap_report["ok"] is True
    assert swap_report["height"] == pre_height + 1
    assert swap_report["tx_accepted"] is True
    receipt = swap_report["receipt"]
    assert isinstance(receipt, dict)
    assert receipt["accepted"] is True


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

    node_base_url, node_dir = live_node
    faucet_report = _fund_smoke_sender(node_base_url, tx_id="ui-live-bridge-browser-faucet-v0")
    assert faucet_report["ok"] is True
    pre_height = _live_height(node_base_url)

    vite_port = _free_port()
    vite_base_url = f"http://127.0.0.1:{vite_port}"
    env = {
        **os.environ,
        "API_PROXY_TARGET": node_base_url,
        "VITE_DEMO_MODE": "false",
    }
    vite = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
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
                "walletAddress": DEFAULT_BOOTSTRAP_SENDER,
                "smokeAmountIn": "100",
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
