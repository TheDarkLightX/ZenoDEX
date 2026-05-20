from __future__ import annotations

from dataclasses import dataclass
import json
import re
import os
import shutil
import socket
import subprocess
import threading
import time
from html import unescape
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import Request, urlopen
from urllib.error import HTTPError

import pytest

from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import make_node_http_server_v0, pull_live_from_peer_v0, run_node_once_v0


ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"
WRITER_TOKEN = "local-writer-token"
FORWARDER_TOKEN = "local-forwarder-token"
DOCKER_WRITER_TOKEN = "local-multidocker-token"


@dataclass(frozen=True)
class LiveNetwork:
    writer_url: str
    forwarder_url: str
    readonly_url: str
    writer_dir: Path
    forwarder_dir: Path
    readonly_dir: Path


def _read_url_json(url: str, *, timeout: float = 5) -> dict[str, object]:
    with urlopen(url, timeout=timeout) as response:  # noqa: S310 - local test server
        payload = response.read().decode("utf-8")
    obj = json.loads(payload)
    assert isinstance(obj, dict)
    return obj


def _post_url_json(
    url: str,
    value: dict[str, object],
    *,
    timeout: float = 5,
    bearer_token: str | None = None,
) -> dict[str, object]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if bearer_token is not None:
        headers["Authorization"] = f"Bearer {bearer_token}"
    request = Request(
        url,
        data=payload,
        headers=headers,
        method="POST",
    )
    with urlopen(request, timeout=timeout) as response:  # noqa: S310 - local test server
        body = response.read().decode("utf-8")
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return obj


def _post_url_json_status(
    url: str,
    value: dict[str, object],
    *,
    timeout: float = 5,
    bearer_token: str | None = None,
) -> tuple[int, dict[str, object]]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if bearer_token is not None:
        headers["Authorization"] = f"Bearer {bearer_token}"
    request = Request(url, data=payload, headers=headers, method="POST")
    try:
        with urlopen(request, timeout=timeout) as response:  # noqa: S310 - local test server
            body = response.read().decode("utf-8")
            status = int(response.status)
    except HTTPError as exc:
        body = exc.read().decode("utf-8")
        status = int(exc.code)
    obj = json.loads(body)
    assert isinstance(obj, dict)
    return status, obj


def _extract_pre_json(dom: str, test_id: str) -> dict[str, object]:
    match = re.search(
        rf'<pre[^>]*data-testid="{re.escape(test_id)}"[^>]*>(.*?)</pre>',
        dom,
        flags=re.DOTALL,
    )
    assert match is not None, f"missing pre[data-testid={test_id!r}]"
    obj = json.loads(unescape(match.group(1)))
    assert isinstance(obj, dict)
    return obj


def _smoke_row(smoke_status: dict[str, object], step: str) -> dict[str, object]:
    rows = smoke_status.get("results")
    assert isinstance(rows, list)
    for row in rows:
        assert isinstance(row, dict)
        if row.get("step") == step:
            return row
    raise AssertionError(f"missing smoke row: {step}")


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
def live_network(tmp_path_factory: pytest.TempPathFactory) -> LiveNetwork:
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

    peer_attestation = bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"

    writer_dir = tmp_path / "writer"
    forwarder_dir = tmp_path / "forwarder"
    readonly_dir = tmp_path / "readonly"
    for node_id, data_dir in (
        ("ui-live-bridge-writer", writer_dir),
        ("ui-live-bridge-forwarder", forwarder_dir),
        ("ui-live-bridge-readonly", readonly_dir),
    ):
        node_report = run_node_once_v0(
            bundle_root=bundle_root,
            node_id=node_id,
            data_dir=data_dir,
            peer_watcher_attestation_paths=[peer_attestation],
        )
        assert node_report["ok"] is True

    servers = []

    def start_server(data_dir: Path, **kwargs: object) -> str:
        server = make_node_http_server_v0(
            data_dir=data_dir,
            host="127.0.0.1",
            port=0,
            **kwargs,
        )
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        servers.append(server)
        host, port = server.server_address
        return f"http://{host}:{port}"

    writer_url = start_server(
        writer_dir,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        write_auth_token=WRITER_TOKEN,
    )
    forwarder_url = start_server(
        forwarder_dir,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        submit_peer_url=writer_url,
        write_auth_token=FORWARDER_TOKEN,
        submit_peer_auth_token=WRITER_TOKEN,
        peer_urls=[writer_url],
    )
    readonly_url = start_server(readonly_dir, peer_urls=[writer_url])
    try:
        yield LiveNetwork(
            writer_url=writer_url,
            forwarder_url=forwarder_url,
            readonly_url=readonly_url,
            writer_dir=writer_dir,
            forwarder_dir=forwarder_dir,
            readonly_dir=readonly_dir,
        )
    finally:
        for server in servers:
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
        },
        bearer_token=WRITER_TOKEN,
    )


def test_live_node_serves_ui_pools_and_accepts_ui_swap(live_network: LiveNetwork) -> None:
    node_base_url = live_network.writer_url
    faucet_report = _fund_smoke_sender(node_base_url, tx_id="ui-live-bridge-api-faucet-v0")
    assert faucet_report["ok"] is True

    pools = _read_url_json(f"{node_base_url}/api/pools")
    assert pools["ok"] is True
    pool_rows = pools["pools"]
    assert isinstance(pool_rows, list)
    assert len(pool_rows) >= 1
    first_pool = pool_rows[0]
    assert isinstance(first_pool, dict)
    assert first_pool["token0"] == "tASSET0"
    assert first_pool["token1"] == "tASSET1"
    assert first_pool["asset0"] == DEFAULT_ASSET0

    pre_height = _live_height(node_base_url)
    swap_report = _post_url_json(
        f"{node_base_url}/api/swap",
        {
            "from": "tASSET0",
            "to": "tASSET1",
            "poolId": first_pool["pool_id"],
            "amountIn": 100,
            "minAmountOut": 1,
            "senderPubkey": DEFAULT_BOOTSTRAP_SENDER,
            "recipient": DEFAULT_BOOTSTRAP_SENDER,
            "time_ms": 1_778_740_101_000,
        },
        bearer_token=WRITER_TOKEN,
    )
    assert swap_report["ok"] is True
    assert swap_report["height"] == pre_height + 1
    assert swap_report["tx_accepted"] is True
    receipt = swap_report["receipt"]
    assert isinstance(receipt, dict)
    assert receipt["accepted"] is True


def test_forwarder_uses_distinct_inbound_and_peer_auth(live_network: LiveNetwork) -> None:
    payload = {
        "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "asset": DEFAULT_ASSET0,
        "amount": 123,
        "time_ms": 1_778_740_102_000,
        "tx_id": "ui-live-bridge-forwarder-auth-faucet-v0",
    }

    wrong_status, wrong_report = _post_url_json_status(
        f"{live_network.forwarder_url}/faucet",
        payload,
        bearer_token=WRITER_TOKEN,
    )
    assert wrong_status == 401
    assert wrong_report["ok"] is False
    assert wrong_report["error"] == "unauthorized"

    pre_height = _live_height(live_network.writer_url)
    ok_status, ok_report = _post_url_json_status(
        f"{live_network.forwarder_url}/faucet",
        payload,
        bearer_token=FORWARDER_TOKEN,
    )
    assert ok_status == 200
    assert ok_report["ok"] is True
    assert ok_report["forwarded_to"] == live_network.writer_url
    assert ok_report["height"] == pre_height + 1
    assert _live_height(live_network.writer_url) == pre_height + 1


def test_dex_ui_smoke_runs_live_multinode_dex_flow_through_browser(
    live_network: LiveNetwork,
    tmp_path: Path,
) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    node_base_url = live_network.writer_url
    pre_height = _live_height(node_base_url)

    vite_port = _free_port()
    vite_base_url = f"http://127.0.0.1:{vite_port}"
    env = {
        **os.environ,
        "API_PROXY_TARGET": node_base_url,
        "LEDGER_WRITER_TARGET": live_network.writer_url,
        "LEDGER_FORWARDER_TARGET": live_network.forwarder_url,
        "LEDGER_READONLY_TARGET": live_network.readonly_url,
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
                "zenodexUiSmokeScript": "full",
                "walletAddress": DEFAULT_BOOTSTRAP_SENDER,
                "smokeAmountIn": "100",
                "zenodexUiSmokeWriterToken": WRITER_TOKEN,
                "zenodexUiSmokeForwarderToken": FORWARDER_TOKEN,
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
                "--virtual-time-budget=25000",
                "--dump-dom",
                f"{vite_base_url}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=55,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        height = _wait_for_live_height(node_base_url, min_height=pre_height + 5, timeout_s=30)
        assert height == pre_height + 5

        reports = [
            json.loads((live_network.writer_dir / "append_reports" / f"{report_height}.json").read_text(encoding="utf-8"))
            for report_height in range(pre_height + 1, height + 1)
        ]
        assert len(reports) >= 5
        assert reports[0]["append_kind"] == "testnet_faucet"
        assert all(report["ok"] is True for report in reports)
        dex_reports = [report for report in reports if report.get("receipt") is not None]
        assert len(dex_reports) >= 4
        assert all(report["receipt"]["accepted"] is True for report in dex_reports)

        pull_report = pull_live_from_peer_v0(data_dir=live_network.readonly_dir, peer_url=live_network.writer_url)
        assert pull_report["ok"] is True
        assert pull_report["pulled_count"] >= 5
        assert _live_height(live_network.readonly_url) == height

        smoke_status = _extract_pre_json(result.stdout, "smoke-status")
        assert smoke_status["done"] is True
        assert smoke_status["ok"] is True
        assert _smoke_row(smoke_status, "writer_faucet_asset0")["accepted"] is True
        assert _smoke_row(smoke_status, "writer_swap")["accepted"] is True
        assert _smoke_row(smoke_status, "writer_add_liquidity")["accepted"] is True
        assert _smoke_row(smoke_status, "writer_remove_liquidity")["accepted"] is True
        assert _smoke_row(smoke_status, "forwarder_swap")["accepted"] is True
        readonly_row = _smoke_row(smoke_status, "readonly_swap")
        assert readonly_row["status"] == 403
        assert readonly_row["accepted"] is False
        assert readonly_row["error"] == "testnet_intake_disabled"
    finally:
        vite.terminate()
        try:
            vite.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite.kill()
            vite.wait(timeout=5)


@pytest.mark.skipif(
    os.environ.get("ZENO_DEX_DOCKER_LIVE_TEST") != "1",
    reason="set ZENO_DEX_DOCKER_LIVE_TEST=1 with published Docker ledger nodes",
)
def test_dex_ui_smoke_runs_against_published_docker_nodes(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the Docker browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the Docker browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    writer_url = os.environ.get("ZENO_DEX_DOCKER_WRITER_URL", "http://127.0.0.1:8787")
    forwarder_url = os.environ.get("ZENO_DEX_DOCKER_FORWARDER_URL", "http://127.0.0.1:8788")
    readonly_url = os.environ.get("ZENO_DEX_DOCKER_READONLY_URL", "http://127.0.0.1:8789")
    _wait_for_http(f"{writer_url}/status", timeout_s=120)
    _wait_for_http(f"{forwarder_url}/status", timeout_s=120)
    _wait_for_http(f"{readonly_url}/status", timeout_s=120)
    pre_height = _live_height(writer_url)

    vite_port = _free_port()
    vite_base_url = f"http://127.0.0.1:{vite_port}"
    env = {
        **os.environ,
        "API_PROXY_TARGET": writer_url,
        "LEDGER_WRITER_TARGET": writer_url,
        "LEDGER_FORWARDER_TARGET": forwarder_url,
        "LEDGER_READONLY_TARGET": readonly_url,
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
                "zenodexUiSmokeScript": "full",
                "walletAddress": DEFAULT_BOOTSTRAP_SENDER,
                "smokeAmountIn": "100",
                "zenodexUiSmokeWriterToken": DOCKER_WRITER_TOKEN,
                "zenodexUiSmokeForwarderToken": DOCKER_WRITER_TOKEN,
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
                "--virtual-time-budget=25000",
                "--dump-dom",
                f"{vite_base_url}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=55,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        writer_height = _wait_for_live_height(writer_url, min_height=pre_height + 5, timeout_s=30)
        assert writer_height == pre_height + 5
        _wait_for_live_height(forwarder_url, min_height=writer_height, timeout_s=30)
        _wait_for_live_height(readonly_url, min_height=writer_height, timeout_s=30)

        smoke_status = _extract_pre_json(result.stdout, "smoke-status")
        assert smoke_status["done"] is True
        assert smoke_status["ok"] is True
        assert _smoke_row(smoke_status, "writer_faucet_asset0")["accepted"] is True
        assert _smoke_row(smoke_status, "writer_swap")["accepted"] is True
        assert _smoke_row(smoke_status, "writer_add_liquidity")["accepted"] is True
        assert _smoke_row(smoke_status, "writer_remove_liquidity")["accepted"] is True
        assert _smoke_row(smoke_status, "forwarder_swap")["accepted"] is True
        readonly_row = _smoke_row(smoke_status, "readonly_swap")
        assert readonly_row["status"] == 403
        assert readonly_row["accepted"] is False
        assert readonly_row["error"] == "testnet_intake_disabled"
    finally:
        vite.terminate()
        try:
            vite.wait(timeout=5)
        except subprocess.TimeoutExpired:
            vite.kill()
            vite.wait(timeout=5)
