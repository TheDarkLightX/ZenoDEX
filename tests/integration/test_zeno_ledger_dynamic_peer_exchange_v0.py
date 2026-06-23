from __future__ import annotations

import json
import shutil
import threading
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.integration.zeno_ledger_dynamic_peers_v0 import (
    build_dynamic_peer_admission_v0,
    build_dynamic_peer_candidate_v0,
    validate_dynamic_peer_admission_v0,
)
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_node import make_node_http_server_v0, run_node_once_v0


def _get_json(url: str) -> dict[str, object]:
    with urlopen(url, timeout=5) as response:  # noqa: S310 - local test server
        payload = response.read().decode("utf-8")
    obj = json.loads(payload)
    assert isinstance(obj, dict)
    return obj


def _post_json(url: str, value: dict[str, object]) -> dict[str, object]:
    request = Request(
        url,
        data=json.dumps(value, sort_keys=True).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=5) as response:  # noqa: S310 - local test server
            payload = response.read().decode("utf-8")
    except HTTPError as exc:
        payload = exc.read().decode("utf-8")
    obj = json.loads(payload)
    assert isinstance(obj, dict)
    return obj


@pytest.fixture(scope="module")
def bundle_root(tmp_path_factory: pytest.TempPathFactory) -> Path:
    root = tmp_path_factory.mktemp("dynamic_peer_bundle") / "bundle"
    report = build_public_testnet_bundle_v0(
        out_dir=root,
        network_id="zeno-ledger-dynamic-peer-testnet-0",
        chain_id="zeno-ledger-dynamic-peer-testnet-0",
        sequencer_id="sequencer-dynamic-peer-testnet-0",
        time_ms=1_778_730_523_000,
        token_symbol="tZENO",
    )
    assert report["ok"] is True
    return root


@pytest.fixture(scope="module")
def baseline_nodes(tmp_path_factory: pytest.TempPathFactory, bundle_root: Path) -> tuple[Path, Path, Path]:
    root = tmp_path_factory.mktemp("dynamic_peer_nodes")
    node_b = root / "node-b-base"
    node_c = root / "node-c-base"
    assert run_node_once_v0(bundle_root=bundle_root, node_id="node-b", data_dir=node_b)["ok"] is True
    assert run_node_once_v0(bundle_root=bundle_root, node_id="node-c", data_dir=node_c)["ok"] is True
    return bundle_root, node_b, node_c


def _node_pair(tmp_path: Path, baseline_nodes: tuple[Path, Path, Path]) -> tuple[Path, Path, Path]:
    bundle_root, node_b_base, node_c_base = baseline_nodes
    node_b = tmp_path / "node-b"
    node_c = tmp_path / "node-c"
    shutil.copytree(node_b_base, node_b)
    shutil.copytree(node_c_base, node_c)
    return bundle_root, node_b, node_c


def test_dynamic_peer_admission_is_hash_bound() -> None:
    candidate = build_dynamic_peer_candidate_v0(
        network_id="zeno-ledger-dynamic-peer-testnet-0",
        chain_id="zeno-ledger-dynamic-peer-testnet-0",
        source_node_id="node-a",
        source_peer_url="http://127.0.0.1:8800",
        candidate_peer_urls=["http://127.0.0.1:8801"],
        observed_at_height=5,
    )
    peer_check = {
        "schema": "zenodex.zeno_ledger.node_peer_check_report.v0",
        "ok": True,
        "status": "accepted",
        "node_id": "node-a",
        "network_id": "zeno-ledger-dynamic-peer-testnet-0",
        "chain_id": "zeno-ledger-dynamic-peer-testnet-0",
        "feature_suite_hash": "0x" + "11" * 32,
        "local_tip": {"height": 5, "header_hash": "0x" + "22" * 32},
        "peer_count": 1,
        "peers": [{"peer_url": "http://127.0.0.1:8801", "ok": True, "status": "accepted"}],
    }
    admission = build_dynamic_peer_admission_v0(
        current_peer_urls=["http://127.0.0.1:8800"],
        candidate=candidate,
        peer_check_report=peer_check,
        max_peer_count=4,
    )

    validate_dynamic_peer_admission_v0(
        admission=admission,
        current_peer_urls=["http://127.0.0.1:8800"],
        candidate=candidate,
        peer_check_report=peer_check,
        max_peer_count=4,
    )
    tampered = dict(admission)
    tampered["admitted_peer_count"] = 99
    with pytest.raises(ValueError, match="binding mismatch"):
        validate_dynamic_peer_admission_v0(
            admission=tampered,
            current_peer_urls=["http://127.0.0.1:8800"],
            candidate=candidate,
            peer_check_report=peer_check,
            max_peer_count=4,
        )


def test_dynamic_peer_http_route_is_opt_in_and_updates_peer_set(
    tmp_path: Path,
    baseline_nodes: tuple[Path, Path, Path],
) -> None:
    _, node_b, node_c = _node_pair(tmp_path, baseline_nodes)
    candidate_server = make_node_http_server_v0(data_dir=node_c, host="127.0.0.1", port=0)
    candidate_thread = threading.Thread(target=candidate_server.serve_forever, daemon=True)
    candidate_thread.start()
    try:
        candidate_host, candidate_port = candidate_server.server_address
        candidate_url = f"http://{candidate_host}:{candidate_port}"

        disabled = make_node_http_server_v0(data_dir=node_b, host="127.0.0.1", port=0)
        disabled_thread = threading.Thread(target=disabled.serve_forever, daemon=True)
        disabled_thread.start()
        try:
            host, port = disabled.server_address
            rejected = _post_json(
                f"http://{host}:{port}/peers/announce",
                {"peer_url": candidate_url, "source_node_id": "node-c", "source_peer_url": candidate_url},
            )
        finally:
            disabled.shutdown()
            disabled.server_close()
        assert rejected["error"] == "dynamic_peer_exchange_disabled"

        enabled = make_node_http_server_v0(
            data_dir=node_b,
            host="127.0.0.1",
            port=0,
            enable_dynamic_peer_exchange=True,
            max_dynamic_peer_count=4,
        )
        enabled_thread = threading.Thread(target=enabled.serve_forever, daemon=True)
        enabled_thread.start()
        try:
            host, port = enabled.server_address
            accepted = _post_json(
                f"http://{host}:{port}/peers/announce",
                {"peer_url": candidate_url, "source_node_id": "node-c", "source_peer_url": candidate_url},
            )
            peers = _get_json(f"http://{host}:{port}/peers")
            network = _get_json(f"http://{host}:{port}/network")
        finally:
            enabled.shutdown()
            enabled.server_close()
    finally:
        candidate_server.shutdown()
        candidate_server.server_close()

    assert accepted["ok"] is True
    assert accepted["admission"]["admitted_peer_urls"] == [candidate_url]
    assert candidate_url in peers["peer_urls"]
    assert candidate_url in network["peer_urls"]
