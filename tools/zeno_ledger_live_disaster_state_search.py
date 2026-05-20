#!/usr/bin/env python3
"""Bounded stateful disaster-state search for live ZenoLedger nodes."""

from __future__ import annotations

import argparse
import json
import socket
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from http import HTTPStatus
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.parse import urljoin
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.state.pools import compute_pool_id
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_ASSET1, DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import make_node_http_server_v0, pull_live_from_peer_v0, run_node_once_v0


SCHEMA = "zenodex/zeno_ledger_live_disaster_state_search/v0"
WRITER_TOKEN = "live-disaster-writer-token"
FORWARDER_TOKEN = "live-disaster-forwarder-token"


@dataclass(frozen=True)
class LiveNetwork:
    writer_url: str
    forwarder_url: str
    readonly_url: str
    writer_dir: Path
    forwarder_dir: Path
    readonly_dir: Path


@dataclass(frozen=True)
class ActionSpec:
    name: str
    node: str
    path: str
    body: dict[str, Any]
    token: str | None
    expected_status: int
    expected_accepted: bool | None
    expected_writer_delta: int | None
    expected_readonly_delta: int | None
    disaster_ids: tuple[str, ...]


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _read_json(url: str, *, timeout: float = 5.0) -> dict[str, Any]:
    with urlopen(url, timeout=timeout) as response:  # noqa: S310 - local test server
        obj = json.loads(response.read().decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} returned non-object JSON")
    return obj


def _post_json_status(
    url: str,
    value: dict[str, Any],
    *,
    token: str | None,
    timeout: float = 5.0,
) -> tuple[int, dict[str, Any]]:
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    request = Request(url, data=payload, headers=headers, method="POST")
    try:
        with urlopen(request, timeout=timeout) as response:  # noqa: S310 - local test server
            body = response.read().decode("utf-8")
            status = int(response.status)
    except HTTPError as exc:
        body = exc.read().decode("utf-8")
        status = int(exc.code)
    obj = json.loads(body)
    if not isinstance(obj, dict):
        raise ValueError(f"{url} returned non-object JSON")
    return status, obj


def _height(node_url: str) -> int:
    live = _read_json(urljoin(node_url.rstrip("/") + "/", "live"))
    if live.get("live") is True:
        state = live.get("state")
        if not isinstance(state, dict):
            raise ValueError("live state must be an object")
        return int(state["latest_height"])
    status = _read_json(urljoin(node_url.rstrip("/") + "/", "status"))
    return int(status["latest_height"])


def _tip_hash(node_url: str) -> str:
    network = _read_json(urljoin(node_url.rstrip("/") + "/", "network"))
    tip = network.get("local_tip")
    if not isinstance(tip, dict):
        raise ValueError("network.local_tip must be an object")
    return str(tip["header_hash"])


def _wait_for_http(url: str, *, timeout_s: float = 30.0) -> None:
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
    raise TimeoutError(f"server did not become ready at {url}: {last_error}")


def _start_server(data_dir: Path, **kwargs: Any) -> tuple[Any, str]:
    server = make_node_http_server_v0(data_dir=data_dir, host="127.0.0.1", port=_free_port(), **kwargs)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    host, port = server.server_address
    url = f"http://{host}:{port}"
    _wait_for_http(f"{url}/status")
    return server, url


def _build_live_network(root: Path) -> tuple[LiveNetwork, list[Any]]:
    bundle_root = root / "bundle"
    build_report = build_public_testnet_bundle_v0(
        out_dir=bundle_root,
        network_id="zenodex-live-disaster-search-testnet",
        chain_id="zenodex-live-disaster-search-testnet",
        sequencer_id="sequencer-live-disaster-search",
        time_ms=1_778_740_000_000,
        token_symbol="tZENO",
    )
    if build_report.get("ok") is not True:
        raise RuntimeError(f"bundle build failed: {build_report}")

    peer_attestation = bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    writer_dir = root / "writer"
    forwarder_dir = root / "forwarder"
    readonly_dir = root / "readonly"
    for node_id, data_dir in (
        ("live-disaster-writer", writer_dir),
        ("live-disaster-forwarder", forwarder_dir),
        ("live-disaster-readonly", readonly_dir),
    ):
        node_report = run_node_once_v0(
            bundle_root=bundle_root,
            node_id=node_id,
            data_dir=data_dir,
            peer_watcher_attestation_paths=[peer_attestation],
        )
        if node_report.get("ok") is not True:
            raise RuntimeError(f"node init failed: {node_report}")

    servers: list[Any] = []
    writer_server, writer_url = _start_server(
        writer_dir,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        write_auth_token=WRITER_TOKEN,
    )
    servers.append(writer_server)
    forwarder_server, forwarder_url = _start_server(
        forwarder_dir,
        enable_testnet_intake=True,
        enable_testnet_faucet=True,
        submit_peer_url=writer_url,
        write_auth_token=FORWARDER_TOKEN,
        submit_peer_auth_token=WRITER_TOKEN,
        peer_urls=[writer_url],
    )
    servers.append(forwarder_server)
    readonly_server, readonly_url = _start_server(readonly_dir, peer_urls=[writer_url])
    servers.append(readonly_server)
    return (
        LiveNetwork(
            writer_url=writer_url,
            forwarder_url=forwarder_url,
            readonly_url=readonly_url,
            writer_dir=writer_dir,
            forwarder_dir=forwarder_dir,
            readonly_dir=readonly_dir,
        ),
        servers,
    )


def _swap_tx(*, tx_id: str, nonce: int, intent_byte: str, amount_in: int = 100) -> dict[str, Any]:
    return {
        "tx_id": tx_id,
        "block_timestamp": 1_778_740_100,
        "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "0x" + intent_byte * 32,
                    "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                    "deadline": 1_999_999_999,
                    "nonce": nonce,
                    "pool_id": compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30),
                    "asset_in": DEFAULT_ASSET0,
                    "asset_out": DEFAULT_ASSET1,
                    "amount_in": amount_in,
                    "min_amount_out": 1,
                    "recipient": DEFAULT_BOOTSTRAP_SENDER,
                }
            ]
        },
    }


def _liquidity_tx(*, kind: str, tx_id: str, nonce: int, intent_byte: str) -> dict[str, Any]:
    operation: dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": kind,
        "intent_id": "0x" + intent_byte * 32,
        "sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "deadline": 1_999_999_999,
        "nonce": nonce,
        "pool_id": compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30),
        "amount0_min": 0,
        "amount1_min": 0,
    }
    if kind == "ADD_LIQUIDITY":
        operation.update({"amount0_desired": 100, "amount1_desired": 200})
    else:
        operation.update({"lp_amount": 10})
    return {
        "tx_id": tx_id,
        "block_timestamp": 1_778_740_100,
        "tx_sender_pubkey": DEFAULT_BOOTSTRAP_SENDER,
        "operations": {"2": [operation]},
    }


def _actions() -> list[ActionSpec]:
    return [
        ActionSpec(
            name="writer_valid_faucet",
            node="writer",
            path="/faucet",
            token=WRITER_TOKEN,
            body={
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": DEFAULT_ASSET0,
                "amount": 10_000,
                "time_ms": 1_778_740_100_000,
                "tx_id": "live-disaster-valid-faucet",
            },
            expected_status=HTTPStatus.OK,
            expected_accepted=True,
            expected_writer_delta=1,
            expected_readonly_delta=0,
            disaster_ids=(),
        ),
        ActionSpec(
            name="writer_valid_swap_nonce_5",
            node="writer",
            path="/tx",
            token=WRITER_TOKEN,
            body={"time_ms": 1_778_740_101_000, "tx": _swap_tx(tx_id="live-disaster-swap-1", nonce=5, intent_byte="a1")},
            expected_status=HTTPStatus.OK,
            expected_accepted=True,
            expected_writer_delta=1,
            expected_readonly_delta=0,
            disaster_ids=(),
        ),
        ActionSpec(
            name="writer_duplicate_nonce_swap",
            node="writer",
            path="/tx",
            token=WRITER_TOKEN,
            body={
                "time_ms": 1_778_740_102_000,
                "tx": _swap_tx(tx_id="live-disaster-swap-duplicate-nonce", nonce=5, intent_byte="a2", amount_in=1),
            },
            expected_status=HTTPStatus.OK,
            expected_accepted=False,
            expected_writer_delta=1,
            expected_readonly_delta=0,
            disaster_ids=("duplicate_nonce_state_changed",),
        ),
        ActionSpec(
            name="writer_valid_add_liquidity",
            node="writer",
            path="/tx",
            token=WRITER_TOKEN,
            body={
                "time_ms": 1_778_740_103_000,
                "tx": _liquidity_tx(kind="ADD_LIQUIDITY", tx_id="live-disaster-add-liquidity", nonce=6, intent_byte="a3"),
            },
            expected_status=HTTPStatus.OK,
            expected_accepted=True,
            expected_writer_delta=1,
            expected_readonly_delta=0,
            disaster_ids=(),
        ),
        ActionSpec(
            name="writer_valid_remove_liquidity",
            node="writer",
            path="/tx",
            token=WRITER_TOKEN,
            body={
                "time_ms": 1_778_740_104_000,
                "tx": _liquidity_tx(
                    kind="REMOVE_LIQUIDITY",
                    tx_id="live-disaster-remove-liquidity",
                    nonce=7,
                    intent_byte="a4",
                ),
            },
            expected_status=HTTPStatus.OK,
            expected_accepted=True,
            expected_writer_delta=1,
            expected_readonly_delta=0,
            disaster_ids=(),
        ),
        ActionSpec(
            name="forwarder_wrong_inbound_token",
            node="forwarder",
            path="/faucet",
            token=WRITER_TOKEN,
            body={
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": DEFAULT_ASSET0,
                "amount": 1,
                "time_ms": 1_778_740_105_000,
                "tx_id": "live-disaster-forwarder-wrong-token",
            },
            expected_status=HTTPStatus.UNAUTHORIZED,
            expected_accepted=False,
            expected_writer_delta=0,
            expected_readonly_delta=0,
            disaster_ids=("forwarder_wrong_token_forwarded", "unauthorized_write_accepted"),
        ),
        ActionSpec(
            name="forwarder_valid_swap_nonce_8",
            node="forwarder",
            path="/tx",
            token=FORWARDER_TOKEN,
            body={"time_ms": 1_778_740_106_000, "tx": _swap_tx(tx_id="live-disaster-forwarder-swap", nonce=8, intent_byte="a5")},
            expected_status=HTTPStatus.OK,
            expected_accepted=True,
            expected_writer_delta=1,
            expected_readonly_delta=0,
            disaster_ids=(),
        ),
        ActionSpec(
            name="readonly_rejects_tx",
            node="readonly",
            path="/tx",
            token=None,
            body={"time_ms": 1_778_740_107_000, "tx": _swap_tx(tx_id="live-disaster-readonly-swap", nonce=9, intent_byte="a6")},
            expected_status=HTTPStatus.FORBIDDEN,
            expected_accepted=False,
            expected_writer_delta=0,
            expected_readonly_delta=0,
            disaster_ids=("readonly_node_mutated",),
        ),
        ActionSpec(
            name="writer_unauthorized_faucet",
            node="writer",
            path="/faucet",
            token=None,
            body={
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": DEFAULT_ASSET0,
                "amount": 1,
                "time_ms": 1_778_740_108_000,
                "tx_id": "live-disaster-writer-unauthorized",
            },
            expected_status=HTTPStatus.UNAUTHORIZED,
            expected_accepted=False,
            expected_writer_delta=0,
            expected_readonly_delta=0,
            disaster_ids=("unauthorized_write_accepted",),
        ),
        ActionSpec(
            name="writer_oversized_faucet",
            node="writer",
            path="/faucet",
            token=WRITER_TOKEN,
            body={
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": DEFAULT_ASSET0,
                "amount": 10**18,
                "time_ms": 1_778_740_109_000,
                "tx_id": "live-disaster-oversized-faucet",
            },
            expected_status=HTTPStatus.BAD_REQUEST,
            expected_accepted=False,
            expected_writer_delta=0,
            expected_readonly_delta=0,
            disaster_ids=("oversized_faucet_accepted",),
        ),
        ActionSpec(
            name="writer_malformed_tx",
            node="writer",
            path="/tx",
            token=WRITER_TOKEN,
            body={"time_ms": 1_778_740_110_000, "tx": "bad"},
            expected_status=HTTPStatus.BAD_REQUEST,
            expected_accepted=False,
            expected_writer_delta=0,
            expected_readonly_delta=0,
            disaster_ids=("malformed_tx_accepted",),
        ),
    ]


def _node_url(network: LiveNetwork, node: str) -> str:
    if node == "writer":
        return network.writer_url
    if node == "forwarder":
        return network.forwarder_url
    if node == "readonly":
        return network.readonly_url
    raise ValueError(f"unknown node: {node}")


def _accepted(response: dict[str, Any]) -> bool:
    receipt = response.get("receipt")
    return bool(response.get("tx_accepted") is True or (isinstance(receipt, dict) and receipt.get("accepted") is True))


def _state_changed(response: dict[str, Any]) -> bool:
    receipt = response.get("receipt")
    return bool(isinstance(receipt, dict) and receipt.get("state_changed") is True)


def _check_action(network: LiveNetwork, action: ActionSpec) -> dict[str, Any]:
    writer_before = _height(network.writer_url)
    readonly_before = _height(network.readonly_url)
    status, response = _post_json_status(
        urljoin(_node_url(network, action.node).rstrip("/") + "/", action.path.lstrip("/")),
        action.body,
        token=action.token,
        timeout=10.0,
    )
    writer_after = _height(network.writer_url)
    readonly_after = _height(network.readonly_url)
    accepted = _accepted(response)
    state_changed = _state_changed(response)
    issues: list[str] = []
    reached_disasters: list[str] = []

    if status != int(action.expected_status):
        issues.append(f"status {status} != expected {int(action.expected_status)}")
    if action.expected_accepted is not None and accepted != action.expected_accepted:
        issues.append(f"accepted {accepted} != expected {action.expected_accepted}")
    if action.expected_writer_delta is not None and writer_after - writer_before != action.expected_writer_delta:
        issues.append(
            f"writer delta {writer_after - writer_before} != expected {action.expected_writer_delta}"
        )
    if action.expected_readonly_delta is not None and readonly_after - readonly_before != action.expected_readonly_delta:
        issues.append(
            f"readonly delta {readonly_after - readonly_before} != expected {action.expected_readonly_delta}"
        )

    if "duplicate_nonce_state_changed" in action.disaster_ids and (accepted or state_changed):
        reached_disasters.append("duplicate_nonce_state_changed")
    if "forwarder_wrong_token_forwarded" in action.disaster_ids and (
        response.get("forwarded_to") is not None or writer_after != writer_before
    ):
        reached_disasters.append("forwarder_wrong_token_forwarded")
    if "unauthorized_write_accepted" in action.disaster_ids and (accepted or writer_after != writer_before):
        reached_disasters.append("unauthorized_write_accepted")
    if "readonly_node_mutated" in action.disaster_ids and (
        accepted or writer_after != writer_before or readonly_after != readonly_before
    ):
        reached_disasters.append("readonly_node_mutated")
    if "oversized_faucet_accepted" in action.disaster_ids and (accepted or writer_after != writer_before):
        reached_disasters.append("oversized_faucet_accepted")
    if "malformed_tx_accepted" in action.disaster_ids and (accepted or writer_after != writer_before):
        reached_disasters.append("malformed_tx_accepted")

    return {
        "name": action.name,
        "node": action.node,
        "path": action.path,
        "status": status,
        "accepted": accepted,
        "state_changed": state_changed,
        "writer_height_before": writer_before,
        "writer_height_after": writer_after,
        "readonly_height_before": readonly_before,
        "readonly_height_after": readonly_after,
        "expected_status": int(action.expected_status),
        "expected_accepted": action.expected_accepted,
        "expected_writer_delta": action.expected_writer_delta,
        "expected_readonly_delta": action.expected_readonly_delta,
        "issues": issues,
        "reached_disasters": reached_disasters,
        "response_error": response.get("error")
        or (response.get("receipt") if isinstance(response.get("receipt"), dict) else {}).get("error_code"),
    }


def run_live_disaster_state_search(*, budget: int | None = None) -> dict[str, Any]:
    started = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="zeno-ledger-live-disaster-") as tmp:
        network, servers = _build_live_network(Path(tmp))
        try:
            selected_actions = _actions()[:budget] if budget is not None else _actions()
            action_reports = [_check_action(network, action) for action in selected_actions]
            pull_report = pull_live_from_peer_v0(data_dir=network.readonly_dir, peer_url=network.writer_url)
            writer_height = _height(network.writer_url)
            readonly_height = _height(network.readonly_url)
            writer_tip = _tip_hash(network.writer_url)
            readonly_tip = _tip_hash(network.readonly_url)
            replay_issue = None
            if writer_height != readonly_height or writer_tip != readonly_tip:
                replay_issue = "readonly_replay_diverged"
        finally:
            for server in servers:
                server.shutdown()
                server.server_close()

    reached = sorted(
        {
            disaster
            for report in action_reports
            for disaster in report["reached_disasters"]
        }
    )
    issue_count = sum(len(report["issues"]) for report in action_reports)
    if replay_issue is not None:
        reached.append(replay_issue)
        issue_count += 1

    disaster_states = [
        "duplicate_nonce_state_changed",
        "forwarder_wrong_token_forwarded",
        "unauthorized_write_accepted",
        "readonly_node_mutated",
        "oversized_faucet_accepted",
        "malformed_tx_accepted",
        "readonly_replay_diverged",
    ]
    return {
        "schema": SCHEMA,
        "ok": issue_count == 0 and not reached,
        "status": "accepted" if issue_count == 0 and not reached else "rejected",
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
        "action_count": len(action_reports),
        "selected_disaster_state_count": len(disaster_states),
        "disaster_states": [
            {
                "id": disaster,
                "reached": disaster in reached,
                "status": "reached" if disaster in reached else "unreachable_under_bounds",
            }
            for disaster in disaster_states
        ],
        "reached_disasters": reached,
        "issue_count": issue_count,
        "actions": action_reports,
        "replay": {
            "pull_ok": pull_report.get("ok") is True,
            "pulled_count": pull_report.get("pulled_count"),
            "writer_height": writer_height,
            "readonly_height": readonly_height,
            "writer_tip": writer_tip,
            "readonly_tip": readonly_tip,
        },
        "bounds": {
            "budget": budget,
            "max_action_count": len(_actions()),
            "deterministic_seed": "zeno-ledger-live-disaster-state-search-v0",
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--budget", type=int, default=None)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--format", choices=("json", "text"), default="text")
    args = parser.parse_args(argv)

    report = run_live_disaster_state_search(budget=args.budget)
    if args.output_json is not None:
        _write_json(args.output_json, report)
    if args.format == "json":
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("ZenoLedger live disaster-state search")
        print(f"ok: {'yes' if report['ok'] else 'no'}")
        print(f"actions: {report['action_count']}")
        print(f"selected_disaster_states: {report['selected_disaster_state_count']}")
        print(f"reached_disasters: {', '.join(report['reached_disasters']) or 'none'}")
        print(f"issue_count: {report['issue_count']}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
