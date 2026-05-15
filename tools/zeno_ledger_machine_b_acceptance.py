#!/usr/bin/env python3
"""Run the Machine B acceptance flow for a ZenoLedger public testnet."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping
from urllib.error import HTTPError
from urllib.parse import urljoin
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_make_testnet_bundle import DEFAULT_BOOTSTRAP_SENDER
from tools.zeno_ledger_node import (
    build_node_evidence_report_v0,
    doctor_public_node_v0,
    join_public_node_from_network_config_url_v0,
    poll_live_peers_once_v0,
)
from tools.zeno_ledger_verify_two_machine_evidence import verify_two_machine_evidence_report_v0


MACHINE_B_ACCEPTANCE_SCHEMA = "zenodex.zeno_ledger.machine_b_acceptance.v0"
MAX_RESPONSE_BYTES = 16 * 1024 * 1024


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _as_string_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{name} must be a list of strings")
    return list(value)


def _post_json(url: str, value: Mapping[str, Any]) -> tuple[dict[str, Any], int]:
    payload = json.dumps(dict(value), sort_keys=True).encode("utf-8")
    request = Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=30) as response:  # noqa: S310 - operator-supplied URL
            status = int(response.status)
            data = response.read(MAX_RESPONSE_BYTES + 1)
    except HTTPError as exc:
        status = int(exc.code)
        data = exc.read(MAX_RESPONSE_BYTES + 1)
    if len(data) > MAX_RESPONSE_BYTES:
        raise ValueError(f"remote response too large: {url}")
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must decode to a JSON object")
    return obj, status


def run_machine_b_acceptance_v0(
    *,
    config_url: str,
    expected_network_config_hash: str,
    node_id: str,
    bundle_root: Path,
    data_dir: Path,
    host: str,
    port: int | None,
    poll_seconds: int | None,
    token_symbol: str,
    token_name: str,
    token_salt: str,
    creator_pubkey: str,
    token_decimals: int,
    time_ms: int | None = None,
    writer_url: str | None = None,
) -> dict[str, Any]:
    """Run the physical Machine B acceptance sequence without starting a server."""

    observed_time_ms = int(time.time() * 1000) if time_ms is None else time_ms
    data_dir.mkdir(parents=True, exist_ok=True)

    doctor_report = doctor_public_node_v0(
        config_url=config_url,
        expected_network_config_hash=expected_network_config_hash,
    )
    join_report = join_public_node_from_network_config_url_v0(
        config_url=config_url,
        node_id=node_id,
        bundle_root=bundle_root,
        data_dir=data_dir,
        host=host,
        port=port,
        poll_seconds=poll_seconds,
        serve=False,
        expected_network_config_hash=expected_network_config_hash,
    )
    network_config = _load_json_object(data_dir / "public_network_config.json")
    writer_urls = _as_string_list(network_config.get("writer_urls"), name="writer_urls")
    peer_urls = _as_string_list(network_config.get("peer_urls"), name="peer_urls")
    selected_writer = writer_url or writer_urls[0]
    selected_peers = list(dict.fromkeys([selected_writer, *peer_urls]))

    token_payload = {
        "creator_pubkey": creator_pubkey,
        "decimals": token_decimals,
        "name": token_name,
        "salt": token_salt,
        "symbol": token_symbol,
        "time_ms": observed_time_ms,
        "tx_id": f"machine-b-acceptance-create-{token_symbol.lower()}-v0",
    }
    token_report, token_http_status = _post_json(
        urljoin(selected_writer.rstrip("/") + "/", "tokens"),
        token_payload,
    )
    follow_report = poll_live_peers_once_v0(
        data_dir=data_dir,
        peer_urls=selected_peers,
    )
    evidence_report = build_node_evidence_report_v0(
        data_dir=data_dir,
        peer_urls=[selected_writer],
    )
    evidence_report_path = data_dir / "evidence_report.json"
    _write_json(evidence_report_path, evidence_report)

    min_height = token_report.get("height")
    verification_report = verify_two_machine_evidence_report_v0(
        evidence_report=evidence_report,
        expected_created_token_symbols=[token_symbol],
        min_height=int(min_height) if isinstance(min_height, int) and not isinstance(min_height, bool) else None,
    )
    verification_report_path = data_dir / "two_machine_evidence_verification.json"
    _write_json(verification_report_path, verification_report)

    ok = all(
        item.get("ok") is True
        for item in (
            doctor_report,
            join_report,
            token_report,
            follow_report,
            evidence_report,
            verification_report,
        )
    )
    return {
        "schema": MACHINE_B_ACCEPTANCE_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "config_url": config_url,
        "expected_network_config_hash": expected_network_config_hash,
        "node_id": node_id,
        "bundle_root": str(bundle_root),
        "data_dir": str(data_dir),
        "writer_url": selected_writer,
        "peer_urls": selected_peers,
        "token_http_status": token_http_status,
        "token_symbol": token_symbol,
        "token_report": token_report,
        "doctor_report": doctor_report,
        "join_report": join_report,
        "follow_report": follow_report,
        "evidence_report_path": str(evidence_report_path),
        "verification_report_path": str(verification_report_path),
        "evidence_report_ok": evidence_report.get("ok") is True,
        "verification_report_ok": verification_report.get("ok") is True,
        "verification_report": verification_report,
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config-url", required=True)
    parser.add_argument("--expected-network-config-hash", required=True)
    parser.add_argument("--node-id", default="operator-b")
    parser.add_argument("--bundle-root", required=True, type=Path)
    parser.add_argument("--data-dir", required=True, type=Path)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int)
    parser.add_argument("--poll-seconds", type=int)
    parser.add_argument("--writer-url")
    parser.add_argument("--token-symbol", default="tMANGO")
    parser.add_argument("--token-name", default="Test Mango Credit")
    parser.add_argument("--token-salt", default="machine-b-acceptance-token-v0")
    parser.add_argument("--token-decimals", type=int, default=8)
    parser.add_argument("--creator-pubkey", default=DEFAULT_BOOTSTRAP_SENDER)
    parser.add_argument("--time-ms", type=int)
    parser.add_argument("--out", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        report = run_machine_b_acceptance_v0(
            config_url=args.config_url,
            expected_network_config_hash=args.expected_network_config_hash,
            node_id=args.node_id,
            bundle_root=args.bundle_root,
            data_dir=args.data_dir,
            host=args.host,
            port=args.port,
            poll_seconds=args.poll_seconds,
            writer_url=args.writer_url,
            token_symbol=args.token_symbol,
            token_name=args.token_name,
            token_salt=args.token_salt,
            creator_pubkey=args.creator_pubkey,
            token_decimals=args.token_decimals,
            time_ms=args.time_ms,
        )
        if args.out is not None:
            _write_json(args.out, report)
            report = {**report, "acceptance_report_path": str(args.out)}
    except Exception as exc:
        report = {
            "schema": MACHINE_B_ACCEPTANCE_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())

