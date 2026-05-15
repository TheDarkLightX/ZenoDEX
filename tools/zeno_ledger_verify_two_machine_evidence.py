#!/usr/bin/env python3
"""Verify the Machine B evidence report for a ZenoLedger two-machine run."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_node import NODE_EVIDENCE_REPORT_SCHEMA


VERIFY_TWO_MACHINE_EVIDENCE_SCHEMA = "zenodex.zeno_ledger.two_machine_evidence_verification.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _check(name: str, ok: bool, **fields: Any) -> dict[str, Any]:
    return {"name": name, "ok": ok, **fields}


def _as_mapping(value: object) -> Mapping[str, Any] | None:
    return value if isinstance(value, Mapping) else None


def _as_list(value: object) -> list[Any]:
    return list(value) if isinstance(value, list) else []


def verify_two_machine_evidence_report_v0(
    *,
    evidence_report: Mapping[str, Any],
    expected_created_token_symbols: list[str] | None = None,
    min_height: int | None = None,
) -> dict[str, Any]:
    """Verify that a Machine B evidence report satisfies the public-node gate."""

    expected_symbols = list(expected_created_token_symbols or [])
    checks: list[dict[str, Any]] = []
    schema_ok = evidence_report.get("schema") == NODE_EVIDENCE_REPORT_SCHEMA
    checks.append(
        _check(
            "schema",
            schema_ok,
            actual=evidence_report.get("schema"),
            expected=NODE_EVIDENCE_REPORT_SCHEMA,
        )
    )
    checks.append(_check("evidence_report_ok", evidence_report.get("ok") is True))

    required_features = _as_list(evidence_report.get("required_features"))
    covered_feature_count = evidence_report.get("covered_feature_count")
    feature_coverage_ok = (
        isinstance(covered_feature_count, int)
        and not isinstance(covered_feature_count, bool)
        and covered_feature_count == len(required_features)
        and covered_feature_count > 0
    )
    checks.append(
        _check(
            "feature_coverage",
            feature_coverage_ok,
            covered_feature_count=covered_feature_count,
            required_feature_count=len(required_features),
        )
    )

    local_tip = _as_mapping(evidence_report.get("local_tip"))
    local_height = local_tip.get("height") if local_tip is not None else None
    local_header_hash = local_tip.get("header_hash") if local_tip is not None else None
    local_tip_ok = (
        isinstance(local_height, int)
        and not isinstance(local_height, bool)
        and local_height >= 0
        and isinstance(local_header_hash, str)
        and local_header_hash.startswith("0x")
    )
    if min_height is not None:
        local_tip_ok = bool(local_tip_ok and isinstance(local_height, int) and local_height >= min_height)
    checks.append(
        _check(
            "local_tip",
            local_tip_ok,
            height=local_height,
            header_hash=local_header_hash,
            min_height=min_height,
        )
    )

    peer_check = _as_mapping(evidence_report.get("peer_check"))
    peer_check_ok = peer_check is not None and peer_check.get("ok") is True
    checks.append(_check("peer_check_ok", peer_check_ok))

    same_height_peer: Mapping[str, Any] | None = None
    peers = _as_list(peer_check.get("peers") if peer_check is not None else None)
    for peer in peers:
        peer_obj = _as_mapping(peer)
        if peer_obj is None:
            continue
        if (
            peer_obj.get("ok") is True
            and peer_obj.get("height_relation") == "same_height"
            and peer_obj.get("common_header_match") is True
        ):
            same_height_peer = peer_obj
            break
    peer_same_height_ok = same_height_peer is not None
    checks.append(_check("peer_same_height", peer_same_height_ok, peer_count=len(peers)))

    common_hash = same_height_peer.get("common_header_hash") if same_height_peer is not None else None
    common_height = same_height_peer.get("common_height") if same_height_peer is not None else None
    peer_tip = _as_mapping(same_height_peer.get("peer_tip")) if same_height_peer is not None else None
    peer_tip_hash = peer_tip.get("header_hash") if peer_tip is not None else None
    root_match_ok = (
        peer_same_height_ok
        and common_hash == local_header_hash
        and common_height == local_height
        and peer_tip_hash == local_header_hash
    )
    checks.append(
        _check(
            "common_header_binding",
            root_match_ok,
            local_height=local_height,
            common_height=common_height,
            local_header_hash=local_header_hash,
            common_header_hash=common_hash,
            peer_tip_header_hash=peer_tip_hash,
        )
    )

    created_tokens = _as_list(evidence_report.get("created_test_tokens"))
    created_count = evidence_report.get("created_test_token_count")
    token_count_ok = isinstance(created_count, int) and not isinstance(created_count, bool) and created_count == len(created_tokens)
    created_symbols = [str(token.get("symbol")) for token in created_tokens if isinstance(token, Mapping)]
    expected_symbols_ok = all(symbol in created_symbols for symbol in expected_symbols)
    checks.append(
        _check(
            "created_test_tokens",
            bool(token_count_ok and expected_symbols_ok),
            created_test_token_count=created_count,
            created_symbols=created_symbols,
            expected_created_token_symbols=expected_symbols,
        )
    )

    ok = all(check["ok"] is True for check in checks)
    return {
        "schema": VERIFY_TWO_MACHINE_EVIDENCE_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "node_id": evidence_report.get("node_id"),
        "network_id": evidence_report.get("network_id"),
        "chain_id": evidence_report.get("chain_id"),
        "local_tip": local_tip,
        "same_height_peer": dict(same_height_peer) if same_height_peer is not None else None,
        "checks": checks,
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-report", required=True, type=Path)
    parser.add_argument("--expected-created-token-symbol", action="append", default=[])
    parser.add_argument("--min-height", type=int)
    parser.add_argument("--out", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        report = verify_two_machine_evidence_report_v0(
            evidence_report=_load_json_object(args.evidence_report),
            expected_created_token_symbols=list(args.expected_created_token_symbol),
            min_height=args.min_height,
        )
        if args.out is not None:
            _write_json(args.out, report)
            report = {**report, "verification_report_path": str(args.out)}
    except Exception as exc:
        report = {
            "schema": VERIFY_TWO_MACHINE_EVIDENCE_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
