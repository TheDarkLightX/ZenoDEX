#!/usr/bin/env python3
"""Run a same-machine two-operator ZenoLedger public-testnet rehearsal."""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)
from tools.zeno_ledger_operator_rehearsal import run_operator_rehearsal_v0
from tools.operator_report_output import emit_operator_json


REPORT_SCHEMA = "zenodex.zeno_ledger.dual_operator_rehearsal_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _remove_tree(path: Path) -> None:
    if path.exists():
        shutil.rmtree(path)


def _require_equal(name: str, left: object, right: object, errors: list[str]) -> None:
    if left != right:
        errors.append(f"{name} mismatch")


def run_dual_operator_rehearsal_v0(
    *,
    out_dir: Path,
    network_id: str,
    chain_id: str,
    sequencer_id: str,
    time_ms: int,
    token_symbol: str,
    operator_id: str,
    observed_time_ms: int | None,
) -> dict[str, Any]:
    root = out_dir.resolve()
    operator_a_bundle_root = root / "operator_a_bundle"
    operator_a2_bundle_root = root / "operator_a2_independent_bundle"
    operator_b_bundle_root = root / "operator_b_bundle_copy"
    operator_b_out_dir = root / "operator_b_replay"
    report_path = root / "dual_operator_rehearsal_report.json"

    root.mkdir(parents=True, exist_ok=True)
    for path in (
        operator_a_bundle_root,
        operator_a2_bundle_root,
        operator_b_bundle_root,
        operator_b_out_dir,
    ):
        _remove_tree(path)

    operator_a_build = build_public_testnet_bundle_v0(
        out_dir=operator_a_bundle_root,
        network_id=network_id,
        chain_id=chain_id,
        sequencer_id=sequencer_id,
        time_ms=time_ms,
        token_symbol=token_symbol,
    )
    operator_a2_build = build_public_testnet_bundle_v0(
        out_dir=operator_a2_bundle_root,
        network_id=network_id,
        chain_id=chain_id,
        sequencer_id=sequencer_id,
        time_ms=time_ms,
        token_symbol=token_symbol,
    )

    operator_a_status = _load_json_object(operator_a_bundle_root / "testnet_status.json")
    operator_a2_status = _load_json_object(operator_a2_bundle_root / "testnet_status.json")
    operator_a_mirror_index = _load_json_object(operator_a_bundle_root / "bootstrap" / "mirror_index.json")
    operator_a2_mirror_index = _load_json_object(operator_a2_bundle_root / "bootstrap" / "mirror_index.json")
    operator_a_feature_suite = _load_json_object(operator_a_bundle_root / "core_features" / "feature_suite.json")
    operator_a2_feature_suite = _load_json_object(operator_a2_bundle_root / "core_features" / "feature_suite.json")

    errors: list[str] = []
    _require_equal(
        "testnet status hash",
        operator_a_status.get("testnet_status_hash"),
        operator_a2_status.get("testnet_status_hash"),
        errors,
    )
    _require_equal(
        "mirror index hash",
        operator_a_mirror_index.get("mirror_index_hash"),
        operator_a2_mirror_index.get("mirror_index_hash"),
        errors,
    )
    _require_equal(
        "feature suite hash",
        operator_a_feature_suite.get("feature_suite_hash"),
        operator_a2_feature_suite.get("feature_suite_hash"),
        errors,
    )
    _require_equal(
        "covered features",
        operator_a_build.get("covered_features"),
        operator_a2_build.get("covered_features"),
        errors,
    )

    if errors:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": errors,
            "operator_a_bundle_root": str(operator_a_bundle_root),
            "operator_a2_bundle_root": str(operator_a2_bundle_root),
            "independent_build_match": False,
        }
        _write_json(report_path, report)
        return report

    shutil.copytree(operator_a_bundle_root, operator_b_bundle_root)
    peer_attestation_path = (
        operator_b_bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    )
    operator_b_rehearsal = run_operator_rehearsal_v0(
        bundle_root=operator_b_bundle_root,
        operator_id=operator_id,
        out_dir=operator_b_out_dir,
        observed_time_ms=observed_time_ms,
        peer_watcher_attestation_paths=[peer_attestation_path],
    )
    if operator_b_rehearsal.get("ok") is not True:
        raise ValueError("operator B rehearsal rejected")

    report = {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "network_id": network_id,
        "chain_id": chain_id,
        "operator_a_bundle_root": str(operator_a_bundle_root),
        "operator_a2_bundle_root": str(operator_a2_bundle_root),
        "operator_b_bundle_root": str(operator_b_bundle_root),
        "operator_b_out_dir": str(operator_b_out_dir),
        "operator_id": operator_id,
        "independent_build_match": True,
        "operator_b_rehearsal_ok": True,
        "testnet_status_hash": operator_a_status["testnet_status_hash"],
        "operator_a2_testnet_status_hash": operator_a2_status["testnet_status_hash"],
        "mirror_index_hash": operator_a_mirror_index["mirror_index_hash"],
        "operator_a2_mirror_index_hash": operator_a2_mirror_index["mirror_index_hash"],
        "feature_suite_hash": operator_a_feature_suite["feature_suite_hash"],
        "operator_a2_feature_suite_hash": operator_a2_feature_suite["feature_suite_hash"],
        "covered_feature_count": operator_a_build["covered_feature_count"],
        "covered_features": operator_a_build["covered_features"],
        "combined_watcher_count": operator_b_rehearsal["combined_watcher_count"],
        "combined_testnet_status_hash": operator_b_rehearsal["combined_testnet_status_hash"],
        "operator_attestation_hash": operator_b_rehearsal["operator_attestation_hash"],
        "last_header_hash": operator_b_rehearsal["last_header_hash"],
        "last_app_hash": operator_b_rehearsal["last_app_hash"],
        "report_path": str(report_path),
    }
    _write_json(report_path, report)
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run a same-machine two-operator ZenoLedger rehearsal")
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    parser.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    parser.add_argument("--token-symbol", default="tZENO")
    parser.add_argument("--operator-id", default="operator-b")
    parser.add_argument("--observed-time-ms", type=int)
    args = parser.parse_args(argv)

    try:
        report = run_dual_operator_rehearsal_v0(
            out_dir=args.out_dir,
            network_id=args.network_id,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
            operator_id=args.operator_id,
            observed_time_ms=args.observed_time_ms,
        )
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    emit_operator_json(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
