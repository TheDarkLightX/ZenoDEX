#!/usr/bin/env python3
"""Build a compact public ZenoLedger testnet status object."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_testnet_status import build_testnet_status_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.make_testnet_status_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a public ZenoLedger testnet status JSON object")
    parser.add_argument("--network-id", required=True)
    parser.add_argument("--mirror-index", required=True, type=Path)
    parser.add_argument("--mirror-root", required=True, type=Path)
    parser.add_argument("--watcher-attestation", required=True, action="append", type=Path)
    parser.add_argument("--feature-suite", type=Path)
    parser.add_argument("--feature-suite-run-report", type=Path)
    parser.add_argument("--quorum-report", action="append", default=[], type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    try:
        status = build_testnet_status_v0(
            network_id=args.network_id,
            mirror_index=_load_json_object(args.mirror_index),
            mirror_root=args.mirror_root,
            watcher_attestations=[
                _load_json_object(path)
                for path in args.watcher_attestation
            ],
            feature_suite=(
                _load_json_object(args.feature_suite)
                if args.feature_suite is not None
                else None
            ),
            feature_suite_run_report=(
                _load_json_object(args.feature_suite_run_report)
                if args.feature_suite_run_report is not None
                else None
            ),
            quorum_reports=[_load_json_object(path) for path in args.quorum_report],
        )
        if args.out is not None:
            _write_json(args.out, status)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "testnet_status_hash": status["testnet_status_hash"],
            "watcher_count": status["watcher_count"],
            "quorum_report_count": status["quorum_report_count"],
            "artifact_count": status["artifact_count"],
        }
        if args.out is not None:
            report["status_path"] = str(args.out)
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
