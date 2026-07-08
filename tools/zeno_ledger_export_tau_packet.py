#!/usr/bin/env python3
"""Export a ZenoLedger checkpoint as an adapter-neutral Tau handoff packet."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_tau_export import build_tau_export_packet_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.export_tau_packet_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Export a ZenoLedger checkpoint as a Tau handoff packet")
    parser.add_argument("--checkpoint", required=True, type=Path)
    parser.add_argument("--header", required=True, type=Path)
    parser.add_argument("--body", required=True, type=Path)
    parser.add_argument("--profile", required=True, type=Path)
    parser.add_argument("--tau-network-id", required=True)
    parser.add_argument("--tau-adapter-ref", required=True)
    parser.add_argument("--cross-shard-posting-summary", type=Path, action="append")
    parser.add_argument(
        "--cross-shard-posting-summary-requirement",
        choices=("optional", "required", "forbidden", "body_evidence"),
        default="optional",
    )
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    try:
        posting_summaries = tuple(
            _load_json_object(path)
            for path in (args.cross_shard_posting_summary or ())
        )
        packet = build_tau_export_packet_v0(
            checkpoint=_load_json_object(args.checkpoint),
            header=_load_json_object(args.header),
            body=_load_json_object(args.body),
            profile=_load_json_object(args.profile),
            tau_network_id=args.tau_network_id,
            tau_adapter_ref=args.tau_adapter_ref,
            cross_shard_posting_summaries=posting_summaries,
            cross_shard_posting_summary_requirement=(
                args.cross_shard_posting_summary_requirement
            ),
        )
        if args.out is not None:
            _write_json(args.out, packet)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "packet": packet,
        }
        if args.out is not None:
            report["packet_path"] = str(args.out)
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
