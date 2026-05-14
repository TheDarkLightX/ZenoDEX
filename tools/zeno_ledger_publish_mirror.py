#!/usr/bin/env python3
"""Publish indexed ZenoLedger mirror artifacts into a verified directory."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_mirror import publish_mirror_from_index_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.publish_mirror_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Publish indexed ZenoLedger mirror artifacts")
    parser.add_argument("--index", required=True, type=Path)
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--publish-root", required=True, type=Path)
    parser.add_argument("--receipt-out", type=Path)
    parser.add_argument("--include-extra", action="append", type=Path, default=[])
    args = parser.parse_args(argv)

    try:
        index = _load_json_object(args.index)
        receipt = publish_mirror_from_index_v0(
            index=index,
            source_root=args.source_root,
            index_path=args.index,
            publish_root=args.publish_root,
            extra_paths=list(args.include_extra),
        )
        receipt_out = args.receipt_out
        if receipt_out is None:
            receipt_out = args.publish_root / "mirror_publish_receipt.json"
        _write_json(receipt_out, receipt)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "publish_root": str(args.publish_root),
            "receipt_path": str(receipt_out),
            "receipt": receipt,
        }
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
