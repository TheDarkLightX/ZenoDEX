#!/usr/bin/env python3
"""Verify a public ZenoLedger mirror index against local files."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_mirror import validate_mirror_index_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.verify_mirror_index_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a public ZenoLedger mirror index")
    parser.add_argument("--index", required=True, type=Path)
    parser.add_argument("--mirror-root", required=True, type=Path)
    args = parser.parse_args(argv)

    try:
        index = _load_json_object(args.index)
        validate_mirror_index_v0(index=index, mirror_root=args.mirror_root)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "mirror_index_hash": index["mirror_index_hash"],
            "artifact_count": index["artifact_count"],
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
