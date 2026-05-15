#!/usr/bin/env python3
"""Build a public mirror index for a ZenoLedger artifact bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_mirror import build_mirror_index_v0, validate_mirror_index_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.make_mirror_index_report.v0"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a public mirror index for ZenoLedger artifacts")
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--mirror-root", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)

    try:
        index = build_mirror_index_v0(
            mirror_root=args.mirror_root,
            manifest_path=args.manifest,
            exclude_paths=[args.out],
        )
        _write_json(args.out, index)
        validate_mirror_index_v0(index=index, mirror_root=args.mirror_root)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "mirror_index_path": str(args.out),
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
