#!/usr/bin/env python3
"""Build a ZenoLedger feature-suite manifest from feature-lane manifests."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_feature_suite import build_feature_suite_manifest_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.make_feature_suite_report.v0"


def _parse_lane(value: str) -> tuple[str, Path]:
    if "=" not in value:
        raise ValueError("--lane must be FEATURE_ID=MANIFEST_PATH")
    feature_id, path_text = value.split("=", 1)
    if feature_id == "" or path_text == "":
        raise ValueError("--lane must be FEATURE_ID=MANIFEST_PATH")
    return feature_id, Path(path_text)


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a ZenoLedger feature-suite manifest")
    parser.add_argument("--suite-name", required=True)
    parser.add_argument("--lane", action="append", required=True, help="FEATURE_ID=MANIFEST_PATH")
    parser.add_argument("--required-feature", action="append", default=[])
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)

    try:
        suite = build_feature_suite_manifest_v0(
            suite_name=args.suite_name,
            lanes=[_parse_lane(item) for item in args.lane],
            required_features=list(args.required_feature),
        )
        _write_json(args.out, suite)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "suite_path": str(args.out),
            "feature_suite_hash": suite["feature_suite_hash"],
            "feature_count": suite["feature_count"],
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
