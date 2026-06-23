from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.verifier.settlement_apply_report_v1 import (  # noqa: E402
    FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA,
    verify_fire_settlement_apply_report,
)


CHECK_REPORT_SCHEMA = "zenodex/fire-settlement-apply-check-report/v1"


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Replay-check a FIRE settlement apply report.")
    parser.add_argument("--report-file", type=Path, required=True, help="JSON report emitted by apply_fire_settlement.py")
    parser.add_argument("--bundle-dir", type=Path, help="Optional persisted FIRE bundle directory to match against the report")
    parser.add_argument("--expected-object-hash", help="Optional expected object hash")
    parser.add_argument("--expected-instance-hash", help="Optional expected instance hash")
    parser.add_argument("--expected-cert-sha256", help="Optional expected certificate sha256")
    parser.add_argument("--expected-bundle-hash", help="Optional expected bundle hash")
    parser.add_argument("--expected-witness-hash", help="Optional expected witness binding hash")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON check report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        payload = json.loads(args.report_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    if not isinstance(payload, dict):
        print("apply report must be a JSON object", file=sys.stderr)
        return 1

    ok, err = verify_fire_settlement_apply_report(
        payload,
        expected_object_hash=args.expected_object_hash,
        expected_instance_hash=args.expected_instance_hash,
        expected_cert_sha256=args.expected_cert_sha256,
        expected_bundle_hash=args.expected_bundle_hash,
        expected_witness_hash=args.expected_witness_hash,
        expected_bundle_dir=args.bundle_dir,
    )
    report = {
        "schema": CHECK_REPORT_SCHEMA,
        "accepted": ok,
        "error": err,
        "report_schema": payload.get("schema"),
        "report_hash": payload.get("report_hash"),
        "expected_report_schema": FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA,
        "bundle_dir_checked": None if args.bundle_dir is None else str(args.bundle_dir.resolve()),
        "object_hash": payload.get("object_hash"),
        "instance_hash": payload.get("instance_hash"),
        "bundle_hash": payload.get("bundle_hash"),
        "witness_hash": payload.get("witness_hash"),
    }
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
