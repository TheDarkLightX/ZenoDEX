from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.verifier.settlement_apply_artifact_v1 import (  # noqa: E402
    check_fire_settlement_apply_artifact_receipt,
)


CHECK_REPORT_SCHEMA = "zenodex/fire-settlement-apply-artifact-receipt-check-report/v1"


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Replay-check a FIRE settlement apply artifact receipt.")
    parser.add_argument("--receipt-file", type=Path, required=True, help="Receipt emitted by build_fire_settlement_apply_artifact_receipt.py")
    parser.add_argument("--expected-bundle-dir", type=Path, help="Require the receipt to point at this exact bundle directory")
    parser.add_argument("--expected-bundle-hash", help="Require this exact bundle hash")
    parser.add_argument("--expected-object-hash", help="Require this exact object hash")
    parser.add_argument("--expected-instance-hash", help="Require this exact instance hash")
    parser.add_argument("--expected-cert-sha256", help="Require this exact certificate sha256")
    parser.add_argument("--expected-witness-hash", help="Require this exact witness binding hash")
    parser.add_argument("--expected-report-hash", help="Require this exact apply report hash")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON check report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    report = check_fire_settlement_apply_artifact_receipt(
        args.receipt_file,
        expected_bundle_dir=args.expected_bundle_dir,
        expected_bundle_hash=args.expected_bundle_hash,
        expected_object_hash=args.expected_object_hash,
        expected_instance_hash=args.expected_instance_hash,
        expected_cert_sha256=args.expected_cert_sha256,
        expected_witness_hash=args.expected_witness_hash,
        expected_report_hash=args.expected_report_hash,
    )
    payload = {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": report["accepted"],
        **report,
    }
    stream = sys.stdout if report["accepted"] else sys.stderr
    if args.pretty:
        print(json.dumps(payload, indent=2, sort_keys=True), file=stream)
    else:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")), file=stream)
    return 0 if report["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
