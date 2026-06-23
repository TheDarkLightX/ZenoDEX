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
    write_fire_settlement_apply_artifact_receipt,
)


BUILD_REPORT_SCHEMA = "zenodex/fire-settlement-apply-artifact-receipt-build-report/v1"


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Write a receipt for a verified FIRE settlement apply report.")
    parser.add_argument("--report-file", type=Path, required=True, help="JSON report emitted by apply_fire_settlement.py")
    parser.add_argument("--bundle-dir", type=Path, required=True, help="Persisted FIRE bundle directory matched by the report")
    parser.add_argument("--output", type=Path, required=True, help="Output receipt path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON build report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        receipt = write_fire_settlement_apply_artifact_receipt(args.output, args.report_file, args.bundle_dir)
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    report = {
        "schema": BUILD_REPORT_SCHEMA,
        "ok": True,
        "output_path": str(args.output.resolve()),
        "report_hash": receipt["report_hash"],
        "bundle_hash": receipt["bundle_hash"],
        "object_hash": receipt["object_hash"],
        "instance_hash": receipt["instance_hash"],
        "cert_sha256": receipt["cert_sha256"],
        "witness_hash": receipt["witness_hash"],
        "receipt_sha256": receipt["receipt_sha256"],
    }
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
