from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.kernel.kernel_receipt_v1 import (  # noqa: E402
    FIRE_KERNEL_RECEIPT_CHECK_REPORT_SCHEMA,
    verify_fire_kernel_receipt_file,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Fail-closed checker for FIRE kernel receipts.")
    parser.add_argument("--receipt-file", type=Path, required=True, help="Path to kernel_receipt.json")
    parser.add_argument("--object-manifest-file", type=Path, required=True, help="Path to object_manifest.json")
    parser.add_argument("--instance-manifest-file", type=Path, required=True, help="Path to instance_manifest.json")
    parser.add_argument("--expected-receipt-sha256", help="Optional expected SHA-256 of kernel_receipt.json")
    parser.add_argument("--expected-object-hash", help="Optional expected object_hash")
    parser.add_argument("--expected-instance-hash", help="Optional expected instance_hash")
    parser.add_argument("--expected-cert-sha256", help="Optional expected cert_sha256")
    parser.add_argument("--expected-kernel-ref-file-sha256", help="Optional expected canonical ref-model file sha256")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON verification report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    ok, err, verification = verify_fire_kernel_receipt_file(
        args.receipt_file,
        object_manifest_path=args.object_manifest_file,
        instance_manifest_path=args.instance_manifest_file,
        expected_receipt_sha256=args.expected_receipt_sha256,
        expected_object_hash=args.expected_object_hash,
        expected_instance_hash=args.expected_instance_hash,
        expected_cert_sha256=args.expected_cert_sha256,
        expected_kernel_ref_file_sha256=args.expected_kernel_ref_file_sha256,
    )
    if not ok or verification is None:
        payload = {
            "schema": FIRE_KERNEL_RECEIPT_CHECK_REPORT_SCHEMA,
            "ok": False,
            "receipt_path": str(args.receipt_file.resolve()),
            "object_manifest_path": str(args.object_manifest_file.resolve()),
            "instance_manifest_path": str(args.instance_manifest_file.resolve()),
            "error": err or "kernel_receipt_verification_failed",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1

    sys.stdout.write(json.dumps(verification.to_report_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
