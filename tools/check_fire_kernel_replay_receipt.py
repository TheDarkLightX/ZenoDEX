from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.kernel.kernel_replay_receipt_v1 import verify_fire_kernel_replay_receipt_file  # noqa: E402


def _sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed checker for FIRE kernel_replay_receipt.json files.")
    parser.add_argument("--receipt-file", type=Path, required=True, help="Path to kernel_replay_receipt.json")
    parser.add_argument("--object-manifest-file", type=Path, required=True, help="Path to object_manifest.json")
    parser.add_argument("--instance-manifest-file", type=Path, required=True, help="Path to instance_manifest.json")
    parser.add_argument("--replay-input-file", type=Path, required=True, help="Path to replay_input.json")
    parser.add_argument("--compile-receipt-file", type=Path, help="Optional path to compile_receipt.json; its sha256 will be used as an expected pin")
    parser.add_argument("--kernel-receipt-file", type=Path, help="Optional path to kernel_receipt.json; its sha256 will be used as an expected pin")
    parser.add_argument("--kernel-eval-receipt-file", type=Path, help="Optional path to kernel_eval_receipt.json; its sha256 will be used as an expected pin")
    parser.add_argument("--kernel-settlement-receipt-file", type=Path, help="Optional path to kernel_settlement_receipt.json; its sha256 will be used as an expected pin")
    parser.add_argument("--expected-receipt-sha256", help="Optional expected SHA-256 of kernel_replay_receipt.json")
    parser.add_argument("--expected-object-hash", help="Optional expected canonical object hash")
    parser.add_argument("--expected-instance-hash", help="Optional expected canonical instance hash")
    parser.add_argument("--expected-cert-sha256", help="Optional expected FIRE certificate sha256")
    parser.add_argument("--expected-replay-input-sha256", help="Optional expected SHA-256 of replay_input.json")
    parser.add_argument("--expected-compile-receipt-sha256", help="Optional expected SHA-256 of compile_receipt.json")
    parser.add_argument("--expected-kernel-receipt-sha256", help="Optional expected SHA-256 of kernel_receipt.json")
    parser.add_argument("--expected-kernel-eval-receipt-sha256", help="Optional expected SHA-256 of kernel_eval_receipt.json")
    parser.add_argument("--expected-kernel-settlement-receipt-sha256", help="Optional expected SHA-256 of kernel_settlement_receipt.json")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON report")
    args = parser.parse_args(argv)

    expected_compile_receipt_sha256 = args.expected_compile_receipt_sha256
    if args.compile_receipt_file is not None:
        expected_compile_receipt_sha256 = _sha256_file(args.compile_receipt_file.resolve())
    expected_kernel_receipt_sha256 = args.expected_kernel_receipt_sha256
    if args.kernel_receipt_file is not None:
        expected_kernel_receipt_sha256 = _sha256_file(args.kernel_receipt_file.resolve())
    expected_kernel_eval_receipt_sha256 = args.expected_kernel_eval_receipt_sha256
    if args.kernel_eval_receipt_file is not None:
        expected_kernel_eval_receipt_sha256 = _sha256_file(args.kernel_eval_receipt_file.resolve())
    expected_kernel_settlement_receipt_sha256 = args.expected_kernel_settlement_receipt_sha256
    if args.kernel_settlement_receipt_file is not None:
        expected_kernel_settlement_receipt_sha256 = _sha256_file(args.kernel_settlement_receipt_file.resolve())

    ok, err, verification = verify_fire_kernel_replay_receipt_file(
        args.receipt_file,
        object_manifest_path=args.object_manifest_file,
        instance_manifest_path=args.instance_manifest_file,
        replay_input_path=args.replay_input_file,
        expected_receipt_sha256=args.expected_receipt_sha256,
        expected_object_hash=args.expected_object_hash,
        expected_instance_hash=args.expected_instance_hash,
        expected_cert_sha256=args.expected_cert_sha256,
        expected_replay_input_sha256=args.expected_replay_input_sha256,
        expected_compile_receipt_sha256=expected_compile_receipt_sha256,
        expected_kernel_receipt_sha256=expected_kernel_receipt_sha256,
        expected_kernel_eval_receipt_sha256=expected_kernel_eval_receipt_sha256,
        expected_kernel_settlement_receipt_sha256=expected_kernel_settlement_receipt_sha256,
    )
    if not ok or verification is None:
        payload = {
            "schema": "zenodex/fire-kernel-replay-receipt-check-report/v1",
            "ok": False,
            "error": err or "kernel_replay_receipt_verification_failed",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1

    sys.stdout.write(json.dumps(verification.to_report_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
