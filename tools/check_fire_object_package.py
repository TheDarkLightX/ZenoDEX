from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.verifier.object_package_v1 import verify_fire_object_package  # noqa: E402


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Fail-closed checker for a FIRE object package directory.")
    parser.add_argument("--bundle-dir", type=Path, required=True, help="Path to the FIRE object package directory")
    parser.add_argument("--expected-bundle-hash", help="Optional expected bundle hash")
    parser.add_argument("--expected-bundle-file-sha256", help="Optional expected SHA-256 of bundle_manifest.json")
    parser.add_argument("--require-replay-input", action="store_true", help="Fail closed if replay_input.json is missing")
    parser.add_argument(
        "--require-compile-receipt",
        action="store_true",
        help="Fail closed if compile_receipt.json is missing",
    )
    parser.add_argument(
        "--require-kernel-receipt",
        action="store_true",
        help="Fail closed if kernel_receipt.json is missing",
    )
    parser.add_argument(
        "--require-kernel-eval-receipt",
        action="store_true",
        help="Fail closed if kernel_eval_receipt.json is missing",
    )
    parser.add_argument(
        "--require-kernel-replay-receipt",
        action="store_true",
        help="Fail closed if kernel_replay_receipt.json is missing",
    )
    parser.add_argument(
        "--require-kernel-settlement-receipt",
        action="store_true",
        help="Fail closed if kernel_settlement_receipt.json is missing",
    )
    parser.add_argument(
        "--require-proof-tree-cert",
        action="store_true",
        help="Fail closed if proof_tree_certificate.json is missing",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON verification report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    ok, err, verification = verify_fire_object_package(
        args.bundle_dir,
        expected_bundle_hash=args.expected_bundle_hash,
        expected_bundle_file_sha256=args.expected_bundle_file_sha256,
        require_replay_input=args.require_replay_input,
        require_compile_receipt=args.require_compile_receipt,
        require_kernel_receipt=args.require_kernel_receipt,
        require_kernel_eval_receipt=args.require_kernel_eval_receipt,
        require_kernel_replay_receipt=args.require_kernel_replay_receipt,
        require_kernel_settlement_receipt=args.require_kernel_settlement_receipt,
        require_proof_tree_cert=args.require_proof_tree_cert,
    )
    if not ok or verification is None:
        payload = {
            "schema": "zenodex/fire-object-package-check-report/v1",
            "ok": False,
            "bundle_dir": str(args.bundle_dir.resolve()),
            "require_replay_input": args.require_replay_input,
            "require_compile_receipt": args.require_compile_receipt,
            "require_kernel_receipt": args.require_kernel_receipt,
            "require_kernel_eval_receipt": args.require_kernel_eval_receipt,
            "require_kernel_replay_receipt": args.require_kernel_replay_receipt,
            "require_kernel_settlement_receipt": args.require_kernel_settlement_receipt,
            "require_proof_tree_cert": args.require_proof_tree_cert,
            "error": err or "object_package_verification_failed",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1

    payload = verification.to_report_dict()
    payload["require_replay_input"] = args.require_replay_input
    payload["require_compile_receipt"] = args.require_compile_receipt
    payload["require_kernel_receipt"] = args.require_kernel_receipt
    payload["require_kernel_eval_receipt"] = args.require_kernel_eval_receipt
    payload["require_kernel_replay_receipt"] = args.require_kernel_replay_receipt
    payload["require_kernel_settlement_receipt"] = args.require_kernel_settlement_receipt
    payload["require_proof_tree_cert"] = args.require_proof_tree_cert
    sys.stdout.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
