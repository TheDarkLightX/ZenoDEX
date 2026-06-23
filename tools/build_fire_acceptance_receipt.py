from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.verifier.acceptance_receipt_v1 import write_fire_acceptance_receipt  # noqa: E402


BUILD_REPORT_SCHEMA = "zenodex/fire-acceptance-receipt-build-report/v1"


def _add_strict_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--require-replay-input", action="store_true")
    parser.add_argument("--require-compile-receipt", action="store_true")
    parser.add_argument("--require-kernel-receipt", action="store_true")
    parser.add_argument("--require-kernel-eval-receipt", action="store_true")
    parser.add_argument("--require-kernel-replay-receipt", action="store_true")
    parser.add_argument("--require-kernel-settlement-receipt", action="store_true")
    parser.add_argument("--require-proof-tree-cert", action="store_true")


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Build a hash-bound FIRE package acceptance receipt.")
    parser.add_argument("--bundle-dir", type=Path, required=True, help="Path to the accepted FIRE object package")
    parser.add_argument("--output", type=Path, required=True, help="Path to write fire_acceptance_receipt.json")
    parser.add_argument("--expected-bundle-hash", help="Optional expected bundle hash")
    parser.add_argument("--expected-bundle-file-sha256", help="Optional expected SHA-256 of bundle_manifest.json")
    _add_strict_flags(parser)
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON build report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        receipt = write_fire_acceptance_receipt(
            args.output,
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
    except (OSError, RuntimeError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    payload = {
        "schema": BUILD_REPORT_SCHEMA,
        "ok": True,
        "output": str(args.output.resolve()),
        "bundle_dir": str(args.bundle_dir.resolve()),
        "bundle_hash": receipt["bundle_hash"],
        "bundle_manifest_sha256": receipt["bundle_manifest_sha256"],
        "object_hash": receipt["object_hash"],
        "instance_hash": receipt["instance_hash"],
        "cert_sha256": receipt["cert_sha256"],
        "receipt_sha256": receipt["receipt_sha256"],
        "authorizes_settlement": False,
        "strict_requirements": receipt["strict_requirements"],
    }
    sys.stdout.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
