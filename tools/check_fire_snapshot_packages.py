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


CHECK_REPORT_SCHEMA = "zenodex/fire-snapshot-package-check-report/v1"


def _bundle_dirs(snapshot_dir: Path) -> list[Path]:
    return sorted(path.parent for path in snapshot_dir.glob("*/bundle_manifest.json"))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Schema-aware check for every FIRE object package in a snapshot directory.")
    parser.add_argument(
        "--snapshot-dir",
        type=Path,
        default=REPO_ROOT / "docs" / "fire_registry" / "devnet_v1",
        help="Snapshot directory containing FIRE bundle subdirectories",
    )
    parser.add_argument(
        "--require-replay-input",
        action="store_true",
        help="Fail closed if any bundle lacks replay_input.json",
    )
    parser.add_argument(
        "--require-compile-receipt",
        action="store_true",
        help="Fail closed if any bundle lacks compile_receipt.json",
    )
    parser.add_argument(
        "--require-kernel-receipt",
        action="store_true",
        help="Fail closed if any bundle lacks kernel_receipt.json",
    )
    parser.add_argument(
        "--require-kernel-eval-receipt",
        action="store_true",
        help="Fail closed if any bundle lacks kernel_eval_receipt.json",
    )
    parser.add_argument(
        "--require-kernel-replay-receipt",
        action="store_true",
        help="Fail closed if any bundle lacks kernel_replay_receipt.json",
    )
    parser.add_argument(
        "--require-kernel-settlement-receipt",
        action="store_true",
        help="Fail closed if any bundle lacks kernel_settlement_receipt.json",
    )
    parser.add_argument(
        "--require-proof-tree-cert",
        action="store_true",
        help="Fail closed if any bundle lacks proof_tree_certificate.json",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON report")
    args = parser.parse_args(argv)

    reports: list[dict[str, object]] = []
    all_ok = True
    for bundle_dir in _bundle_dirs(args.snapshot_dir):
        ok, err, verification = verify_fire_object_package(
            bundle_dir,
            require_replay_input=args.require_replay_input,
            require_compile_receipt=args.require_compile_receipt,
            require_kernel_receipt=args.require_kernel_receipt,
            require_kernel_eval_receipt=args.require_kernel_eval_receipt,
            require_kernel_replay_receipt=args.require_kernel_replay_receipt,
            require_kernel_settlement_receipt=args.require_kernel_settlement_receipt,
            require_proof_tree_cert=args.require_proof_tree_cert,
        )
        if ok and verification is not None:
            bundle_report = verification.to_report_dict()
            reports.append(
                {
                    "bundle_dir": str(bundle_dir.resolve()),
                    "ok": True,
                    "bundle_hash": bundle_report["bundle_hash"],
                    "object_name": bundle_report["object_name"],
                    "object_version": bundle_report["object_version"],
                    "object_family": bundle_report["object_family"],
                    "object_hash": bundle_report["object_hash"],
                    "instance_hash": bundle_report["instance_hash"],
                    "lock_hash": bundle_report["lock_hash"],
                    "cert_sha256": bundle_report["cert_sha256"],
                    "artifact_schemas_valid": bundle_report["artifact_schemas_valid"],
                    "compile_receipt_present": bundle_report["compile_receipt_present"],
                    "kernel_receipt_present": bundle_report["kernel_receipt_present"],
                    "kernel_eval_receipt_present": bundle_report["kernel_eval_receipt_present"],
                    "kernel_replay_receipt_present": bundle_report["kernel_replay_receipt_present"],
                    "kernel_settlement_receipt_present": bundle_report["kernel_settlement_receipt_present"],
                    "proof_tree_cert_present": bundle_report["proof_tree_cert_present"],
                    "replay_input_present": bundle_report["replay_input_present"],
                }
            )
            continue

        all_ok = False
        reports.append(
            {
                "bundle_dir": str(bundle_dir.resolve()),
                "ok": False,
                "error": err or "object_package_verification_failed",
            }
        )

    payload = {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": all_ok,
        "snapshot_dir": str(args.snapshot_dir.resolve()),
        "require_replay_input": args.require_replay_input,
        "require_compile_receipt": args.require_compile_receipt,
        "require_kernel_receipt": args.require_kernel_receipt,
        "require_kernel_eval_receipt": args.require_kernel_eval_receipt,
        "require_kernel_replay_receipt": args.require_kernel_replay_receipt,
        "require_kernel_settlement_receipt": args.require_kernel_settlement_receipt,
        "require_proof_tree_cert": args.require_proof_tree_cert,
        "bundle_count": len(reports),
        "bundles": reports,
    }
    rendered = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True)
    stream = sys.stdout if all_ok else sys.stderr
    stream.write(rendered + "\n")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
