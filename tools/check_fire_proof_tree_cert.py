from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.verifier.proof_tree_cert_v1 import (  # noqa: E402
    FIRE_PROOF_TREE_CERT_CHECK_REPORT_SCHEMA,
    verify_fire_proof_tree_certificate_file,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Fail-closed checker for draft FIRE proof-tree certificates.")
    parser.add_argument("--cert-file", type=Path, required=True, help="Path to the draft proof-tree cert JSON")
    parser.add_argument("--expected-object-hash", help="Optional expected object hash")
    parser.add_argument("--expected-instance-hash", help="Optional expected instance hash")
    parser.add_argument("--expected-certificate-sha256", help="Optional expected runtime certificate sha256")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON verification report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    ok, err, verification = verify_fire_proof_tree_certificate_file(
        args.cert_file,
        expected_object_hash=args.expected_object_hash,
        expected_instance_hash=args.expected_instance_hash,
        expected_certificate_sha256=args.expected_certificate_sha256,
    )
    if not ok or verification is None:
        payload = {
            "schema": FIRE_PROOF_TREE_CERT_CHECK_REPORT_SCHEMA,
            "ok": False,
            "certificate_path": str(args.cert_file.resolve()),
            "error": err or "proof_tree_cert_verification_failed",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1

    sys.stdout.write(json.dumps(verification.to_report_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
