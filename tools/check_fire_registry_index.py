from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.registry.index_v1 import verify_fire_registry_index  # noqa: E402


CHECK_REPORT_SCHEMA = "zenodex/fire-registry-index-check-report/v1"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed checker for a FIRE registry index.")
    parser.add_argument("--index-file", type=Path, required=True)
    parser.add_argument("--expected-index-hash")
    parser.add_argument("--expected-index-file-sha256")
    parser.add_argument("--expected-signer-pubkey")
    parser.add_argument("--require-signature", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    ok, err, index = verify_fire_registry_index(
        args.index_file,
        expected_index_hash=args.expected_index_hash,
        expected_index_file_sha256=args.expected_index_file_sha256,
        expected_signer_pubkey=args.expected_signer_pubkey,
        require_signature=args.require_signature,
    )
    if ok and index is not None:
        payload = {
            "schema": CHECK_REPORT_SCHEMA,
            "ok": True,
            "index_path": str(args.index_file.resolve()),
            "index_hash": index.index_hash,
            "entry_count": len(index.entries),
            "contract_count": len(index.contract_receipts),
            "instance_gate_summary": index.instance_gate_summary.to_dict(),
            "certificate_instance_gate_summary": index.certificate_instance_gate_summary.to_dict(),
            "contracts": [receipt.to_dict() for receipt in index.contract_receipts],
            "signature_present": index.signature is not None,
            "signer_pubkey": index.signer_pubkey,
            "objects": [
                {
                    "object_name": entry.object_name,
                    "object_version": entry.object_version,
                    "object_family": entry.object_family,
                    "bundle_path": entry.bundle_path,
                    "object_hash": entry.manifest_hash,
                    "instance_hash": entry.instance_hash,
                    "lock_hash": entry.lock_hash,
                    "instance_gates": entry.instance_gate_report.to_dict(),
                    "certificate_instance_gate_claims": entry.certificate_instance_gate_claims.to_dict(),
                }
                for entry in index.entries
            ],
        }
        sys.stdout.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 0

    payload = {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": False,
        "index_path": str(args.index_file.resolve()),
        "error": err or "index_verification_failed",
    }
    sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
