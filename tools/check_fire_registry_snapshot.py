from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.registry.release_v1 import (  # noqa: E402
    verify_fire_registry_release,
)


CHECK_REPORT_SCHEMA = "zenodex/fire-registry-snapshot-check-report/v1"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed checker for a pinned FIRE registry snapshot.")
    parser.add_argument("--metadata-file", type=Path, required=True)
    parser.add_argument("--expected-snapshot-name")
    parser.add_argument("--expected-metadata-file-sha256")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    ok, err, metadata = verify_fire_registry_release(
        args.metadata_file,
        expected_snapshot_name=args.expected_snapshot_name,
        expected_metadata_file_sha256=args.expected_metadata_file_sha256,
    )
    if ok and metadata is not None:
        payload = {
            "schema": CHECK_REPORT_SCHEMA,
            "ok": True,
            "metadata_path": str(args.metadata_file.resolve()),
            "snapshot_name": metadata.snapshot_name,
            "index_path": metadata.index_path,
            "index_hash": metadata.index_hash,
            "index_file_sha256": metadata.index_file_sha256,
            "contract_count": len(metadata.contract_receipts),
            "instance_gate_summary": metadata.instance_gate_summary.to_dict(),
            "certificate_instance_gate_summary": metadata.certificate_instance_gate_summary.to_dict(),
            "contracts": [receipt.to_dict() for receipt in metadata.contract_receipts],
            "require_signature": metadata.require_signature,
            "signer_pubkey": metadata.signer_pubkey,
        }
        sys.stdout.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 0

    payload = {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": False,
        "metadata_path": str(args.metadata_file.resolve()),
        "error": err or "snapshot_verification_failed",
    }
    sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
