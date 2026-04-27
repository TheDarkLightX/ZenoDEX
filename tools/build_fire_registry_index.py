from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.registry.index_v1 import write_fire_registry_index  # noqa: E402


BUILD_REPORT_SCHEMA = "zenodex/fire-registry-index-build-report/v1"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a deterministic FIRE registry index from one or more bundle directories.")
    parser.add_argument("--bundle-dir", dest="bundle_dirs", action="append", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--signer-privkey", help="Optional BLS private key used to sign the registry index")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        index, index_file_sha256 = write_fire_registry_index(
            args.output,
            [path.resolve() for path in args.bundle_dirs],
            signer_privkey=args.signer_privkey,
        )
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    payload = {
        "schema": BUILD_REPORT_SCHEMA,
        "ok": True,
        "index_path": str(args.output.resolve()),
        "index_hash": index.index_hash,
        "index_file_sha256": index_file_sha256,
        "entry_count": len(index.entries),
        "contract_count": len(index.contract_receipts),
        "instance_gate_summary": index.instance_gate_summary.to_dict(),
        "certificate_instance_gate_summary": index.certificate_instance_gate_summary.to_dict(),
        "contracts": [receipt.to_dict() for receipt in index.contract_receipts],
        "bundle_paths": [entry.bundle_path for entry in index.entries],
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
        "signature_present": index.signature is not None,
        "signer_pubkey": index.signer_pubkey,
    }
    if args.pretty:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
