from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.registry.deployment_contract_v1 import (  # noqa: E402
    write_fire_registry_deployment_receipt,
)


BUILD_REPORT_SCHEMA = "zenodex/fire-registry-deployment-receipt-build-report/v1"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a FIRE registry deployment receipt from a contract and release metadata.")
    parser.add_argument("--contract-file", type=Path, required=True)
    parser.add_argument("--release-metadata-file", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        receipt = write_fire_registry_deployment_receipt(
            args.output,
            args.contract_file,
            args.release_metadata_file,
        )
    except (OSError, RuntimeError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    payload = {
        "schema": BUILD_REPORT_SCHEMA,
        "ok": True,
        "output": str(args.output.resolve()),
        "contract_id": receipt["contract_id"],
        "snapshot_name": receipt["snapshot_name"],
        "contract_count": len(receipt.get("contracts", [])),
        "contracts": receipt.get("contracts", []),
        "receipt_sha256": receipt["receipt_sha256"],
        "contract_path": receipt["contract_path"],
        "release_metadata_path": receipt["release_metadata_path"],
        "required_signer_pubkey": receipt["required_signer_pubkey"],
    }
    if args.pretty:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
