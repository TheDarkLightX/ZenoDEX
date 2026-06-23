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
    FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
    load_fire_registry_deployment_contract,
)
from src.fire.registry.release_v1 import load_fire_registry_release_metadata  # noqa: E402


BUILD_REPORT_SCHEMA = "zenodex/fire-registry-deployment-contract-build-report/v1"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a FIRE registry deployment contract.")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--snapshot-name", required=True)
    parser.add_argument("--required-signer-pubkey", required=True)
    parser.add_argument(
        "--release-metadata-file",
        type=Path,
        help="Optional release metadata file used to pin the expected contract summary into the deployment contract",
    )
    parser.add_argument("--contract-id", help="Optional explicit contract id; defaults to fire.registry.deploy.<snapshot>.v1")
    parser.add_argument("--description", default="Accept only the signed FIRE registry snapshot for the named publication lane.")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    contract_id = args.contract_id or f"fire.registry.deploy.{args.snapshot_name}.v1"
    payload = {
        "schema": FIRE_REGISTRY_DEPLOYMENT_CONTRACT_SCHEMA,
        "contract_id": contract_id,
        "snapshot_name": args.snapshot_name,
        "required_signer_pubkey": args.required_signer_pubkey,
        "require_signature": True,
        "description": args.description,
    }

    try:
        if args.release_metadata_file is not None:
            metadata, _ = load_fire_registry_release_metadata(args.release_metadata_file)
            if metadata.snapshot_name != args.snapshot_name:
                raise ValueError("release metadata snapshot_name mismatch")
            if metadata.signer_pubkey != args.required_signer_pubkey:
                raise ValueError("release metadata signer_pubkey mismatch")
            payload["contracts"] = [receipt.to_dict() for receipt in metadata.contract_receipts]
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")
        contract = load_fire_registry_deployment_contract(args.output)
    except (OSError, RuntimeError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    report = {
        "schema": BUILD_REPORT_SCHEMA,
        "ok": True,
        "output": str(args.output.resolve()),
        "contract_id": contract["contract_id"],
        "snapshot_name": contract["snapshot_name"],
        "required_signer_pubkey": contract["required_signer_pubkey"],
        "contract_hash": contract["contract_hash"],
        "contract_count": len(contract.get("contracts", [])),
        "contracts": contract.get("contracts", []),
    }
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
