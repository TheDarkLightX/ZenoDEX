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
    check_fire_registry_deployment_receipt,
)


CHECK_REPORT_SCHEMA = "zenodex/fire-registry-deployment-receipt-check-report/v1"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed checker for a FIRE registry deployment receipt.")
    parser.add_argument("--receipt-file", type=Path, required=True)
    parser.add_argument("--require-current", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = check_fire_registry_deployment_receipt(
        args.receipt_file,
        require_current=args.require_current,
    )
    if report["accepted"]:
        payload = {
            "schema": CHECK_REPORT_SCHEMA,
            "ok": True,
            "receipt_path": str(args.receipt_file.resolve()),
            "require_current": args.require_current,
            "contract_count": len(report.get("rebuilt_receipt", {}).get("contracts", [])),
            "contracts": report.get("rebuilt_receipt", {}).get("contracts", []),
            "violated_checks": [],
        }
        if args.pretty:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
        return 0

    payload = {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": False,
        "receipt_path": str(args.receipt_file.resolve()),
        "require_current": args.require_current,
        "violated_checks": report["violated_checks"],
        "error": report.get("error"),
    }
    if args.pretty:
        print(json.dumps(payload, indent=2, sort_keys=True), file=sys.stderr)
    else:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")), file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
