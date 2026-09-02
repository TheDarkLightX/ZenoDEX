#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.pathing_v1 import (  # noqa: E402
    fire_acceptance_receipt_schema_path,
    fire_formal_assurance_claims_path,
    fire_verifier_rules_path,
)
from src.fire.verifier.release_assurance_v1 import (  # noqa: E402
    FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA,
    verify_fire_release_assurance,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run the FIRE release assurance gate.")
    parser.add_argument("--formal-claims-manifest", type=Path, default=fire_formal_assurance_claims_path())
    parser.add_argument("--acceptance-receipt-schema", type=Path, default=fire_acceptance_receipt_schema_path())
    parser.add_argument("--verifier-rules", type=Path, default=fire_verifier_rules_path())
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON verification report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    ok, err, verification = verify_fire_release_assurance(
        formal_claims_manifest=args.formal_claims_manifest,
        acceptance_receipt_schema=args.acceptance_receipt_schema,
        verifier_rules=args.verifier_rules,
    )
    if not ok or verification is None:
        payload = {
            "schema": FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA,
            "ok": False,
            "formal_claims_manifest": str(args.formal_claims_manifest.resolve()),
            "acceptance_receipt_schema": str(args.acceptance_receipt_schema.resolve()),
            "verifier_rules": str(args.verifier_rules.resolve()),
            "error": err or "fire_release_assurance_failed",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1

    sys.stdout.write(json.dumps(verification.to_report_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
