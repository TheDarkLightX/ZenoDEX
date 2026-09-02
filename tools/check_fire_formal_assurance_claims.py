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

from src.fire.pathing_v1 import fire_formal_assurance_claims_path  # noqa: E402
from src.fire.verifier.formal_assurance_claims_v1 import (  # noqa: E402
    FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA,
    verify_fire_formal_assurance_claims_file,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Fail-closed checker for FIRE formal assurance claims.")
    parser.add_argument(
        "--manifest",
        type=Path,
        default=fire_formal_assurance_claims_path(),
        help="Path to formal-assurance-claims.yaml",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON verification report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    ok, err, verification = verify_fire_formal_assurance_claims_file(args.manifest)
    if not ok or verification is None:
        payload = {
            "schema": FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA,
            "ok": False,
            "manifest_path": str(args.manifest.resolve()),
            "error": err or "formal_assurance_claims_verification_failed",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1

    sys.stdout.write(json.dumps(verification.to_report_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
