#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

import check_zusd_repay_assurance_manifest as base


DEFAULT_MANIFEST = Path(__file__).resolve().with_name(
    "perp_submission_auth_field_selector_assurance_manifest.json"
)


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if "--manifest" not in args:
        args = ["--manifest", str(DEFAULT_MANIFEST), *args]
    return base.main(args)


if __name__ == "__main__":
    raise SystemExit(main())
