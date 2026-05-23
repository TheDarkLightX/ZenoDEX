#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.autotrader_risk_disclosure import (  # noqa: E402
    build_autotrader_risk_disclosure,
)
from src.integration.zenograph_ranking_review_bundle_verify import (  # noqa: E402
    verify_zenograph_ranking_review_bundle_manifest,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verify a ZenoGraph ranking review bundle manifest against emitted artifacts.",
        epilog=(
            "Advanced experimental automation review verifier. "
            "This only verifies non-executing review artifacts."
        ),
    )
    parser.add_argument("--manifest-file", required=True, type=Path)
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    payload = json.loads(args.manifest_file.read_text(encoding="utf-8"))
    result = verify_zenograph_ranking_review_bundle_manifest(
        manifest_path=args.manifest_file,
        payload=payload,
    )
    report = {
        "schema": result.schema,
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="shadow",
            requires_explicit_acknowledgement=False,
            user_acknowledged=False,
        ),
        **result.to_dict(),
    }
    text = json.dumps(report, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    sys.stdout.write(text)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
