from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.cantor_region_backend_invariance_receipt import (
    build_cantor_region_backend_invariance_receipt,
)
from src.integration.region_ba_backends import DEFAULT_REGION_BA_BACKEND


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Cantor RegionBA backend invariance receipt.")
    parser.add_argument("--left", default=DEFAULT_REGION_BA_BACKEND, help="Left RegionBA backend")
    parser.add_argument("--right", default="bdd", help="Right RegionBA backend")
    parser.add_argument("--output", required=True, help="Path to write the receipt JSON")
    parser.add_argument(
        "--require-equal",
        action="store_true",
        help="Fail closed unless the compared backend payloads are exactly equal",
    )
    args = parser.parse_args(argv)

    try:
        receipt = build_cantor_region_backend_invariance_receipt(
            left_backend=args.left,
            right_backend=args.right,
        )
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    if args.require_equal and not receipt.payload_equal:
        print("backend invariance receipt indicates unequal payloads", file=sys.stderr)
        return 1

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(receipt.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
