from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.cantor_region_assurance_bundle import build_default_cantor_region_assurance_bundle
from src.integration.region_ba_backends import resolve_region_ba_backend


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed parity check across two RegionBA backends.")
    parser.add_argument("--left", default="prefix", help="Left RegionBA backend")
    parser.add_argument("--right", default="bdd", help="Right RegionBA backend")
    parser.add_argument("--output", help="Optional path to write the shared invariant payload when parity holds")
    args = parser.parse_args(argv)

    left_payload = build_default_cantor_region_assurance_bundle(
        ba=resolve_region_ba_backend(args.left)
    ).to_dict()
    right_payload = build_default_cantor_region_assurance_bundle(
        ba=resolve_region_ba_backend(args.right)
    ).to_dict()

    if left_payload != right_payload:
        print(
            f"backend invariant failed: {args.left!r} payload differs from {args.right!r}",
            file=sys.stderr,
        )
        return 1

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(left_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
