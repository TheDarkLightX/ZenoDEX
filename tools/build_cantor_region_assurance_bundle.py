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
from src.integration.region_ba_backends import DEFAULT_REGION_BA_BACKEND, resolve_region_ba_backend, supported_region_ba_backends


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build the default Cantor-region assurance bundle.")
    parser.add_argument("--output", required=True, help="Path to write the bundle JSON")
    parser.add_argument(
        "--backend",
        default=DEFAULT_REGION_BA_BACKEND,
        choices=supported_region_ba_backends(),
        help="RegionBA backend to use when constructing the bundle",
    )
    args = parser.parse_args(argv)

    bundle = build_default_cantor_region_assurance_bundle(ba=resolve_region_ba_backend(args.backend)).to_dict()
    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
