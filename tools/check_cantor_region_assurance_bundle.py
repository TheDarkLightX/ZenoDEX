from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.cantor_region_assurance_verify import verify_cantor_region_assurance_bundle_payload


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed verifier for a Cantor-region assurance bundle.")
    parser.add_argument("bundle", help="Path to a bundle JSON file")
    parser.add_argument(
        "--require-current-default",
        action="store_true",
        help="Require the payload to match the current deterministic default bundle exactly",
    )
    args = parser.parse_args(argv)

    payload = json.loads(Path(args.bundle).read_text(encoding="utf-8"))
    ok, err = verify_cantor_region_assurance_bundle_payload(
        payload,
        require_current_default=bool(args.require_current_default),
    )
    if not ok:
        print(err or "bundle verification failed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
