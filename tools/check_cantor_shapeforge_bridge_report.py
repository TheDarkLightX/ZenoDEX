from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.cantor_shapeforge_bridge_verify import (
    verify_cantor_shapeforge_bridge_report_payload,
)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed verifier for a Cantor-to-ShapeForge bridge report.")
    parser.add_argument("report", help="Path to a bridge report JSON file")
    parser.add_argument(
        "--require-current",
        action="store_true",
        help="Require the payload to match the current deterministic bridge construction exactly",
    )
    args = parser.parse_args(argv)

    payload = json.loads(Path(args.report).read_text(encoding="utf-8"))
    ok, err = verify_cantor_shapeforge_bridge_report_payload(
        payload,
        require_current=bool(args.require_current),
    )
    if not ok:
        print(err or "bridge verification failed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
