from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.cantor_shapeforge_bridge_report import (
    DEFAULT_SHAPEFORGE_WORLD_MODEL_PATH,
    build_cantor_shapeforge_bridge_report,
)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a ShapeForge bridge report from the Cantor assurance bundle.")
    parser.add_argument(
        "--world-model",
        default=str(DEFAULT_SHAPEFORGE_WORLD_MODEL_PATH),
        help="Path to the ShapeForge world model JSON",
    )
    parser.add_argument("--output", required=True, help="Path to write the bridge report JSON")
    args = parser.parse_args(argv)

    report = build_cantor_shapeforge_bridge_report(world_model_path=Path(args.world_model))
    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
