#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.world_model_validate import _resolve_linked_path, validate_artifact


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate a promoted ShapeForge world-model artifact.")
    parser.add_argument("path", type=Path, help="Path to a promoted world-model, negative-knowledge, or target-shapes JSON file")
    args = parser.parse_args()

    errors = validate_artifact(args.path)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print(f"OK {args.path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
