from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.compiler.zpl_v1 import compile_fire_zpl_file, write_compiled_fire_zpl  # noqa: E402


REPORT_SCHEMA = "zenodex/fire-zpl-compile-report/v1"


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Compile a minimal FIRE ZPL source file into an FMOS JSON spec.")
    parser.add_argument("source_file", type=Path, help="Path to a .zpl source file")
    parser.add_argument("--output", type=Path, required=True, help="Path to write the compiled FMOS JSON spec")
    parser.add_argument("--compact", action="store_true", help="Write compact JSON instead of pretty JSON")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the compile report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    try:
        payload = compile_fire_zpl_file(args.source_file)
        write_compiled_fire_zpl(args.output, payload, pretty=not args.compact)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    report = {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "source_file": str(args.source_file.resolve()),
        "output_file": str(args.output.resolve()),
        "object_id": payload["object_id"],
        "object_name": payload["object_name"],
        "object_version": payload["object_version"],
        "imports": [item["name"] for item in payload.get("imports", [])],
        "outputs": [item["name"] for item in payload.get("outputs", [])],
    }
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
