from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.compiler.fmos_file_v1 import (  # noqa: E402
    load_fire_math_object_spec_file,
    verify_fire_math_object_spec_file,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Fail-closed checker for FIRE FMOS spec files.")
    parser.add_argument("spec_file", type=Path, help="Path to a FIRE FMOS spec JSON file")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON verification report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    try:
        spec_file = load_fire_math_object_spec_file(args.spec_file)
        ok, err = verify_fire_math_object_spec_file(spec_file)
        if not ok:
            raise ValueError(err or "unknown FIRE FMOS spec validation error")
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    report = {
        "schema": "zenodex/fire-fmos-spec-check-report/v1",
        "ok": True,
        "spec_file": str(args.spec_file.resolve()),
        "object_id": spec_file.object_id,
        "object_name": spec_file.object_name,
        "object_version": spec_file.object_version,
        "term_fields": [
            {
                "name": field.name,
                "unit": field.unit,
                "minimum": field.minimum,
                "maximum": field.maximum,
            }
            for field in spec_file.term_fields
        ],
        "source_bounds": [bound.name for bound in spec_file.source_bounds],
        "imports": [imported.name for imported in spec_file.imports],
        "witnesses": [witness.name for witness in spec_file.witnesses],
        "outputs": [output.name for output in spec_file.outputs],
    }
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
