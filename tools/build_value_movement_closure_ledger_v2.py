#!/usr/bin/env python3
"""Build or compare the canonical O-005B V2 closure-ledger artifact."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.value_movement_closure_ledger_v2 import (  # noqa: E402
    ARTIFACT_RELATIVE_PATH_V2,
    ValueMovementClosureLedgerRejectV2,
    build_ledger_bytes_v2,
    check_ledger_v2,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output = args.root / ARTIFACT_RELATIVE_PATH_V2
    try:
        if args.check:
            report = check_ledger_v2(args.root)
            if report["ok"] is not True:
                print(f"REJECT {report['findings']}", file=sys.stderr)
                return 1
            print(f"OK {output}")
            return 0
        expected = build_ledger_bytes_v2(args.root)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(expected)
        print(f"wrote {output}")
        return 0
    except (OSError, ValueMovementClosureLedgerRejectV2) as exc:
        print(f"REJECT {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
