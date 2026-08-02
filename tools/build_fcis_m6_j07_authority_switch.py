"""Build or check the J07 authority-switch vector."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import cast

from experiments.fcis_m6_j07_authority_switch_check import build_payload
from src.state.canonical import canonical_json_bytes

DEFAULT_OUTPUT = Path("docs/research/m6_tasks/TASK_J07_AUTHORITY_SWITCH_V1.json")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = cast(bytes, canonical_json_bytes(build_payload())) + b"\n"
    if args.check:
        if args.output.read_bytes() != payload:
            raise SystemExit("FAIL: J07 authority-switch vector differs from source")
        print("J07_AUTHORITY_SWITCH_VECTOR_MATCH")
        return
    args.output.write_bytes(payload)
    print(args.output)


if __name__ == "__main__":
    main()
