"""Build or check the J08 rollback vector."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import cast

from experiments.fcis_m6_j08_rollback_check import build_payload
from src.state.canonical import canonical_json_bytes

DEFAULT_OUTPUT = Path("docs/research/m6_tasks/TASK_J08_ROLLBACK_V1.json")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = cast(bytes, canonical_json_bytes(build_payload())) + b"\n"
    if args.check:
        if args.output.read_bytes() != payload:
            raise SystemExit("FAIL: J08 rollback vector differs from source")
        print("J08_ROLLBACK_VECTOR_MATCH")
        return
    args.output.write_bytes(payload)
    print(args.output)


if __name__ == "__main__":
    main()
