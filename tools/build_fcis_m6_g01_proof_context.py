"""Build or check the source-bound G01 proof-context vector."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.fcis_m6_g01_proof_context_check import build_payload  # noqa: E402
from src.state.canonical import canonical_json_bytes  # noqa: E402

DEFAULT_OUTPUT = Path("docs/research/m6_tasks/TASK_G01_PROOF_CONTEXT_V1.json")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = cast(bytes, canonical_json_bytes(build_payload())) + b"\n"
    if args.check:
        if args.output.read_bytes() != payload:
            raise SystemExit("FAIL: G01 proof-context vector differs from source")
        print("G01_PROOF_CONTEXT_VECTOR_MATCH")
        return
    args.output.write_bytes(payload)
    print(args.output)


if __name__ == "__main__":
    main()
