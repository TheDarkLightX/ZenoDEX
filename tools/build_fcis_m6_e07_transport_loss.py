"""Build or check the source-bound E07 transport-loss vector."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from experiments.fcis_m6_e07_transport_loss_check import build_payload  # noqa: E402
from src.state.canonical import canonical_json_bytes  # noqa: E402

DEFAULT_OUTPUT = Path("docs/research/m6_tasks/TASK_E07_TRANSPORT_LOSS_V1.json")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = build_payload()
    if args.check:
        if canonical_json_bytes(payload) + b"\n" != args.output.read_bytes():
            raise SystemExit("FAIL: E07 vector differs from the checked-in source")
        print("E07_TRANSPORT_LOSS_VECTOR_MATCH")
        return
    args.output.write_bytes(canonical_json_bytes(payload) + b"\n")
    print(args.output)


if __name__ == "__main__":
    main()
