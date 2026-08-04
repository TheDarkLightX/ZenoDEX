"""Build or check the J07 authority-switch vector."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import cast

from experiments.fcis_m6_j07_authority_switch_check import build_payload
from experiments.fcis_m6_tau_j07_writer_authority_check import (
    build_tau_writer_authority_payload_v2,
)
from src.state.canonical import canonical_json_bytes

DEFAULT_OUTPUT = Path("docs/research/m6_tasks/TASK_J07_AUTHORITY_SWITCH_V1.json")
DEFAULT_TAU_WRITER_OUTPUT = Path("docs/research/m6_tasks/TASK_J07_TAU_WRITER_AUTHORITY_V2.json")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--tau-writer-output",
        type=Path,
        default=DEFAULT_TAU_WRITER_OUTPUT,
    )
    args = parser.parse_args()
    payload = cast(bytes, canonical_json_bytes(build_payload())) + b"\n"
    tau_writer_payload = (
        cast(bytes, canonical_json_bytes(build_tau_writer_authority_payload_v2())) + b"\n"
    )
    if args.check:
        if args.output.read_bytes() != payload:
            raise SystemExit("FAIL: J07 authority-switch vector differs from source")
        if args.tau_writer_output.read_bytes() != tau_writer_payload:
            raise SystemExit("FAIL: J07 Tau writer-authority vector differs from source")
        print("J07_AUTHORITY_SWITCH_VECTORS_MATCH")
        return
    args.output.write_bytes(payload)
    args.tau_writer_output.write_bytes(tau_writer_payload)
    print(args.output)
    print(args.tau_writer_output)


if __name__ == "__main__":
    main()
