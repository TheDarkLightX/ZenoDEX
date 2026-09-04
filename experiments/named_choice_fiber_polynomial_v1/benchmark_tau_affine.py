#!/usr/bin/env python3
"""Single-host timing observation for bounded Tau affine interval queries."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
VERDICT = re.compile(r"%\d+\s*:\s*([TF])")


def _hex16(value: int) -> str:
    return f"{{ #x{value:04X} }}:bv[16]"


def _program(number_of_signs: int) -> str:
    center = 1024
    quantifiers = " ".join(f"all s{index}:bv[16]" for index in range(number_of_signs))
    guards = " && ".join(
        f"(s{index} = {_hex16(0)} || s{index} = {_hex16(1)})" for index in range(number_of_signs)
    )
    terms = " + ".join(f"s{index} * {_hex16(2)}" for index in range(number_of_signs))
    value = f"{_hex16(center - number_of_signs)} + {terms}"
    return (
        "set charvar off\n"
        "set maxsplits 1\n"
        f"n {quantifiers} (({guards}) -> "
        f"(({value}) >= {_hex16(center - number_of_signs)} && "
        f"({value}) <= {_hex16(center + number_of_signs)}))\n"
        "q\n"
    )


def _arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tau-bin", required=True, type=Path)
    parser.add_argument("--sizes", default="1,2,4,8")
    parser.add_argument("--timeout-seconds", default=4.0, type=float)
    return parser.parse_args()


def main() -> int:
    args = _arguments()
    sizes = tuple(int(item) for item in args.sizes.split(","))
    if not sizes or any(size <= 0 or size > 15 for size in sizes):
        raise SystemExit("INVALID_SIZE_PROFILE")
    rows: list[dict[str, object]] = []
    for size in sizes:
        source = _program(size)
        started = time.perf_counter()
        try:
            completed = subprocess.run(
                [str(args.tau_bin), "-q"],
                input=source,
                capture_output=True,
                text=True,
                timeout=args.timeout_seconds,
                check=False,
            )
        except subprocess.TimeoutExpired:
            rows.append(
                {
                    "explicit_assignments": 1 << size,
                    "named_signs": size,
                    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                    "verdict": "TIMEOUT_FAIL_CLOSED",
                }
            )
            continue
        elapsed = time.perf_counter() - started
        combined = ANSI.sub("", completed.stdout + completed.stderr)
        verdicts = VERDICT.findall(combined)
        if completed.returncode != 0 or verdicts != ["T"]:
            raise SystemExit(f"TAU_QUERY_FAILURE:size={size}:verdicts={verdicts}")
        rows.append(
            {
                "elapsed_seconds": round(elapsed, 6),
                "explicit_assignments": 1 << size,
                "named_signs": size,
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "verdict": "T",
            }
        )
    print(
        json.dumps(
            {
                "authority": "NONE",
                "claim_status": "SINGLE_HOST_TIMING_OBSERVATION_ONLY",
                "nonclaims": [
                    "not Tau Net throughput",
                    "not asymptotic complexity",
                    "not evidence for arbitrary nonlinear circuits",
                ],
                "rows": rows,
                "schema": "zenodex.choice_fiber_tau_timing.v1",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
