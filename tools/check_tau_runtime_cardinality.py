#!/usr/bin/env python3
"""Check runtime-active Tau specs preserve input/output trace cardinality.

Runtime gates and per-step program references need one output row for each input
row. If a Tau expression emits a shortened or extra fixed-point trace, the host
cannot safely align outputs with transactions or state transitions.
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import (  # noqa: E402
    extract_stream_types,
    find_tau_bin,
    normalize_spec_text,
    run_tau_spec_steps,
)


TAU_PROFILES = ("runtime", "latest")
TRACE_SHAPES = ("all-0", "all-max", "alternating", "pulse@0")


@dataclass(frozen=True)
class CardinalityResult:
    spec_path: Path
    profile: str
    shape: str
    expected_rows: int
    ok: bool
    detail: str


def _stream_max(type_name: str) -> int:
    ty = type_name.strip()
    if ty == "sbf":
        return 1
    match = re.fullmatch(r"bv\[(\d+)\]", ty)
    if not match:
        return 1
    width = int(match.group(1))
    if width <= 0:
        return 0
    if width > 64:
        # Keep the cardinality check cheap. Value semantics are tested elsewhere.
        width = 64
    return (1 << width) - 1


def _input_streams(spec_path: Path) -> dict[str, str]:
    spec_text = normalize_spec_text(spec_path.read_text(encoding="utf-8"))
    streams = extract_stream_types(spec_text)
    return {name: ty for name, ty in streams.items() if name.startswith("i")}


def _stress_steps(input_streams: dict[str, str], *, shape: str, rows: int) -> list[dict[str, int]]:
    if rows <= 0:
        raise ValueError("rows must be positive")
    max_by_stream = {name: _stream_max(ty) for name, ty in input_streams.items()}
    steps: list[dict[str, int]] = []
    for idx in range(rows):
        step: dict[str, int] = {}
        for name, max_value in max_by_stream.items():
            if shape == "all-0":
                value = 0
            elif shape == "all-max":
                value = max_value
            elif shape == "alternating":
                value = max_value if idx % 2 else 0
            elif shape == "pulse@0":
                value = max_value if idx == 0 else 0
            else:
                raise ValueError(f"unknown trace shape: {shape}")
            step[name] = value
        steps.append(step)
    return steps


def check_spec_cardinality(
    spec_path: Path,
    *,
    profiles: Iterable[str] = TAU_PROFILES,
    shapes: Iterable[str] = TRACE_SHAPES,
    rows: int = 4,
    repo_root: Path = REPO_ROOT,
) -> list[CardinalityResult]:
    spec_path = spec_path.resolve()
    input_streams = _input_streams(spec_path)
    if not input_streams:
        return [
            CardinalityResult(
                spec_path=spec_path,
                profile="<none>",
                shape="<none>",
                expected_rows=rows,
                ok=False,
                detail="no input streams detected",
            )
        ]

    results: list[CardinalityResult] = []
    for profile in profiles:
        tau_bin = find_tau_bin(repo_root, profile=profile)
        if not tau_bin:
            results.append(
                CardinalityResult(
                    spec_path=spec_path,
                    profile=profile,
                    shape="<missing-tau>",
                    expected_rows=rows,
                    ok=False,
                    detail=f"Tau binary for profile {profile!r} not found",
                )
            )
            continue
        for shape in shapes:
            steps = _stress_steps(input_streams, shape=shape, rows=rows)
            try:
                outputs = run_tau_spec_steps(
                    tau_bin=tau_bin,
                    spec_path=spec_path,
                    steps=steps,
                    timeout_s=90.0,
                )
            except Exception as exc:
                results.append(
                    CardinalityResult(
                        spec_path=spec_path,
                        profile=profile,
                        shape=shape,
                        expected_rows=rows,
                        ok=False,
                        detail=str(exc),
                    )
                )
                continue
            results.append(
                CardinalityResult(
                    spec_path=spec_path,
                    profile=profile,
                    shape=shape,
                    expected_rows=rows,
                    ok=len(outputs) == rows,
                    detail=f"{len(outputs)} output row(s)",
                )
            )
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spec", action="append", required=True, help="Tau spec path to check")
    parser.add_argument("--profile", action="append", choices=TAU_PROFILES, help="Tau profile to run")
    parser.add_argument("--rows", type=int, default=4, help="input rows per stress trace")
    args = parser.parse_args()

    profiles = tuple(args.profile) if args.profile else TAU_PROFILES
    any_failed = False
    for raw_spec in args.spec:
        for result in check_spec_cardinality(Path(raw_spec), profiles=profiles, rows=args.rows):
            status = "OK" if result.ok else "FAIL"
            if not result.ok:
                any_failed = True
            spec_label = result.spec_path.relative_to(REPO_ROOT) if result.spec_path.is_relative_to(REPO_ROOT) else result.spec_path
            print(
                f"{status}\t{spec_label}\t{result.profile}\t{result.shape}\t"
                f"expected={result.expected_rows}\t{result.detail}"
            )
    return 1 if any_failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
