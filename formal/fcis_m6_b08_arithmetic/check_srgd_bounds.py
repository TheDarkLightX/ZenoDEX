#!/usr/bin/env python3
"""Run the B08 SMT obligations with two independent solvers."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


QUERY_LABELS = (
    "B08_Q1_QW_U256_BOUND",
    "B08_Q2_RESIDUAL_PRODUCT_BOUND",
    "B08_Q3_BASE_BOUND",
    "B08_Q4_ALLOCATION_BOUND",
    "B08_Q5_SCORE_BOUND",
)
_QUERY_MARKER = re.compile(r"^; Q[1-5]:", re.MULTILINE)


def _version(binary: str) -> str:
    completed = subprocess.run(
        [binary, "--version"], capture_output=True, text=True, check=False
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"version command failed for {binary}: exit {completed.returncode}"
        )
    return (completed.stdout or completed.stderr).strip().splitlines()[0]


def _observations(stdout: str) -> list[str]:
    observations: list[str] = []
    for raw_line in stdout.splitlines():
        line = raw_line.strip().strip('"')
        if line in QUERY_LABELS or line in {"sat", "unsat", "unknown"}:
            observations.append(line)
    return observations


def _render_queries(smt_file: Path) -> dict[str, str]:
    source = smt_file.read_text(encoding="utf-8")
    matches = list(_QUERY_MARKER.finditer(source))
    if len(matches) != len(QUERY_LABELS):
        raise RuntimeError(
            f"expected {len(QUERY_LABELS)} query markers, found {len(matches)}"
        )
    prefix = source[: matches[0].start()]
    rendered: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        rendered[QUERY_LABELS[index]] = prefix + source[match.start() : end]
    return rendered


def _run_solver(
    binary: str,
    label: str,
    smt_file: Path,
    timeout_seconds: int,
) -> dict[str, str]:
    command = [binary, str(smt_file)]
    if Path(binary).name == "cvc5":
        command = [binary, "--lang", "smt2", "--incremental", str(smt_file)]
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(
            f"{binary} timed out on {label} after {timeout_seconds}s"
        ) from exc
    if completed.returncode != 0:
        raise RuntimeError(
            f"{binary} failed on {label} with exit {completed.returncode}: "
            f"{completed.stderr.strip()}"
        )
    expected = [label, "unsat"]
    observed = _observations(completed.stdout)
    if observed != expected:
        raise RuntimeError(
            f"{binary} did not discharge {label}; "
            f"expected {expected!r}, observed {observed!r}"
        )
    return {
        "status": "pass",
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--smt-file",
        type=Path,
        default=Path(__file__).with_name("srgd_bounds.smt2"),
    )
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    smt_file = args.smt_file.resolve()
    if not smt_file.is_file():
        raise SystemExit(f"SMT file is missing: {smt_file}")
    if args.timeout_seconds <= 0:
        raise SystemExit("timeout must be positive")

    solver_paths: list[str] = []
    for name in ("z3", "cvc5"):
        path = shutil.which(name)
        if path is None:
            raise SystemExit(f"required solver is unavailable: {name}")
        solver_paths.append(path)

    query_sources = _render_queries(smt_file)
    solver_results: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="fcis-m6-b08-smt-") as temp_dir:
        temp_root = Path(temp_dir)
        for binary in solver_paths:
            query_results: dict[str, object] = {}
            for label, source in query_sources.items():
                query_file = temp_root / f"{label}.smt2"
                query_file.write_text(source, encoding="utf-8")
                query_results[label] = _run_solver(
                    binary, label, query_file, args.timeout_seconds
                )
            solver_results.append(
                {
                    "binary": binary,
                    "version": _version(binary),
                    "status": "pass",
                    "queries": query_results,
                }
            )

    receipt: dict[str, object] = {
        "schema_version": "zenodex.fcis.m6.b08.smt-receipt.v1",
        "smt_file": smt_file.name,
        "smt_sha256": hashlib.sha256(smt_file.read_bytes()).hexdigest(),
        "query_labels": list(QUERY_LABELS),
        "rendered_query_sha256": {
            label: hashlib.sha256(source.encode("utf-8")).hexdigest()
            for label, source in query_sources.items()
        },
        "results": solver_results,
    }
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8")
    sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
