#!/usr/bin/env python3
"""
Phase 5 shadow replay: run the Rust runtime CLI over a golden trace and verify
it agrees, step-for-step, with the values the authoritative Python runtime
recorded.

The Rust core (``rust-runtime``) is a *shadow* of the Python runtime. This tool
is the gate that keeps them honest: it replays the same transitions through both
and fails loudly on the first disagreement, printing the tx, the Python vs Rust
pre/post state roots, and the first differing field.

Usage::

    python3 tools/runtime/rust_shadow_replay.py tests/runtime/golden_traces/smoke.json

The Rust binary is located via ``$ZENODEX_RUNTIME_BIN`` if set, otherwise built
on demand with ``cargo build`` (use ``--no-build`` to require a prebuilt
binary). Exits non-zero on any divergence.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
RUST_RUNTIME_DIR = _REPO / "rust-runtime"


class ShadowError(RuntimeError):
    """Raised when the shadow runtime cannot be built/run, or it disagrees."""


def cargo_available() -> bool:
    return shutil.which("cargo") is not None


def locate_or_build_cli(*, allow_build: bool = True) -> Path:
    """Return a path to the ``zenodex-runtime`` binary, building it if needed."""
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        p = Path(env_bin)
        if not p.is_file():
            raise ShadowError(f"ZENODEX_RUNTIME_BIN points at a missing file: {p}")
        return p

    if not allow_build:
        for profile in ("release", "debug"):
            candidate = RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
            if candidate.is_file():
                return candidate
        raise ShadowError("no prebuilt zenodex-runtime binary found and --no-build was set")
    if not cargo_available():
        raise ShadowError("cargo not found on PATH; cannot build the Rust shadow runtime")

    # In normal test/review mode, always rebuild. Returning an existing binary
    # can silently compare Python against stale Rust code after a source edit.
    build = subprocess.run(
        ["cargo", "build", "--quiet", "--bin", "zenodex-runtime"],
        cwd=str(RUST_RUNTIME_DIR),
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        raise ShadowError(f"cargo build failed:\n{build.stderr}")
    candidate = RUST_RUNTIME_DIR / "target" / "debug" / "zenodex-runtime"
    if not candidate.is_file():
        raise ShadowError("cargo build succeeded but the binary is missing")
    return candidate


# Trace kernel -> Rust CLI subcommand.
_SUBCOMMAND_BY_KERNEL = {
    "fee_router": "replay-fee-trace",
    "replay_guard": "replay-guard-trace",
}


def _subcommand_for_trace(trace_path: Path) -> str:
    kernel = json.loads(trace_path.read_text(encoding="utf-8")).get("kernel")
    subcommand = _SUBCOMMAND_BY_KERNEL.get(kernel)
    if subcommand is None:
        raise ShadowError(f"no Rust replay subcommand for trace kernel {kernel!r}")
    return subcommand


def run_rust_replay(bin_path: Path, trace_path: Path) -> dict:
    """Run the Rust CLI on ``trace_path`` and return its parsed JSON output.

    The subcommand is chosen from the trace's ``kernel`` field, so this works for
    every runtime surface that has a Rust shadow.
    """
    subcommand = _subcommand_for_trace(trace_path)
    proc = subprocess.run(
        [str(bin_path), subcommand, str(trace_path)],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise ShadowError(f"rust replay exited {proc.returncode}:\n{proc.stderr}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise ShadowError(f"could not parse rust output as JSON: {exc}") from exc


def _python_pre_root(trace: dict, index: int) -> str:
    if index == 0:
        return trace["initial_state_root"]
    return trace["steps"][index - 1]["post_state_root"]


def diff_trace_against_rust(trace: dict, rust: dict) -> list[str]:
    """Return a list of human-readable divergence reports (empty == agreement)."""
    diffs: list[str] = []

    if trace.get("initial_state_root") != rust.get("initial_state_root"):
        diffs.append(
            f"initial_state_root: python={trace.get('initial_state_root')} "
            f"rust={rust.get('initial_state_root')}"
        )
    if trace.get("final_state_root") != rust.get("final_state_root"):
        diffs.append(
            f"final_state_root: python={trace.get('final_state_root')} "
            f"rust={rust.get('final_state_root')}"
        )

    py_steps = trace.get("steps", [])
    rs_results = rust.get("results", [])
    if len(py_steps) != len(rs_results):
        diffs.append(f"step count: python={len(py_steps)} rust={len(rs_results)}")
        return diffs  # cannot align further

    for i, (py, rs) in enumerate(zip(py_steps, rs_results, strict=True)):
        first_field: str | None = None

        py_accept = bool(py.get("expected_accept"))
        if py_accept != bool(rs.get("accept")):
            first_field = first_field or "accept"
        if py.get("expected_reject_reason") != rs.get("reject_reason"):
            first_field = first_field or "reject_reason"
        if py.get("receipt_hash") != rs.get("receipt_hash"):
            first_field = first_field or "receipt_hash"
        if py.get("post_state_root") != rs.get("post_state_root"):
            first_field = first_field or "post_state_root"

        if first_field is not None:
            diffs.append(
                "\n".join(
                    [
                        f"step {i}: first differing field = {first_field}",
                        f"  tx                = {json.dumps(py.get('tx'))}",
                        f"  python pre  root  = {_python_pre_root(trace, i)}",
                        f"  python post root  = {py.get('post_state_root')}",
                        f"  rust   pre  root  = {rs.get('pre_state_root')}",
                        f"  rust   post root  = {rs.get('post_state_root')}",
                        f"  python accept={py_accept} reason={py.get('expected_reject_reason')} "
                        f"receipt={py.get('receipt_hash')}",
                        f"  rust   accept={rs.get('accept')} reason={rs.get('reject_reason')} "
                        f"receipt={rs.get('receipt_hash')}",
                    ]
                )
            )

    return diffs


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Replay a golden trace through the Rust shadow.")
    parser.add_argument("trace", help="path to a golden trace JSON file")
    parser.add_argument(
        "--no-build", action="store_true", help="require a prebuilt binary (do not run cargo build)"
    )
    args = parser.parse_args(argv)

    trace_path = Path(args.trace)
    if not trace_path.is_file():
        print(f"error: trace not found: {trace_path}", file=sys.stderr)
        return 2

    trace = json.loads(trace_path.read_text(encoding="utf-8"))

    try:
        bin_path = locate_or_build_cli(allow_build=not args.no_build)
        rust = run_rust_replay(bin_path, trace_path)
    except ShadowError as exc:
        print(f"SHADOW ERROR: {exc}", file=sys.stderr)
        return 2

    diffs = diff_trace_against_rust(trace, rust)
    if diffs:
        print("SHADOW DIVERGENCE (Rust disagrees with Python):", file=sys.stderr)
        for d in diffs:
            print(d, file=sys.stderr)
        return 1

    n = len(trace.get("steps", []))
    print(f"SHADOW OK: Rust agrees with Python on all {n} steps of {trace_path}")
    print(f"  final_state_root = {trace.get('final_state_root')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
