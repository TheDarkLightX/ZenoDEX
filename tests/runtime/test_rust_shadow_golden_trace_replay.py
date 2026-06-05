"""Rust-shadow replay over every supported committed golden trace.

The per-surface conformance suites exercise deeper randomized corpora. This file
pins the generic golden-trace replay lane itself: a fresh Rust CLI build must
agree with the committed Python trace outputs for every trace whose kernel has a
Rust replay subcommand.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE_DIR = REPO / "tests" / "runtime" / "golden_traces"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from rust_shadow_replay import (  # noqa: E402
    _SUBCOMMAND_BY_KERNEL,
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)

SUPPORTED_TRACE_NAMES = (
    "smoke.json",
    "replay_guard_smoke.json",
    "balance_smoke.json",
    "zusd_smoke.json",
    "burn_smoke.json",
    "cpmm_smoke.json",
    "liquidity_smoke.json",
)


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _load_trace(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_supported_trace_list_covers_committed_supported_traces() -> None:
    expected = {
        p.name
        for p in TRACE_DIR.glob("*.json")
        if _load_trace(p).get("kernel") in _SUBCOMMAND_BY_KERNEL
    }
    assert set(SUPPORTED_TRACE_NAMES) == expected


@pytest.mark.parametrize("trace_name", SUPPORTED_TRACE_NAMES)
def test_rust_shadow_replays_committed_golden_trace(rust_bin: Path, trace_name: str) -> None:
    trace_path = TRACE_DIR / trace_name
    trace = _load_trace(trace_path)
    rust = run_rust_replay(rust_bin, trace_path)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)
