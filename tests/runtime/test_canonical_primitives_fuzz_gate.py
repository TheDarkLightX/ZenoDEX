"""Deterministic fuzz gate for Rust authority promotion of canonical primitives."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from tools.runtime import canonical_primitives_lib as lib  # noqa: E402


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.CanonicalShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def test_canonical_primitives_fuzz_gate_agrees(rust_bin):
    """Fuzz JSON, domain-separated hashes, and fixed hex across Python/Rust."""

    seeds = (3, 11, 29, 101, 20260530, 8675309)
    all_cases: list[dict] = []
    for seed in seeds:
        all_cases.extend(lib.random_cases(seed=seed, n=300))

    py = lib.py_eval_all(all_cases)
    rs = lib.run_rust(rust_bin, all_cases)
    problems = lib.diff_results(py, rs)

    assert len(all_cases) == 1_800
    assert any(c.get("op") == "domain_json_hash" for c in all_cases)
    assert sum(1 for r in py if r["ok"]) > 500
    assert sum(1 for r in py if not r["ok"]) > 100
    assert not problems, "Python/Rust canonical fuzz mismatch:\n" + "\n".join(problems[:20])


def test_canonical_primitives_fuzz_is_deterministic():
    assert lib.random_cases(seed=20260530, n=50) == lib.random_cases(seed=20260530, n=50)
