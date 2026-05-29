"""Python/Rust differential for the isolated perps `advance_epoch` E2 shadow."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
for _p in (str(_REPO), str(_REPO / "tools" / "runtime")):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from tools.runtime import perp_advance_epoch_lib as lib  # noqa: E402


def static_cases() -> list[dict]:
    return [
        {"setup": "init", "delta": 1},
        {"setup": "settled", "delta": 1},
        {"setup": "settled", "delta": 10_000},
        {"setup": "unsettled_open", "delta": 1},
        {"setup": "price_published", "delta": 1},
        {"setup": "settled", "delta": 0},
        {"setup": "settled", "delta": 10_001},
    ]


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.AdvanceEpochShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust advance-epoch mismatch:\n" + "\n".join(problems[:20])
    return py


def test_rust_matches_python_static(rust_bin):
    py = _assert_agrees(static_cases(), rust_bin)
    assert any(p["ok"] for p in py) and any(not p["ok"] for p in py)


def test_rust_matches_golden_trace(rust_bin):
    golden = json.loads(
        (_REPO / "tests" / "runtime" / "golden_traces" / "advance_epoch_smoke.json").read_text()
    )
    proc = subprocess.run(
        [str(rust_bin), "advance-epoch", "-"],
        input=json.dumps({"cases": golden["cases"]}),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    got = json.loads(proc.stdout)["results"]
    assert got == golden["expected"]


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_rust_matches_python_randomized(rust_bin, seed):
    # 3 x 40 cases driving the real authority across all four reachable setups,
    # varied deltas (straddling the param-domain), and varied now_epoch.
    cases = lib.randomized_cases(seed=seed, n=40)
    py = _assert_agrees(cases, rust_bin)
    assert any(p["ok"] for p in py), "expected at least one accept in the batch"
    assert any(not p["ok"] for p in py), "expected at least one reject in the batch"
