"""Python/Rust differential for the isolated perps `publish_clearing_price` E2 shadow."""

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

from tools.runtime import perp_publish_clearing_price_lib as lib  # noqa: E402


def static_cases() -> list[dict]:
    return [
        {"setup": "unsettled_open", "price_e8": 100_000_000},
        {"setup": "unsettled_open", "price_e8": 1},
        {"setup": "unsettled_open", "price_e8": 1_000_000_000_000},
        {"setup": "unsettled_open", "price_e8": 0},
        {"setup": "unsettled_open", "price_e8": -1},
        {"setup": "unsettled_open", "price_e8": 1_000_000_000_001},
        {"setup": "init", "price_e8": 100_000_000},
        {"setup": "price_published", "price_e8": 100_000_000},
        {"setup": "settled", "price_e8": 100_000_000},
        {"setup": "open_deep", "price_e8": 100_000_000},
        {"setup": "open_deep", "cycles": 2, "price_e8": 999_999_999_999},
    ]


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.PublishClearingPriceShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust publish-clearing-price mismatch:\n" + "\n".join(problems[:20])
    return py


def test_rust_matches_python_static(rust_bin):
    py = _assert_agrees(static_cases(), rust_bin)
    assert any(p["ok"] for p in py) and any(not p["ok"] for p in py)


def test_rust_matches_golden_trace(rust_bin):
    golden = json.loads(
        (_REPO / "tests" / "runtime" / "golden_traces" / "publish_clearing_price_smoke.json").read_text()
    )
    proc = subprocess.run(
        [str(rust_bin), "publish-clearing-price", "-"],
        input=json.dumps({"cases": golden["cases"]}),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    got = json.loads(proc.stdout)["results"]
    assert got == golden["expected"]


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_rust_matches_python_randomized(rust_bin, seed):
    # 3 x 40 cases driving the real authority across all reachable setups,
    # prices straddling the param-domain, and varied now_epoch.
    cases = lib.randomized_cases(seed=seed, n=40)
    py = _assert_agrees(cases, rust_bin)
    assert any(p["ok"] for p in py), "expected at least one accept in the batch"
    assert any(not p["ok"] for p in py), "expected at least one reject in the batch"
