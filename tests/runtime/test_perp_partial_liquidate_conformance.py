"""Python/Rust differential for the isolated perps `partial_liquidate` E2 shadow."""

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

from tools.runtime import perp_partial_liquidate_lib as lib  # noqa: E402


def static_cases() -> list[dict]:
    return [
        {"position": 1_000_000, "collateral": 50_000, "fraction_bps": 0, "min_notional_for_bounty": 0},
        {"position": 1_000_000, "collateral": 50_000, "fraction_bps": 10_000, "min_notional_for_bounty": 0},
        {"position": 1_000_000, "collateral": 50_000, "fraction_bps": 2_500, "min_notional_for_bounty": 0},
        {"position": 1_000_000, "collateral": 200_000, "fraction_bps": 0},
        {"position": -1_000_000, "collateral": 50_000, "fraction_bps": 0, "min_notional_for_bounty": 0},
        {"position": 1_000_000, "collateral": 50_000, "fraction_bps": 50_000},
        {"position": 500_000, "collateral": 20_000, "fraction_bps": 0, "min_notional_for_bounty": 100_000_000},
    ]


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.PartialLiquidateShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust partial-liquidate mismatch:\n" + "\n".join(problems[:20])
    return py


def test_rust_matches_python_static(rust_bin):
    py = _assert_agrees(static_cases(), rust_bin)
    # Auto-fraction case partially closes and routes a penalty to the sinks.
    assert py[0]["ok"] and py[0]["liquidated_this_step"]
    assert py[0]["fee_pool_quote"] == py[0]["fee_income"] == py[0]["insurance_balance"] > 0
    # Full close zeroes the position.
    assert py[1]["ok"] and py[1]["position_base"] == 0 and py[1]["entry_price_e8"] == 0
    # Healthy position rejects; out-of-range fraction is a param reject.
    assert py[3]["ok"] is False and py[3]["reason"] == "partial_liquidate_guard"
    assert py[5]["ok"] is False and py[5]["reason"] == "param_domain_fraction_bps"


def test_rust_matches_golden_trace(rust_bin):
    golden = json.loads(
        (_REPO / "tests" / "runtime" / "golden_traces" / "partial_liquidate_smoke.json").read_text()
    )
    proc = subprocess.run(
        [str(rust_bin), "partial-liquidate", "-"],
        input=json.dumps({"cases": golden["cases"]}),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    got = json.loads(proc.stdout)["results"]
    assert got == golden["expected"]


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_rust_matches_python_randomized(rust_bin, seed):
    # 3 x 40 cases driving the real authority: long/short, collateral straddling
    # maintenance margin (liquidatable + healthy), auto/explicit/out-of-range fraction.
    cases = lib.randomized_cases(seed=seed, n=40)
    py = _assert_agrees(cases, rust_bin)
    assert any(p["ok"] for p in py) and any(not p["ok"] for p in py)
