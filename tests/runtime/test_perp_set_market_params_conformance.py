"""Python/Rust differential for the isolated perps `set_market_params` E2 shadow."""

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

from tools.runtime import perp_set_market_params_lib as lib  # noqa: E402


def static_cases() -> list[dict]:
    pk = "aa" * 48
    return [
        {"params": {}},
        {"params": {"maintenance_margin_bps": 600}},
        {"params": {"maintenance_margin_bps": 9000}},
        {"params": {"depeg_buffer_bps": 6000}},
        {"params": {"max_oracle_move_bps": -1}},
        {"params": {"min_notional_for_bounty": 100}},
        {"params": {"liquidation_penalty_bps": 80}, "positions": [(pk, 500_000)]},
        {"params": {"max_position_abs": 100_000}, "positions": [(pk, 500_000)]},
        {"params": {"funding_cap_bps": 500}},
        {"params": {"initial_margin_bps": 2000, "maintenance_margin_bps": 600}},
    ]


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.SetMarketParamsShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust set-market-params mismatch:\n" + "\n".join(problems[:20])
    return py


def test_rust_matches_python_static(rust_bin):
    py = _assert_agrees(static_cases(), rust_bin)
    assert py[1]["ok"] and py[1]["maintenance_margin_bps"] == 600
    assert py[2]["reason"] == "set_market_params_ordering"
    assert py[3]["reason"] == "set_market_params_param_domain"
    assert py[5]["reason"] == "set_market_params_min_notional"
    assert py[6]["reason"] == "set_market_params_anti_farming"
    assert py[7]["reason"] == "set_market_params_account_unsafe"


def test_rust_matches_golden_trace(rust_bin):
    golden = json.loads(
        (_REPO / "tests" / "runtime" / "golden_traces" / "set_market_params_smoke.json").read_text()
    )
    proc = subprocess.run(
        [str(rust_bin), "set-market-params", "-"],
        input=json.dumps({"cases": golden["cases"]}),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    got = json.loads(proc.stdout)["results"]
    assert got == golden["expected"]


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_rust_matches_python_randomized(rust_bin, seed):
    # 3 x 40 cases driving the real authority: random param overlays (subset of
    # the nine control params, values straddling every bound) with/without an
    # open position, exercising all reject categories + the funding-rate clamp.
    cases = lib.randomized_cases(seed=seed, n=40)
    py = _assert_agrees(cases, rust_bin)
    assert any(p["ok"] for p in py) and any(not p["ok"] for p in py)
