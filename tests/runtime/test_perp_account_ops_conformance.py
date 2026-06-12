"""Python/Rust differential for the isolated perps account-management ops E2 shadow."""

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

from tools.runtime import perp_account_ops_lib as lib  # noqa: E402


def static_cases() -> list[dict]:
    return [
        {"op": "deposit_collateral", "position": 500_000, "collateral": 200_000, "amount": 50_000},
        {"op": "deposit_collateral", "position": 500_000, "collateral": 200_000, "amount": 0},
        {"op": "withdraw_collateral", "position": 500_000, "collateral": 200_000, "amount": 50_000},
        {"op": "withdraw_collateral", "position": 500_000, "collateral": 200_000, "amount": 190_000},
        {"op": "withdraw_collateral", "position": 0, "collateral": 200_000, "amount": 200_000},
        {"op": "set_position", "position": 0, "collateral": 200_000, "new_position_base": 800_000},
        {"op": "set_position", "position": 500_000, "collateral": 10_000, "new_position_base": 1_000_000},
        {"op": "set_position", "position": 0, "collateral": 200_000, "new_position_base": 1_000_001},
        {"op": "set_position", "position": 500_000, "collateral": 200_000, "new_position_base": 600_000, "breaker_active": True},
        {"op": "set_position", "position": 500_000, "collateral": 200_000, "new_position_base": 200_000, "breaker_active": True},
        {"op": "clear_breaker", "position": 0, "collateral": 200_000, "breaker_active": True},
        {"op": "clear_breaker", "position": 0, "collateral": 200_000, "breaker_active": False},
        {"op": "clear_breaker", "position": 500_000, "collateral": 200_000, "breaker_active": True},
    ]


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.AccountOpShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust account-op mismatch:\n" + "\n".join(problems[:20])
    return py


def test_rust_matches_python_static(rust_bin):
    py = _assert_agrees(static_cases(), rust_bin)
    assert py[0]["ok"] and py[0]["collateral_quote"] == 250_000
    assert py[5]["ok"] and py[5]["position_base"] == 800_000 and py[5]["entry_price_e8"] == 100_000_000
    assert py[10]["ok"] and py[10]["breaker_active"] is False
    assert py[1]["reason"] == "param_domain_amount"
    assert py[7]["reason"] == "param_domain_new_position_base"
    assert py[12]["reason"] == "clear_breaker_positions_open"


def test_rust_matches_golden_trace(rust_bin):
    golden = json.loads(
        (_REPO / "tests" / "runtime" / "golden_traces" / "account_op_smoke.json").read_text()
    )
    proc = subprocess.run(
        [str(rust_bin), "account-op", "-"],
        input=json.dumps({"cases": golden["cases"]}),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    got = json.loads(proc.stdout)["results"]
    assert got == golden["expected"]


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_rust_matches_python_randomized(rust_bin, seed):
    # 3 x 40 cases driving the real authority across all four ops, accept + reject.
    cases = lib.randomized_cases(seed=seed, n=40)
    py = _assert_agrees(cases, rust_bin)
    assert any(p["ok"] for p in py) and any(not p["ok"] for p in py)
