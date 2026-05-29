"""Python/Rust differential for the isolated perps `settle_epoch` E2 shadow."""

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

from tools.runtime import perp_settle_epoch_lib as lib  # noqa: E402


def static_cases() -> list[dict]:
    a = "aa" * 48
    return [
        {"positions": [], "clearing_price_e8": 100_000_000},
        {"positions": [(a, 1_000_000)], "clearing_price_e8": 100_000_000},   # no move
        {"positions": [(a, 1_000_000)], "clearing_price_e8": 101_000_000},   # +1% long profit
        {"positions": [(a, 1_000_000)], "clearing_price_e8": 99_000_000},    # -1% long loss
        {"positions": [(a, -1_000_000)], "clearing_price_e8": 104_000_000},  # short loss
        {"positions": [(a, 1_000_000)], "clearing_price_e8": 50_000_000, "deposit": 105_000},  # liquidation (clamped)
        {"positions": [(a, 1_000_000)], "clearing_price_e8": 150_000_000},   # +50% -> clamp + breaker
        {
            "positions": [("12" * 48, 500_000), ("34" * 48, -700_000)],
            "clearing_price_e8": 98_000_000,
        },
        # Settle twice: the second settle runs on a Settled state -> guard reject.
        {"positions": [("aa" * 48, 1_000_000)], "clearing_price_e8": 100_000_000, "double_settle": True},
    ]


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.SettleEpochShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, py)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust settle-epoch mismatch:\n" + "\n".join(problems[:20])
    return py


def test_rust_matches_python_static(rust_bin):
    py = _assert_agrees(static_cases(), rust_bin)
    # Cases 0-7 accept; case 8 (double_settle) rejects on the second settle.
    assert all(p["ok"] for p in py[:8]), "first 8 static settle cases should accept"
    assert py[8]["ok"] is False and py[8]["reason"] == "settle_epoch_guard"
    # The liquidation case must actually liquidate its account.
    liq = py[5]["accounts"][("aa" * 48)]
    assert liq[1] == 0 and liq[3] is True, "expected position->0 and liquidated flag"


def test_rust_matches_golden_trace(rust_bin):
    golden = json.loads(
        (_REPO / "tests" / "runtime" / "golden_traces" / "settle_epoch_smoke.json").read_text()
    )
    proc = subprocess.run(
        [str(rust_bin), "settle-epoch", "-"],
        input=json.dumps({"cases": golden["cases"]}),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    got = json.loads(proc.stdout)["results"]
    assert got == golden["expected"]


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_rust_matches_python_randomized(rust_bin, seed):
    # 3 x 40 multi-account cases driving the real authority: varied positions,
    # clearing prices straddling the oracle band (PnL + clamp/breaker), deposits.
    cases = lib.randomized_cases(seed=seed, n=40)
    py = _assert_agrees(cases, rust_bin)
    assert any(p["ok"] for p in py), "expected at least one accept in the batch"
