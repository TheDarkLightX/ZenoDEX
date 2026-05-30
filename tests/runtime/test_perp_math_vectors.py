"""Cross-language vectors for the perp stateless math (Phase E1).

Proves the Rust `perp-math` ops agree byte-for-byte with the authoritative
`src/core/perp_v2/math.py` — the parity-critical surface because perp values are
signed and the magnitude/sign split must match exactly. Also asserts the
authority's own sign-symmetry invariants and the Rust bridge's domain rejection.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.core.perp_v2 import math as m
from tools.runtime import perp_math_lib as lib

P = m.PRICE_SCALE


# --- Python authority: sign symmetry (no Rust) --------------------------------


def test_pnl_sign_symmetry():
    long = m._pnl_quote_python(1000, 110 * P, 100 * P)
    short = m._pnl_quote_python(-1000, 110 * P, 100 * P)
    assert long > 0 and short < 0 and long == -short


def test_funding_sign_symmetry():
    longp = m._funding_payment_python(1000, 100 * P, 50)
    shortp = m._funding_payment_python(-1000, 100 * P, 50)
    assert longp > 0 and shortp < 0 and longp == -shortp


def test_settle_price_clamp_band_nonzero():
    # index*move < BPS_SCALE -> floor delta is 0, ceil-div keeps the band open.
    p = m._settle_price_python(1_000_000, 100, 1, True)
    assert p != 100


# --- Rust/Python differential -------------------------------------------------


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.PerpMathShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, cases)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust perp-math mismatch:\n" + "\n".join(problems[:20])


def test_rust_matches_python_static(rust_bin):
    _assert_agrees(lib.static_cases(), rust_bin)


@pytest.mark.parametrize("seed", [1, 9, 77, 20260529])
def test_rust_matches_python_randomized(rust_bin, seed):
    _assert_agrees(lib.random_cases(seed=seed, n=500), rust_bin)


def test_rust_rejects_out_of_domain(rust_bin):
    # The Python authority is unbounded; the Rust bridge fails closed on inputs
    # outside its safe i128 product domain. (Rust-only assertion.)
    cases = [
        {"op": "notional_quote", "position_base": 10 ** 30, "price_e8": 100 * P},
        {"op": "maint_margin_req", "position_base": 1000, "price_e8": 100 * P,
         "maint_bps": 10 ** 9, "depeg_bps": 0},
    ]
    rs = lib.run_rust(rust_bin, cases)
    assert all(not r["ok"] and r["code"] == "out_of_domain" for r in rs), rs


def test_rust_rejects_i128_min_without_panicking(rust_bin):
    min_i128 = -(2**127)
    cases = [
        {"op": "notional_quote", "position_base": min_i128, "price_e8": 100 * P},
    ]
    rs = lib.run_rust(rust_bin, cases)
    assert rs == [{"index": 0, "ok": False, "code": "out_of_domain"}]
