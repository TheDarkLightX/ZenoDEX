"""Fee-router conservation invariant must fail closed on the authority path.

The conservation invariant (amount + dust_in == buyburn + stakers + reserve +
hosts + dust_out) was previously guarded only by a bare `assert` in the
`apply_step` golden-trace wrapper. A bare `assert` is stripped under `python -O`,
so an optimized production run would not enforce it (fail open), and the
production authority path (`_route_fee_python`) did not check it at all.

These tests pin the fix: the invariant is now enforced fail-closed on the
authority path and survives `-O`.
"""

from __future__ import annotations

import pathlib
import subprocess
import sys
import textwrap

import pytest

import src.core.fee_router as fee_router
from src.core.fee_router import (
    FeeAccumulator,
    FeeRouterConservationError,
    FeeSplitTable,
    RouteAccepted,
    apply_step,
    route_fee,
)
from src.runtime.authority import reset_active_authority_policy

_ROOT = str(pathlib.Path(__file__).resolve().parents[2])
_ASSET = "0x" + "11" * 32


def _valid_split() -> FeeSplitTable:
    # buyburn floor for dex/perps is 5000 bps; this split sums to 10000.
    return FeeSplitTable(buyburn_bps=6000, stakers_bps=2000, reserve_bps=1000, hosts_bps=1000)


def test_conservation_holds_on_real_route():
    reset_active_authority_policy()  # python_authority
    result = route_fee(
        source="dex", asset=_ASSET, amount=12345, split_table=_valid_split(), accumulator=FeeAccumulator()
    )
    assert isinstance(result, RouteAccepted)
    r = result.receipt
    assert 12345 + 0 == r.buyburn + r.stakers + r.reserve + r.hosts + r.dust


def test_authority_path_fails_closed_on_conservation_violation(monkeypatch):
    # Simulate a routing/accumulator corruption by forcing the conservation
    # predicate false; the authority path must raise (not silently commit).
    reset_active_authority_policy()
    monkeypatch.setattr(fee_router, "_conservation_holds", lambda *a, **k: False)
    with pytest.raises(FeeRouterConservationError):
        route_fee(
            source="dex", asset=_ASSET, amount=12345, split_table=_valid_split(), accumulator=FeeAccumulator()
        )


def test_apply_step_fails_closed_on_conservation_violation(monkeypatch):
    reset_active_authority_policy()
    monkeypatch.setattr(fee_router, "_conservation_holds", lambda *a, **k: False)
    with pytest.raises(FeeRouterConservationError):
        apply_step(FeeAccumulator(), source="dex", asset=_ASSET, amount=12345, split_table=_valid_split())


def test_conservation_guard_survives_python_O_optimize():
    # Under `python -O`, a bare `assert` is stripped; the fail-closed `if/raise`
    # must still fire. Run in a subprocess with -O, forcing the predicate false.
    snippet = textwrap.dedent(
        f"""
        import sys
        sys.path.insert(0, {_ROOT!r})
        import src.core.fee_router as fr
        from src.runtime.authority import reset_active_authority_policy
        reset_active_authority_policy()
        fr._conservation_holds = lambda *a, **k: False  # simulate corruption
        st = fr.FeeSplitTable(buyburn_bps=6000, stakers_bps=2000, reserve_bps=1000, hosts_bps=1000)
        try:
            fr.apply_step(fr.FeeAccumulator(), source="dex", asset="0x" + "11" * 32, amount=12345, split_table=st)
        except fr.FeeRouterConservationError:
            print("RAISED")
            sys.exit(0)
        print("NO_RAISE")
        sys.exit(1)
        """
    )
    proc = subprocess.run([sys.executable, "-O", "-c", snippet], capture_output=True, text=True)
    assert proc.returncode == 0, (
        f"conservation guard failed to fire under python -O (fail-open): "
        f"stdout={proc.stdout!r} stderr={proc.stderr!r}"
    )
