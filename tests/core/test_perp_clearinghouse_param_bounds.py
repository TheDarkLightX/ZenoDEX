"""Forged-snapshot param-range hardening for the 2p/3p clearinghouse snapshot types.

The 2p/3p snapshot validators previously checked net-zero / conservation / key+type,
but NOT the margin/control param RANGES that the engine validates at set-time
(`perp_engine._CLEARINGHOUSE_CONTROL_PARAM_BOUNDS`). A forged/corrupt snapshot with an
out-of-range param therefore passed the boundary and reached settlement math. The
validators now call `_check_clearinghouse_params`, which checks both the ranges and
the margin-tier ORDERING (max_oracle_move <= maintenance <= initial), mirroring the
kernel ref model's `inv_margin_params_ordered` invariant. The engine enforces both at
set-time (ranges via `_validated_control_params`; ordering via the ref model in
`_ch2p/_ch3p_state_from_dict`), so the snapshot check rejects only already-invalid
configs.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import src.core.perps as P  # noqa: E402
import src.integration.perp_engine as E  # noqa: E402


def _pk(tag: str) -> str:
    return "0x" + tag * 48


def _make_2p(state: dict) -> P.PerpClearinghouse2pMarketState:
    return P.PerpClearinghouse2pMarketState(
        quote_asset="zUSD", account_a_pubkey=_pk("aa"), account_b_pubkey=_pk("bb"), state=state)


def _make_3p(state: dict) -> P.PerpClearinghouse3pTransferMarketState:
    return P.PerpClearinghouse3pTransferMarketState(
        quote_asset="zUSD", account_a_pubkey=_pk("aa"), account_b_pubkey=_pk("bb"),
        account_c_pubkey=_pk("cc"), state=state)


def test_param_bounds_match_engine_drift_guard():
    """The core's clearinghouse param bounds must stay in lock-step with the engine's
    set-time bounds; if they drift, the snapshot validator could reject configs the
    engine accepts (or vice-versa)."""
    assert P.PERP_CLEARINGHOUSE_PARAM_BOUNDS == E._CLEARINGHOUSE_CONTROL_PARAM_BOUNDS


def test_2p_accepts_valid_default_snapshot():
    _make_2p(E._ch2p_init_state_dict())  # must not raise


def test_3p_accepts_valid_default_snapshot():
    _make_3p(E._ch3p_init_state_dict())  # must not raise


@pytest.mark.parametrize("key,bounds", list(P.PERP_CLEARINGHOUSE_PARAM_BOUNDS.items()))
def test_2p_rejects_each_param_below_and_above_range(key, bounds):
    lo, hi = bounds
    for bad in (lo - 1, hi + 1):
        state = dict(E._ch2p_init_state_dict())
        state[key] = bad
        with pytest.raises(ValueError, match="out of range"):
            _make_2p(state)


@pytest.mark.parametrize("key,bounds", list(P.PERP_CLEARINGHOUSE_PARAM_BOUNDS.items()))
def test_3p_rejects_each_param_below_and_above_range(key, bounds):
    lo, hi = bounds
    for bad in (lo - 1, hi + 1):
        state = dict(E._ch3p_init_state_dict())
        state[key] = bad
        with pytest.raises(ValueError, match="out of range"):
            _make_3p(state)


_ORDERING_KEYS = {"max_oracle_move_bps", "maintenance_margin_bps", "initial_margin_bps"}


def test_2p_accepts_non_ordering_param_boundaries():
    """For params NOT in the margin ordering, exact lo/hi are valid (off-by-one safety
    on the range check). The ordering params are covered by the ordering tests below."""
    for key, (lo, hi) in P.PERP_CLEARINGHOUSE_PARAM_BOUNDS.items():
        if key in _ORDERING_KEYS:
            continue
        for good in (lo, hi):
            state = dict(E._ch2p_init_state_dict())
            state[key] = good
            _make_2p(state)  # must not raise


@pytest.mark.parametrize("make,init", [
    (_make_2p, E._ch2p_init_state_dict), (_make_3p, E._ch3p_init_state_dict)])
def test_rejects_invalid_margin_ordering(make, init):
    """The margin-tier ordering (max_oracle_move <= maintenance <= initial) is enforced,
    mirroring the kernel ref model's inv_margin_params_ordered."""
    s = dict(init())
    s["max_oracle_move_bps"] = int(s["maintenance_margin_bps"]) + 1   # max_move > maint
    with pytest.raises(ValueError, match="margin params ordering"):
        make(s)
    s = dict(init())
    s["maintenance_margin_bps"] = int(s["initial_margin_bps"]) + 1    # maint > initial
    with pytest.raises(ValueError, match="margin params ordering"):
        make(s)


def test_snapshot_ordering_matches_engine_rejection():
    """A snapshot the engine rejects for ordering (initial_margin_bps=0, with default
    maintenance > 0) is now also rejected by the snapshot validator -- closing the
    asymmetry where the validator was more permissive than the engine."""
    s = dict(E._ch2p_init_state_dict())
    s["initial_margin_bps"] = 0
    with pytest.raises(ValueError, match="margin params ordering"):
        _make_2p(s)
