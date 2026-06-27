"""Tests for the promoted N-party net-zero clearinghouse core + market state.

Promoted from `experiments/perp_np_clearinghouse_v1` (semantics machine-checked
there: ESSO z3+cvc5, Lean 0-sorry, Kani, hypothesis property tests). These tests
lock the promotion into the live `src/core` and exercise 3+ INDEPENDENT wallets —
the participation the fixed 2-party clearinghouse cannot provide.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import src.core.perp_np_clearinghouse as C  # noqa: E402
import src.core.perps as P  # noqa: E402
from src.core.perp_np_matching import (  # noqa: E402
    E8,
    Intent,
    ration_net_zero,
)
from src.core.perps import (  # noqa: E402
    PerpClearinghouseNpAccount,
    PerpClearinghouseNpMarketState,
)


def _pk(byte: str) -> str:
    return "0x" + byte * 48


def _global_state(net_deposited_e8: int, *, fee=0, ins=0, ins_ext=0, claims=0) -> dict:
    return {
        "now_epoch": 0, "index_price_e8": 100 * E8, "fee_pool_e8": fee,
        "insurance_e8": ins, "insurance_ext_e8": ins_ext, "claims_paid_e8": claims,
        "net_deposited_e8": net_deposited_e8, "initial_margin_bps": 1000,
        "maintenance_margin_bps": 500, "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50, "max_oracle_move_bps": 500,
        "funding_cap_bps": 100, "max_position_abs": 1_000_000,
        "min_notional_for_bounty_e8": 100 * E8,
    }


# --- pure core: matcher + N-party epoch -------------------------------------
def test_matcher_emits_net_zero_three_sides():
    out = ration_net_zero([10, -6, -4])
    assert sum(out) == 0
    assert out == [10, -6, -4]


def test_three_independent_wallets_match_net_zero():
    m = C.init_market(100 * E8)
    for pk in ("aa", "bb", "cc"):
        m = C.deposit(m, pk, 10 ** 15)
    intents = [
        Intent("aa", target_base=10, nonce=1),   # long
        Intent("bb", target_base=-6, nonce=1),   # short
        Intent("cc", target_base=-4, nonce=1),   # short
    ]
    m2, res = C.apply_match(m, intents)
    assert res.net == 0
    assert {a.pubkey: a.position_base for a in m2.accounts} == {"aa": 10, "bb": -6, "cc": -4}
    assert C.net_position(m2) == 0
    assert C.check_invariants(m2) == []


def test_run_epoch_settles_zero_sum_against_index():
    m = C.init_market(100 * E8)
    for pk in ("aa", "bb", "cc"):
        m = C.deposit(m, pk, 10 ** 15)
    m, _ = C.apply_match(m, [
        Intent("aa", target_base=10, nonce=1),
        Intent("bb", target_base=-6, nonce=1),
        Intent("cc", target_base=-4, nonce=1),
    ])
    before = C.total_collateral_e8(m)
    # Settle the book at a moved (within-clamp) price; MTM is exactly zero-sum.
    m2, _ = C.run_epoch(m, clearing_price_e8=104 * E8, funding_rate_bps=0, intents=[])
    assert C.net_position(m2) == 0
    assert C.total_collateral_e8(m2) == before          # zero-sum MTM, no funding
    assert m2.index_price_e8 == 104 * E8                # index advanced to settle price
    assert m2.now_epoch == m.now_epoch + 1
    assert C.check_invariants(m2) == []


def test_matcher_rations_heavy_side_largest_remainder():
    # 1 buyer (+7) vs 3 sellers (-3,-3,-3): matched volume 7 of 9 sell, lex tie-break.
    out = ration_net_zero([7, -3, -3, -3])
    assert sum(out) == 0
    assert out[0] == 7
    assert sorted(out[1:]) == [-3, -2, -2]              # 7 rationed across 3 by largest remainder


# --- persistent market state type (snapshot-grade, fail-closed) -------------
def test_state_type_valid_three_party_market():
    accts = (
        PerpClearinghouseNpAccount(_pk("11"), 10, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("22"), -6, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("33"), -4, 100 * E8, 10 ** 15),
    )
    m = PerpClearinghouseNpMarketState(
        quote_asset="zUSD", global_state=_global_state(3 * 10 ** 15), accounts=accts)
    assert len(m.accounts) == 3
    assert m.role_for_pubkey(_pk("22")) == _pk("22")    # member resolves own account
    assert m.role_for_pubkey(_pk("99")) is None         # non-member: no observer trap


def test_pubkey_bytes48_or_none_handles_expected_canonicalization_rejects():
    assert P._pubkey_bytes48_or_none("not-hex") is None
    assert P._pubkey_bytes48_or_none(123) is None  # type: ignore[arg-type]


def test_pubkey_bytes48_or_none_does_not_mask_internal_errors(monkeypatch: pytest.MonkeyPatch):
    def broken(_pubkey: str, *, name: str) -> bytes:
        raise RuntimeError(f"internal pubkey fault: {name}")

    monkeypatch.setattr(P, "_pubkey_bytes48", broken)

    with pytest.raises(RuntimeError, match="internal pubkey fault: pubkey"):
        P._pubkey_bytes48_or_none(_pk("11"))


def test_state_type_rejects_net_zero_violation():
    accts = (
        PerpClearinghouseNpAccount(_pk("11"), 10, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("22"), -6, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("33"), -3, 100 * E8, 10 ** 15),  # sums to +1
    )
    with pytest.raises(ValueError, match="sum.position_base. == 0"):
        PerpClearinghouseNpMarketState(
            quote_asset="zUSD", global_state=_global_state(3 * 10 ** 15), accounts=accts)


def test_state_type_rejects_conservation_violation():
    accts = (
        PerpClearinghouseNpAccount(_pk("11"), 10, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("22"), -6, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("33"), -4, 100 * E8, 10 ** 15),
    )
    with pytest.raises(ValueError, match="net_deposited_e8 . insurance_ext_e8"):
        PerpClearinghouseNpMarketState(
            quote_asset="zUSD", global_state=_global_state(999), accounts=accts)


def test_state_type_rejects_negative_np_snapshot_counters():
    gs = _global_state(1, ins=1, claims=-1)
    with pytest.raises(ValueError, match="claims_paid_e8.*non-negative"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())

    gs = _global_state(0)
    gs["now_epoch"] = -1
    with pytest.raises(ValueError, match="now_epoch.*non-negative"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())


def test_state_type_rejects_np_param_values_outside_engine_bounds():
    gs = _global_state(0)
    gs["funding_cap_bps"] = 0
    with pytest.raises(ValueError, match="funding_cap_bps.*out of range"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())

    gs = _global_state(0)
    gs["max_position_abs"] = 0
    with pytest.raises(ValueError, match="max_position_abs.*out of range"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())


def test_state_type_rejects_invalid_margin_params_ordering():
    """The Np snapshot type must reject margin-tier orderings that the isolated_v2
    market already forbids: max_oracle_move <= maintenance+depeg <= initial_margin.
    Per-key range bounds permit each value individually; only the ordering check
    rejects the dangerous RELATIONSHIP (which would make single-epoch bad-debt
    reachable). Fail-closed at the boundary -- also guards forged snapshots."""
    # max_oracle_move (700) > maintenance+depeg (600): a clamped move could outrun
    # the maintenance buffer, so liquidation could miss bad-debt. Must reject.
    gs = _global_state(0)
    gs["max_oracle_move_bps"] = 700
    with pytest.raises(ValueError, match="margin params ordering"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())

    # maintenance+depeg (600) > initial_margin (550): liquidation threshold above the
    # entry-margin floor. Must reject.
    gs = _global_state(0)
    gs["initial_margin_bps"] = 550
    with pytest.raises(ValueError, match="margin params ordering"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())


def test_state_type_rejects_penalty_at_or_above_maintenance_buffer():
    """liquidation_penalty_bps must be strictly below maintenance+depeg, else the
    penalty alone could drive a just-liquidatable account underwater."""
    gs = _global_state(0)
    gs["liquidation_penalty_bps"] = 600          # == maintenance(500)+depeg(100)
    with pytest.raises(ValueError, match="liquidation_penalty_bps"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())


def test_state_type_rejects_unfunded_liquidation_after_oracle_move():
    gs = _global_state(0)
    gs["max_oracle_move_bps"] = 548
    with pytest.raises(ValueError, match="funded liquidation"):
        PerpClearinghouseNpMarketState(quote_asset="zUSD", global_state=gs, accounts=())


def test_state_type_accepts_valid_margin_safety_boundary():
    """A tight but funded boundary remains valid: maint+depeg == initial_margin and
    liquidation penalty is still collectible after the configured oracle move."""
    gs = _global_state(3 * 10 ** 15)
    gs["max_oracle_move_bps"] = 500
    gs["initial_margin_bps"] = 600               # == maintenance+depeg
    gs["liquidation_penalty_bps"] = 95
    accts = (
        PerpClearinghouseNpAccount(_pk("11"), 10, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("22"), -6, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("33"), -4, 100 * E8, 10 ** 15),
    )
    m = PerpClearinghouseNpMarketState(
        quote_asset="zUSD", global_state=gs, accounts=accts)
    assert len(m.accounts) == 3


def test_init_market_rejects_unfunded_liquidation_params():
    with pytest.raises(ValueError, match="funded liquidation"):
        C.init_market(100 * E8, C.MarketParams(max_oracle_move_bps=548))


def test_init_market_rejects_bool_market_params():
    with pytest.raises(TypeError, match="plain int"):
        C.init_market(100 * E8, C.MarketParams(max_oracle_move_bps=True))


def test_state_type_rejects_duplicate_members():
    accts = (
        PerpClearinghouseNpAccount(_pk("11"), 10, 100 * E8, 10 ** 15),
        PerpClearinghouseNpAccount(_pk("11"), -10, 100 * E8, 10 ** 15),  # duplicate pubkey
    )
    with pytest.raises(ValueError, match="distinct"):
        PerpClearinghouseNpMarketState(
            quote_asset="zUSD", global_state=_global_state(2 * 10 ** 15), accounts=accts)
