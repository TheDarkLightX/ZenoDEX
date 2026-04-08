from __future__ import annotations

from src.core.zusd import (
    E8,
    ZUSDCommand,
    ZUSDState,
    check_invariants,
    in_recovery_mode,
    init_state,
    step,
)


def _ok(s: ZUSDState, tag: str, **kwargs) -> ZUSDState:
    r = step(s, ZUSDCommand(tag=tag, args=kwargs))
    assert r.ok, r.error
    assert r.state is not None
    return r.state


def _bootstrap(s: ZUSDState, *, price_e8: int = 100 * E8) -> ZUSDState:
    return _ok(s, "bootstrap_oracle", price_e8=price_e8, auth_ok=True)


def test_basic_mint_repay_and_conservation() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=100 * E8)
    s = _ok(s, "deposit_sp", amount_e8=40 * E8)
    s = _ok(s, "repay_zusd", amount_e8=20 * E8)

    assert s.debt_e8 == 80 * E8
    assert s.free_debt_e8 == 40 * E8
    assert s.sp_debt_e8 == 40 * E8
    assert check_invariants(s) == []


def test_pending_price_freezes_risky_ops() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=100 * E8)
    s = _ok(s, "oracle_report", price_e8=80 * E8, auth_ok=True)

    r_mint = step(s, ZUSDCommand(tag="mint_zusd", args={"amount_e8": 1 * E8}))
    assert not r_mint.ok
    assert "freeze" in (r_mint.error or "")

    r_withdraw = step(s, ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": 1}))
    assert not r_withdraw.ok
    assert "freeze" in (r_withdraw.error or "")


def test_oracle_commit_requires_mcr_at_pending_price() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=150 * E8)
    s = _ok(s, "oracle_report", price_e8=50 * E8, auth_ok=True)

    r = step(s, ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}))
    assert not r.ok
    assert "below MCR" in (r.error or "")


def test_recovery_mode_blocks_mint_and_withdraw() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=120 * E8)
    s = _ok(s, "oracle_report", price_e8=75 * E8, auth_ok=True)
    s = _ok(s, "oracle_commit", auth_ok=True)

    assert in_recovery_mode(s) is True

    r_mint = step(s, ZUSDCommand(tag="mint_zusd", args={"amount_e8": 1 * E8}))
    assert not r_mint.ok
    assert "recovery mode" in (r_mint.error or "")

    r_withdraw = step(s, ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": 1}))
    assert not r_withdraw.ok
    assert "recovery mode" in (r_withdraw.error or "")


def test_liquidation_under_pending_price_moves_debt_to_sp() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=150 * E8)
    s = _ok(s, "deposit_sp", amount_e8=150 * E8)
    s = _ok(s, "oracle_report", price_e8=70 * E8, auth_ok=True)

    r = step(s, ZUSDCommand(tag="liquidate", args={}))
    assert r.ok, r.error
    assert r.state is not None
    ns = r.state
    assert ns.debt_e8 == 0
    assert ns.collateral_e8 == 0
    assert ns.sp_debt_e8 == 0
    assert ns.sp_coll_e8 == 2 * E8


def test_repay_cannot_exceed_free_debt_balance() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", amount_e8=100 * E8)
    s = _ok(s, "deposit_sp", amount_e8=40 * E8)

    r = step(s, ZUSDCommand(tag="repay_zusd", args={"amount_e8": 80 * E8}))
    assert not r.ok
    assert "free debt" in (r.error or "")


def test_invariant_detection_for_supply_conservation() -> None:
    bad = ZUSDState(
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        debt_e8=10 * E8,
        free_debt_e8=9 * E8,
        sp_debt_e8=0,
        collateral_e8=20 * E8,
    )
    violations = check_invariants(bad)
    assert "inv_supply_conservation" in violations


def test_borrow_fee_adds_debt_and_tracks_protocol_revenue() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = ZUSDState(
        **{
            **s.__dict__,
            "borrow_fee_floor_bps": 100,
            "borrow_fee_max_bps": 100,
        }
    )
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    r = step(s, ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.effects is not None
    ns = r.state

    assert ns.debt_e8 == 101 * E8
    assert ns.free_debt_e8 == 101 * E8
    assert ns.protocol_revenue_zusd_cum_e8 == 1 * E8
    assert r.effects["mint_fee_bps"] == 100
    assert r.effects["mint_fee_e8"] == 1 * E8
    assert check_invariants(ns) == []


def test_redemption_burns_debt_and_moves_collateral_fee_to_protocol() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = ZUSDState(
        **{
            **s.__dict__,
            "redemption_fee_floor_bps": 200,
            "redemption_fee_max_bps": 200,
        }
    )
    s = _ok(s, "deposit_collateral", amount_e8=5 * E8)
    s = _ok(s, "mint_zusd", amount_e8=200 * E8)
    r = step(s, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 100 * E8}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.effects is not None
    ns = r.state

    assert ns.debt_e8 == 100 * E8
    assert ns.free_debt_e8 == 100 * E8
    assert ns.collateral_e8 == 4 * E8
    assert ns.protocol_collateral_e8 == 2_000_000
    assert r.effects["redeemed_collateral_gross_e8"] == 1 * E8
    assert r.effects["redeemed_collateral_out_e8"] == 98_000_000
    assert r.effects["redemption_fee_collateral_e8"] == 2_000_000
    assert check_invariants(ns) == []


def test_base_rate_decay_applies_before_mint_fee_calculation() -> None:
    s = init_state()
    s = _bootstrap(s, price_e8=100 * E8)
    s = ZUSDState(
        **{
            **s.__dict__,
            "base_rate_bps": 100,
            "base_rate_last_epoch": 0,
            "base_rate_decay_per_epoch_bps": 10,
            "base_rate_borrow_bump_bps": 20,
            "borrow_fee_floor_bps": 50,
            "borrow_fee_max_bps": 500,
        }
    )
    s = _ok(s, "advance_epoch", delta=5)
    s = _ok(s, "deposit_collateral", amount_e8=2 * E8)
    r = step(s, ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.effects is not None
    ns = r.state

    # base decays from 100 -> 50 over 5 epochs; fee_bps becomes 50(floor)+50(base)=100
    assert r.effects["mint_fee_bps"] == 100
    assert r.effects["mint_fee_e8"] == 1 * E8
    # base is bumped after action.
    assert ns.base_rate_bps == 70
    assert ns.base_rate_last_epoch == ns.now_epoch
