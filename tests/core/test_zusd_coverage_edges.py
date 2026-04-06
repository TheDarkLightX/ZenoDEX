from __future__ import annotations

from typing import Any

import pytest

import src.core.zusd as zusd
from src.core.zusd import (
    BPS_SCALE,
    E8,
    MAX_AMOUNT_E8,
    ZUSDCommand,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDState,
    ZUSDVault,
    check_invariants,
    check_multi_invariants,
    init_multi_state,
    init_state,
    step,
    step_multi,
)


def _single_ok(state: ZUSDState, tag: str, **args: Any) -> ZUSDState:
    res = step(state, ZUSDCommand(tag=tag, args=args))  # type: ignore[arg-type]
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _multi_ok(state: ZUSDMultiState, tag: str, **args: Any) -> ZUSDMultiState:
    res = step_multi(state, ZUSDMultiCommand(tag=tag, args=args))  # type: ignore[arg-type]
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _unsafe_single(**updates: Any) -> ZUSDState:
    base = init_state()
    inst = object.__new__(ZUSDState)
    data = dict(base.__dict__)
    data.update(updates)
    for key, value in data.items():
        object.__setattr__(inst, key, value)
    return inst


def _unsafe_multi(**updates: Any) -> ZUSDMultiState:
    base = init_multi_state()
    inst = object.__new__(ZUSDMultiState)
    data = dict(base.__dict__)
    data.update(updates)
    for key, value in data.items():
        object.__setattr__(inst, key, value)
    return inst


def test_single_helper_functions_cover_fail_closed_edges() -> None:
    assert zusd._require_pos_int(7, name="amount") == 7
    with pytest.raises(ValueError, match="amount must be a positive int"):
        zusd._require_pos_int(0, name="amount")
    with pytest.raises(ValueError, match="amount must be a positive int"):
        zusd._require_pos_int(True, name="amount")

    assert zusd._is_oracle_fresh(now_epoch=5, last_update_epoch=4, max_staleness_epochs=2, oracle_seen=True) is True
    assert zusd._is_oracle_fresh(now_epoch=10, last_update_epoch=4, max_staleness_epochs=2, oracle_seen=True) is False
    assert zusd._is_oracle_fresh(now_epoch=5, last_update_epoch=4, max_staleness_epochs=-1, oracle_seen=True) is False
    assert zusd._is_oracle_fresh(now_epoch=5, last_update_epoch=4, max_staleness_epochs=2, oracle_seen=False) is False

    zusd._check_bounded_nonneg(0, name="value")
    with pytest.raises(ValueError, match="value must be non-negative"):
        zusd._check_bounded_nonneg(-1, name="value")
    with pytest.raises(ValueError, match="value exceeds MAX_AMOUNT_E8"):
        zusd._check_bounded_nonneg(MAX_AMOUNT_E8 + 1, name="value")

    assert zusd._bounded_add(4, 5, name="sum") == 9
    with pytest.raises(ValueError, match="sum exceeds MAX_AMOUNT_E8"):
        zusd._bounded_add(MAX_AMOUNT_E8, 1, name="sum")

    assert zusd._mcr_ok(collateral_e8=0, debt_e8=0, price_e8=0, mcr_bps=11_000) is True
    assert zusd._mcr_ok(collateral_e8=2 * E8, debt_e8=100 * E8, price_e8=100 * E8, mcr_bps=11_000) is True
    assert zusd._mcr_ok(collateral_e8=1 * E8, debt_e8=100 * E8, price_e8=100 * E8, mcr_bps=11_000) is False
    assert zusd._mcr_headroom_num(collateral_e8=2 * E8, debt_e8=100 * E8, price_e8=100 * E8, mcr_bps=11_000) > 0

    assert zusd._solvent_at_price(collateral_e8=0, debt_e8=0, price_e8=0) is True
    assert zusd._solvent_at_price(collateral_e8=1 * E8, debt_e8=100 * E8, price_e8=100 * E8) is True
    assert zusd._solvent_at_price(collateral_e8=1 * E8, debt_e8=200 * E8, price_e8=100 * E8) is False

    assert zusd._mul_div_up(0, 10, 3) == 0
    assert zusd._mul_div_up(5, 4, 3) == 7
    with pytest.raises(ValueError, match="denominator must be positive"):
        zusd._mul_div_up(1, 1, 0)
    with pytest.raises(ValueError, match="mul_div_up requires non-negative inputs"):
        zusd._mul_div_up(-1, 1, 1)

    assert zusd._decayed_base_rate_bps(base_rate_bps=50, now_epoch=10, last_epoch=5, decay_per_epoch_bps=5) == 25
    with pytest.raises(ValueError, match="base-rate last epoch cannot be in the future"):
        zusd._decayed_base_rate_bps(base_rate_bps=1, now_epoch=1, last_epoch=2, decay_per_epoch_bps=1)

    assert zusd._effective_fee_bps(decayed_base_rate_bps=50, floor_bps=25, max_bps=60) == 60
    assert zusd._effective_fee_bps(decayed_base_rate_bps=BPS_SCALE, floor_bps=BPS_SCALE, max_bps=BPS_SCALE) == BPS_SCALE
    assert zusd._effective_fee_bps(decayed_base_rate_bps=4_000, floor_bps=8_000, max_bps=20_000) == BPS_SCALE

    assert zusd.in_recovery_mode(init_state()) is True
    assert (
        zusd.in_recovery_mode(
            ZUSDState(
                oracle_seen=True,
                oracle_last_update_epoch=0,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                collateral_e8=E8,
                debt_e8=100 * E8,
                free_debt_e8=100 * E8,
            )
        )
        is True
    )
    assert (
        zusd._risky_ops_allowed(
            ZUSDState(
                oracle_seen=True,
                oracle_last_update_epoch=10,
                now_epoch=10,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                collateral_e8=2 * E8,
                debt_e8=100 * E8,
                free_debt_e8=100 * E8,
            )
        )
        is True
    )
    assert (
        zusd._risky_ops_allowed(
            ZUSDState(
                oracle_seen=True,
                oracle_last_update_epoch=0,
                now_epoch=10,
                max_oracle_staleness_epochs=0,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                collateral_e8=2 * E8,
                debt_e8=100 * E8,
                free_debt_e8=100 * E8,
            )
        )
        is False
    )
    assert (
        zusd._risky_ops_allowed(
            ZUSDState(
                oracle_seen=True,
                oracle_last_update_epoch=0,
                now_epoch=0,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                collateral_e8=E8,
                debt_e8=100 * E8,
                free_debt_e8=100 * E8,
            )
        )
        is False
    )


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"oracle_last_update_epoch": 1}, "oracle_last_update_epoch cannot be in the future"),
        ({"base_rate_last_epoch": 1}, "base_rate_last_epoch cannot be in the future"),
        ({"oracle_seen": True, "price_e8": 0, "price_pending_e8": 0}, "oracle_seen requires positive active and pending prices"),
        ({"oracle_seen": True, "price_e8": 100 * E8, "price_pending_e8": 101 * E8}, "require price_pending_e8 <= price_e8"),
        ({"price_e8": 1}, "oracle-not-seen state must be zeroed"),
        ({"mcr_bps": 0}, "require 0 < mcr_bps <= ccr_bps"),
        ({"max_debt_e8": 2, "max_debt_supply_e8": 1}, "max_debt_e8 cannot exceed max_debt_supply_e8"),
        ({"base_rate_bps": BPS_SCALE + 1}, "base_rate_bps out of bounds"),
        ({"base_rate_decay_per_epoch_bps": BPS_SCALE + 1}, "base_rate_decay_per_epoch_bps out of bounds"),
        ({"base_rate_borrow_bump_bps": BPS_SCALE + 1}, "base_rate_borrow_bump_bps out of bounds"),
        ({"base_rate_redeem_bump_bps": BPS_SCALE + 1}, "base_rate_redeem_bump_bps out of bounds"),
        ({"borrow_fee_floor_bps": 5_000, "borrow_fee_max_bps": 4_000}, "borrow_fee bps bounds invalid"),
        ({"redemption_fee_floor_bps": 5_000, "redemption_fee_max_bps": 4_000}, "redemption_fee bps bounds invalid"),
    ],
)
def test_single_state_constructor_rejects_invalid_parameterizations(kwargs: dict[str, Any], message: str) -> None:
    with pytest.raises(ValueError, match=message):
        ZUSDState(**kwargs)


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"oracle_last_update_epoch": 1}, "oracle_last_update_epoch cannot be in the future"),
        ({"base_rate_last_epoch": 1}, "base_rate_last_epoch cannot be in the future"),
        ({"oracle_seen": True, "price_e8": 0, "price_pending_e8": 0}, "oracle_seen requires positive active and pending prices"),
        ({"oracle_seen": True, "price_e8": 100 * E8, "price_pending_e8": 101 * E8}, "require price_pending_e8 <= price_e8"),
        ({"price_e8": 1}, "oracle-not-seen state must be zeroed"),
        ({"mcr_bps": 0}, "require 0 < mcr_bps <= ccr_bps"),
        ({"max_debt_e8": 2, "max_debt_supply_e8": 1}, "max_debt_e8 cannot exceed max_debt_supply_e8"),
        ({"base_rate_bps": BPS_SCALE + 1}, "base_rate_bps out of bounds"),
        ({"base_rate_decay_per_epoch_bps": BPS_SCALE + 1}, "base_rate_decay_per_epoch_bps out of bounds"),
        ({"base_rate_borrow_bump_bps": BPS_SCALE + 1}, "base_rate_borrow_bump_bps out of bounds"),
        ({"base_rate_redeem_bump_bps": BPS_SCALE + 1}, "base_rate_redeem_bump_bps out of bounds"),
        ({"borrow_fee_floor_bps": 5_000, "borrow_fee_max_bps": 4_000}, "borrow_fee bps bounds invalid"),
        ({"redemption_fee_floor_bps": 5_000, "redemption_fee_max_bps": 4_000}, "redemption_fee bps bounds invalid"),
    ],
)
def test_multi_state_constructor_rejects_invalid_parameterizations(kwargs: dict[str, Any], message: str) -> None:
    with pytest.raises(ValueError, match=message):
        ZUSDMultiState(**kwargs)

    with pytest.raises(ValueError, match="vault.collateral_e8 must be non-negative"):
        ZUSDVault(collateral_e8=-1)

    assert zusd.in_multi_recovery_mode(init_multi_state()) is True
    assert (
        zusd._multi_risky_ops_allowed(
            ZUSDMultiState(
                oracle_seen=True,
                oracle_last_update_epoch=10,
                now_epoch=10,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                vault_a=ZUSDVault(collateral_e8=3 * E8, debt_e8=100 * E8),
                vault_b=ZUSDVault(collateral_e8=3 * E8, debt_e8=100 * E8),
                free_debt_e8=200 * E8,
            )
        )
        is True
    )
    assert (
        zusd._multi_risky_ops_allowed(
            ZUSDMultiState(
                oracle_seen=True,
                oracle_last_update_epoch=0,
                now_epoch=10,
                max_oracle_staleness_epochs=0,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                vault_a=ZUSDVault(collateral_e8=3 * E8, debt_e8=100 * E8),
                vault_b=ZUSDVault(collateral_e8=3 * E8, debt_e8=100 * E8),
                free_debt_e8=200 * E8,
            )
        )
        is False
    )
    assert zusd._multi_risky_ops_allowed(init_multi_state()) is False
    assert (
        zusd._multi_risky_ops_allowed(
            ZUSDMultiState(
                oracle_seen=True,
                oracle_last_update_epoch=0,
                now_epoch=0,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                vault_a=ZUSDVault(collateral_e8=E8, debt_e8=100 * E8),
                vault_b=ZUSDVault(collateral_e8=E8, debt_e8=100 * E8),
                free_debt_e8=200 * E8,
            )
        )
        is False
    )


def test_single_invariant_helpers_report_all_defensive_failures() -> None:
    assert check_invariants(
        _unsafe_single(
            oracle_seen=True,
            price_e8=0,
            price_pending_e8=0,
        )
    ) == ["inv_oracle_seen_positive_prices"]

    assert "inv_pending_le_active" in check_invariants(
        _unsafe_single(
            oracle_seen=True,
            price_e8=100 * E8,
            price_pending_e8=101 * E8,
            oracle_last_update_epoch=0,
        )
    )
    assert "inv_oracle_unseen_zeroed" in check_invariants(_unsafe_single(price_e8=1))
    assert "inv_system_no_bad_debt" in check_invariants(
        _unsafe_single(
            oracle_seen=True,
            price_e8=100 * E8,
            price_pending_e8=100 * E8,
            collateral_e8=0,
            debt_e8=1,
            free_debt_e8=1,
        )
    )


def test_multi_invariant_helpers_report_all_defensive_failures() -> None:
    assert "inv_oracle_seen_positive_prices" in check_multi_invariants(
        _unsafe_multi(
            oracle_seen=True,
            price_e8=0,
            price_pending_e8=0,
        )
    )
    assert "inv_pending_le_active" in check_multi_invariants(
        _unsafe_multi(
            oracle_seen=True,
            price_e8=100 * E8,
            price_pending_e8=101 * E8,
        )
    )
    assert "inv_oracle_unseen_zeroed" in check_multi_invariants(_unsafe_multi(price_e8=1))
    assert "inv_supply_conservation" in check_multi_invariants(
        _unsafe_multi(
            oracle_seen=True,
            price_e8=100 * E8,
            price_pending_e8=100 * E8,
            free_debt_e8=1,
        )
    )
    assert "inv_no_bad_debt_a" in check_multi_invariants(
        _unsafe_multi(
            oracle_seen=True,
            price_e8=100 * E8,
            price_pending_e8=100 * E8,
            free_debt_e8=1,
            vault_a=ZUSDVault(collateral_e8=0, debt_e8=1),
        )
    )
    assert "inv_no_bad_debt_b" in check_multi_invariants(
        _unsafe_multi(
            oracle_seen=True,
            price_e8=100 * E8,
            price_pending_e8=100 * E8,
            free_debt_e8=1,
            vault_b=ZUSDVault(collateral_e8=0, debt_e8=1),
        )
    )


def test_single_step_fail_closed_branches() -> None:
    assert "unknown action: bogus" in (step(init_state(), ZUSDCommand(tag="bogus", args={})).error or "")  # type: ignore[arg-type]
    assert "delta must be a positive int" in (step(init_state(), ZUSDCommand(tag="advance_epoch", args={"delta": "bad"})).error or "")  # type: ignore[arg-type]

    base = init_state()
    assert "requires auth_ok=true" in (step(base, ZUSDCommand(tag="bootstrap_oracle", args={"price_e8": E8})).error or "")
    boot = _single_ok(base, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    assert "oracle not bootstrapped" in (step(base, ZUSDCommand(tag="oracle_report", args={"price_e8": 1, "auth_ok": True})).error or "")
    assert "oracle not bootstrapped" in (step(base, ZUSDCommand(tag="oracle_commit", args={"auth_ok": True})).error or "")
    assert "already bootstrapped" in (step(boot, ZUSDCommand(tag="bootstrap_oracle", args={"price_e8": 100 * E8, "auth_ok": True})).error or "")
    assert "oracle_report requires auth_ok=true" in (step(boot, ZUSDCommand(tag="oracle_report", args={"price_e8": 90 * E8})).error or "")
    lower = _single_ok(boot, "oracle_report", price_e8=90 * E8, auth_ok=True)
    assert "non-increasing pending price" in (step(lower, ZUSDCommand(tag="oracle_report", args={"price_e8": 95 * E8, "auth_ok": True})).error or "")
    assert "oracle_commit requires auth_ok=true" in (step(lower, ZUSDCommand(tag="oracle_commit", args={})).error or "")

    funded = _single_ok(boot, "deposit_collateral", amount_e8=2 * E8)
    assert "insufficient collateral" in (step(funded, ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": 3 * E8})).error or "")
    minted = _single_ok(funded, "mint_zusd", amount_e8=150 * E8)
    pending = _single_ok(minted, "oracle_report", price_e8=90 * E8, auth_ok=True)
    assert "freeze" in (step(pending, ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": 1})).error or "")
    safer = _single_ok(_single_ok(boot, "deposit_collateral", amount_e8=3 * E8), "mint_zusd", amount_e8=150 * E8)
    assert "would violate MCR" in (step(safer, ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": 2 * E8})).error or "")

    floor_state = ZUSDState(
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        collateral_e8=2 * E8,
    )
    assert "min_debt_open" in (step(floor_state, ZUSDCommand(tag="mint_zusd", args={"amount_e8": 1})).error or "")
    assert "max_debt_e8" in (
        step(ZUSDState(**{**floor_state.__dict__, "max_debt_e8": 10}), ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8})).error
        or ""
    )
    assert "max_debt_supply" in (
        step(
            _unsafe_single(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                collateral_e8=4 * E8,
                debt_e8=1,
                free_debt_e8=100 * E8,
                max_debt_e8=200 * E8,
                max_debt_supply_e8=150 * E8,
            ),
            ZUSDCommand(tag="mint_zusd", args={"amount_e8": 60 * E8}),
        ).error
        or ""
    )
    assert "would violate MCR" in (
        step(ZUSDState(**{**floor_state.__dict__, "collateral_e8": E8}), ZUSDCommand(tag="mint_zusd", args={"amount_e8": 100 * E8})).error
        or ""
    )

    assert "repay exceeds debt" in (step(init_state(), ZUSDCommand(tag="repay_zusd", args={"amount_e8": 1})).error or "")
    assert "repay exceeds free debt balance" in (
        step(
            _unsafe_single(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                debt_e8=10,
                free_debt_e8=0,
            ),
            ZUSDCommand(tag="repay_zusd", args={"amount_e8": 1}),
        ).error
        or ""
    )
    assert "deposit_sp exceeds free debt balance" in (
        step(
            _unsafe_single(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                debt_e8=10,
                free_debt_e8=0,
            ),
            ZUSDCommand(tag="deposit_sp", args={"amount_e8": 1}),
        ).error
        or ""
    )
    assert "deposit_sp exceeds max_debt_supply" in (
        step(
            _unsafe_single(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                debt_e8=10,
                free_debt_e8=10,
                max_debt_supply_e8=0,
            ),
            ZUSDCommand(tag="deposit_sp", args={"amount_e8": 1}),
        ).error
        or ""
    )
    assert "withdraw_sp exceeds sp_debt" in (step(init_state(), ZUSDCommand(tag="withdraw_sp", args={"amount_e8": 1})).error or "")

    withdraw_sp_state = _unsafe_single(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=90 * E8,
        oracle_last_update_epoch=0,
        debt_e8=10,
        free_debt_e8=0,
        sp_debt_e8=10,
        collateral_e8=E8,
    )
    assert "freeze" in (step(withdraw_sp_state, ZUSDCommand(tag="withdraw_sp", args={"amount_e8": 1})).error or "")
    assert "not at MCR" in (
        step(
            _unsafe_single(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                debt_e8=200 * E8,
                sp_debt_e8=10,
                sp_coll_e8=3 * E8,
                collateral_e8=E8,
            ),
            ZUSDCommand(tag="withdraw_sp", args={"amount_e8": 1}),
        ).error
        or ""
    )

    assert "requires initialized oracle" in (step(init_state(), ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or "")
    assert "pending mismatch" in (step(pending, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or "")
    stale = _single_ok(_single_ok(boot, "deposit_collateral", amount_e8=2 * E8), "mint_zusd", amount_e8=100 * E8)
    stale = _single_ok(stale, "advance_epoch", delta=101)
    assert "stale oracle" in (step(stale, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or "")
    assert "exceeds debt" in (step(boot, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or "")
    debt_with_sp = _single_ok(_single_ok(minted, "deposit_sp", amount_e8=50 * E8), "advance_epoch", delta=1)
    assert "exceeds free debt" in (step(debt_with_sp, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 120 * E8})).error or "")
    tiny = _unsafe_single(
        oracle_seen=True,
        price_e8=MAX_AMOUNT_E8,
        price_pending_e8=MAX_AMOUNT_E8,
        debt_e8=10,
        free_debt_e8=10,
        collateral_e8=10,
    )
    assert "amount too small" in (step(tiny, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or "")
    coll_short = _unsafe_single(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        debt_e8=200 * E8,
        free_debt_e8=200 * E8,
        collateral_e8=E8,
    )
    assert "insufficient vault collateral" in (
        step(coll_short, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 150 * E8})).error or ""
    )
    fee_all = _unsafe_single(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        debt_e8=100 * E8,
        free_debt_e8=100 * E8,
        collateral_e8=2 * E8,
        redemption_fee_floor_bps=BPS_SCALE,
        redemption_fee_max_bps=BPS_SCALE,
    )
    assert "fee consumes all collateral" in (step(fee_all, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8})).error or "")
    fee_cap = _unsafe_single(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        debt_e8=100 * E8,
        free_debt_e8=100 * E8,
        collateral_e8=2 * E8,
        redemption_fee_floor_bps=100,
        redemption_fee_max_bps=100,
        max_protocol_coll_e8=1,
    )
    assert "protocol collateral cap exceeded" in (step(fee_cap, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8})).error or "")
    redeem_mcr = ZUSDState(
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        collateral_e8=2 * E8,
        debt_e8=150 * E8,
        free_debt_e8=150 * E8,
        mcr_bps=16_000,
        ccr_bps=17_000,
    )
    assert "would violate MCR" in (
        step(redeem_mcr, ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8})).error or ""
    )

    assert "initialized pending oracle price" in (step(init_state(), ZUSDCommand(tag="liquidate", args={})).error or "")
    assert "no debt to liquidate" in (step(boot, ZUSDCommand(tag="liquidate", args={})).error or "")
    assert "vault not under MCR" in (step(minted, ZUSDCommand(tag="liquidate", args={})).error or "")
    underwater = _single_ok(_single_ok(_single_ok(funded, "mint_zusd", amount_e8=150 * E8), "deposit_sp", amount_e8=10 * E8), "oracle_report", price_e8=50 * E8, auth_ok=True)
    assert "cannot absorb debt" in (step(underwater, ZUSDCommand(tag="liquidate", args={})).error or "")
    capped = ZUSDState(**{**underwater.__dict__, "sp_debt_e8": underwater.debt_e8, "max_sp_coll_e8": 1})
    assert "collateral cap exceeded" in (step(capped, ZUSDCommand(tag="liquidate", args={})).error or "")
    assert "invariant violation" in (
        step(
            _unsafe_single(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=1,
            ),
            ZUSDCommand(tag="deposit_collateral", args={"amount_e8": 1}),
        ).error
        or ""
    )


def test_multi_step_fail_closed_branches() -> None:
    assert "unknown action: bogus" in (step_multi(init_multi_state(), ZUSDMultiCommand(tag="bogus", args={})).error or "")  # type: ignore[arg-type]
    assert "vault must be 'a' or 'b'" in (
        step_multi(
            ZUSDMultiState(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
            ),
            ZUSDMultiCommand(tag="deposit_collateral", args={"vault": "bad", "amount_e8": 1}),  # type: ignore[arg-type]
        ).error
        or ""
    )

    base = init_multi_state()
    assert "requires auth_ok=true" in (step_multi(base, ZUSDMultiCommand(tag="bootstrap_oracle", args={"price_e8": E8})).error or "")
    boot = _multi_ok(base, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    assert "oracle not bootstrapped" in (
        step_multi(base, ZUSDMultiCommand(tag="oracle_report", args={"price_e8": 1, "auth_ok": True})).error or ""
    )
    assert "oracle not bootstrapped" in (
        step_multi(base, ZUSDMultiCommand(tag="oracle_commit", args={"auth_ok": True})).error or ""
    )
    assert "already bootstrapped" in (step_multi(boot, ZUSDMultiCommand(tag="bootstrap_oracle", args={"price_e8": 100 * E8, "auth_ok": True})).error or "")
    assert "oracle_report requires auth_ok=true" in (step_multi(boot, ZUSDMultiCommand(tag="oracle_report", args={"price_e8": 90 * E8})).error or "")
    assert "oracle_commit requires auth_ok=true" in (step_multi(boot, ZUSDMultiCommand(tag="oracle_commit", args={})).error or "")
    lower_multi = _multi_ok(boot, "oracle_report", price_e8=90 * E8, auth_ok=True)
    assert "non-increasing pending price" in (
        step_multi(lower_multi, ZUSDMultiCommand(tag="oracle_report", args={"price_e8": 95 * E8, "auth_ok": True})).error
        or ""
    )

    funded = _multi_ok(_multi_ok(boot, "deposit_collateral", vault="a", amount_e8=2 * E8), "deposit_collateral", vault="b", amount_e8=2 * E8)
    assert "insufficient collateral" in (step_multi(funded, ZUSDMultiCommand(tag="withdraw_collateral", args={"vault": "a", "amount_e8": 3 * E8})).error or "")
    minted_a = _multi_ok(funded, "mint_zusd", vault="a", amount_e8=150 * E8)
    minted = _multi_ok(minted_a, "mint_zusd", vault="b", amount_e8=100 * E8)
    pending = _multi_ok(minted, "oracle_report", price_e8=90 * E8, auth_ok=True)
    assert "freeze" in (step_multi(pending, ZUSDMultiCommand(tag="withdraw_collateral", args={"vault": "a", "amount_e8": 1})).error or "")
    assert "would violate MCR" in (step_multi(minted_a, ZUSDMultiCommand(tag="withdraw_collateral", args={"vault": "a", "amount_e8": E8})).error or "")
    commit_b_fail = _multi_ok(_multi_ok(boot, "deposit_collateral", vault="a", amount_e8=2 * E8), "deposit_collateral", vault="b", amount_e8=2 * E8)
    commit_b_fail = _multi_ok(commit_b_fail, "mint_zusd", vault="b", amount_e8=150 * E8)
    commit_b_fail = _multi_ok(commit_b_fail, "oracle_report", price_e8=50 * E8, auth_ok=True)
    assert "vault b below MCR" in (
        step_multi(commit_b_fail, ZUSDMultiCommand(tag="oracle_commit", args={"auth_ok": True})).error or ""
    )

    min_floor = ZUSDMultiState(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        vault_a=ZUSDVault(collateral_e8=2 * E8, debt_e8=0),
        free_debt_e8=0,
    )
    assert "min_debt_open" in (step_multi(min_floor, ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 1})).error or "")
    assert "max_debt_e8" in (
        step_multi(ZUSDMultiState(**{**min_floor.__dict__, "max_debt_e8": 10}), ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 100 * E8})).error
        or ""
    )
    assert "max_debt_supply" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                vault_a=ZUSDVault(collateral_e8=4 * E8, debt_e8=1),
                free_debt_e8=100 * E8,
                max_debt_e8=200 * E8,
                max_debt_supply_e8=150 * E8,
            ),
            ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 60 * E8}),
        ).error
        or ""
    )
    assert "would violate MCR" in (
        step_multi(
            ZUSDMultiState(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                vault_a=ZUSDVault(collateral_e8=E8, debt_e8=0),
            ),
            ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 100 * E8}),
        ).error
        or ""
    )

    assert "repay exceeds vault debt" in (step_multi(boot, ZUSDMultiCommand(tag="repay_zusd", args={"vault": "a", "amount_e8": 1})).error or "")
    assert "repay exceeds free debt balance" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                vault_a=ZUSDVault(collateral_e8=E8, debt_e8=10),
            ),
            ZUSDMultiCommand(tag="repay_zusd", args={"vault": "a", "amount_e8": 1}),
        ).error
        or ""
    )
    assert "deposit_sp exceeds free debt balance" in (step_multi(boot, ZUSDMultiCommand(tag="deposit_sp", args={"amount_e8": 1})).error or "")
    assert "withdraw_sp exceeds sp_debt" in (step_multi(boot, ZUSDMultiCommand(tag="withdraw_sp", args={"amount_e8": 1})).error or "")
    multi_freeze = _unsafe_multi(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=90 * E8,
        sp_debt_e8=10,
        vault_a=ZUSDVault(collateral_e8=E8, debt_e8=10),
        vault_b=ZUSDVault(collateral_e8=E8, debt_e8=10),
    )
    assert "freeze" in (
        step_multi(multi_freeze, ZUSDMultiCommand(tag="withdraw_sp", args={"amount_e8": 1})).error or ""
    )
    multi_a_not_mcr = _unsafe_multi(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        sp_debt_e8=10,
        sp_coll_e8=5 * E8,
        vault_a=ZUSDVault(collateral_e8=E8, debt_e8=200 * E8),
        vault_b=ZUSDVault(collateral_e8=3 * E8, debt_e8=10),
    )
    assert "vault a not at MCR" in (
        step_multi(multi_a_not_mcr, ZUSDMultiCommand(tag="withdraw_sp", args={"amount_e8": 1})).error or ""
    )
    multi_b_not_mcr = _unsafe_multi(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        sp_debt_e8=10,
        sp_coll_e8=5 * E8,
        vault_a=ZUSDVault(collateral_e8=3 * E8, debt_e8=10),
        vault_b=ZUSDVault(collateral_e8=E8, debt_e8=200 * E8),
    )
    assert "vault b not at MCR" in (
        step_multi(multi_b_not_mcr, ZUSDMultiCommand(tag="withdraw_sp", args={"amount_e8": 1})).error or ""
    )
    assert "deposit_sp exceeds max_debt_supply" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=10,
                max_debt_supply_e8=0,
            ),
            ZUSDMultiCommand(tag="deposit_sp", args={"amount_e8": 1}),
        ).error
        or ""
    )

    assert "requires initialized oracle" in (step_multi(init_multi_state(), ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or "")
    assert "pending mismatch" in (step_multi(pending, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or "")
    tiny_multi = _unsafe_multi(
        oracle_seen=True,
        price_e8=MAX_AMOUNT_E8,
        price_pending_e8=MAX_AMOUNT_E8,
        free_debt_e8=10,
        vault_a=ZUSDVault(collateral_e8=10, debt_e8=10),
    )
    assert "amount too small" in (
        step_multi(tiny_multi, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 1})).error or ""
    )
    stale_multi = _multi_ok(
        _multi_ok(
            _multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True),
            "deposit_collateral",
            vault="a",
            amount_e8=2 * E8,
        ),
        "mint_zusd",
        vault="a",
        amount_e8=100 * E8,
    )
    stale_multi = _multi_ok(stale_multi, "advance_epoch", delta=101)
    assert "stale oracle" in (
        step_multi(stale_multi, ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 10 * E8})).error
        or ""
    )
    assert "vault must be 'a' or 'b'" in (
        step_multi(minted, ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "bad", "amount_e8": 10 * E8})).error
        or ""
    )
    assert "no redeemable vault" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=10 * E8,
                vault_a=ZUSDVault(collateral_e8=E8, debt_e8=5 * E8),
                vault_b=ZUSDVault(collateral_e8=E8, debt_e8=5 * E8),
            ),
            ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 10 * E8}),
        ).error
        or ""
    )
    assert "no redeemable vault" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=150 * E8,
                vault_a=ZUSDVault(collateral_e8=E8, debt_e8=200 * E8),
                vault_b=ZUSDVault(collateral_e8=3 * E8, debt_e8=10 * E8),
            ),
            ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 150 * E8}),
        ).error
        or ""
    )
    explicit_short = _unsafe_multi(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        free_debt_e8=200 * E8,
        vault_a=ZUSDVault(collateral_e8=E8, debt_e8=200 * E8),
        vault_b=ZUSDVault(collateral_e8=E8, debt_e8=5 * E8),
    )
    assert "insufficient vault collateral" in (
        step_multi(
            explicit_short,
            ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 150 * E8}),
        ).error
        or ""
    )
    fee_all_multi = _unsafe_multi(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        free_debt_e8=100 * E8,
        vault_a=ZUSDVault(collateral_e8=2 * E8, debt_e8=100 * E8),
        redemption_fee_floor_bps=BPS_SCALE,
        redemption_fee_max_bps=BPS_SCALE,
    )
    assert "fee consumes all collateral" in (
        step_multi(
            fee_all_multi,
            ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 50 * E8}),
        ).error
        or ""
    )
    fee_cap_multi = _unsafe_multi(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        free_debt_e8=100 * E8,
        vault_a=ZUSDVault(collateral_e8=2 * E8, debt_e8=100 * E8),
        redemption_fee_floor_bps=100,
        redemption_fee_max_bps=100,
        max_protocol_coll_e8=1,
    )
    assert "protocol collateral cap exceeded" in (
        step_multi(
            fee_cap_multi,
            ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 50 * E8}),
        ).error
        or ""
    )
    assert "exceeds vault debt" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=200 * E8,
                vault_a=ZUSDVault(collateral_e8=4 * E8, debt_e8=10 * E8),
            ),
            ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 50 * E8}),
        ).error
        or ""
    )
    explicit_mcr = ZUSDMultiState(
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        free_debt_e8=150 * E8,
        vault_a=ZUSDVault(collateral_e8=2 * E8, debt_e8=150 * E8),
        mcr_bps=16_000,
        ccr_bps=17_000,
    )
    assert "would violate MCR" in (
        step_multi(
            explicit_mcr,
            ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 50 * E8}),
        ).error
        or ""
    )
    assert "exceeds free debt" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=10 * E8,
                vault_a=ZUSDVault(collateral_e8=4 * E8, debt_e8=200 * E8),
            ),
            ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 50 * E8}),
        ).error
        or ""
    )
    assert "cannot absorb debt" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=50 * E8,
                sp_debt_e8=10 * E8,
                vault_a=ZUSDVault(collateral_e8=2 * E8, debt_e8=150 * E8),
            ),
            ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
        ).error
        or ""
    )
    assert "collateral cap exceeded" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=50 * E8,
                sp_debt_e8=200 * E8,
                max_sp_coll_e8=1,
                vault_a=ZUSDVault(collateral_e8=2 * E8, debt_e8=150 * E8),
            ),
            ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
        ).error
        or ""
    )
    assert "invariant violation" in (
        step_multi(
            _unsafe_multi(
                oracle_seen=True,
                price_e8=100 * E8,
                price_pending_e8=100 * E8,
                free_debt_e8=1,
            ),
            ZUSDMultiCommand(tag="deposit_collateral", args={"vault": "a", "amount_e8": 1}),
        ).error
        or ""
    )

    assert "initialized pending oracle price" in (step_multi(init_multi_state(), ZUSDMultiCommand(tag="liquidate", args={"vault": "a"})).error or "")
    assert "no vault debt to liquidate" in (step_multi(boot, ZUSDMultiCommand(tag="liquidate", args={"vault": "a"})).error or "")
    assert "vault not under MCR" in (step_multi(minted, ZUSDMultiCommand(tag="liquidate", args={"vault": "b"})).error or "")


def test_single_and_multi_success_paths_cover_remaining_state_machine_branches() -> None:
    assert (
        zusd._risky_ops_allowed(
            _unsafe_single(
                oracle_seen=True,
                price_e8=0,
                price_pending_e8=E8,
                oracle_last_update_epoch=0,
            )
        )
        is False
    )

    single = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    single = _single_ok(single, "deposit_collateral", amount_e8=3 * E8)
    single = _single_ok(single, "mint_zusd", amount_e8=100 * E8)
    withdrawn = step(single, ZUSDCommand(tag="withdraw_collateral", args={"amount_e8": E8 // 2}))
    assert withdrawn.ok, withdrawn.error
    assert withdrawn.state is not None
    assert withdrawn.effects == {"event": "collateral_withdrawn", "amount_e8": E8 // 2}

    sp_ready = _single_ok(withdrawn.state, "deposit_sp", amount_e8=20 * E8)
    sp_withdrawn = step(sp_ready, ZUSDCommand(tag="withdraw_sp", args={"amount_e8": 5 * E8}))
    assert sp_withdrawn.ok, sp_withdrawn.error
    assert sp_withdrawn.state is not None
    assert sp_withdrawn.effects == {"event": "sp_withdrawn", "amount_e8": 5 * E8}

    multi = _multi_ok(init_multi_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    multi = _multi_ok(multi, "deposit_collateral", vault="a", amount_e8=4 * E8)
    multi = _multi_ok(multi, "deposit_collateral", vault="b", amount_e8=4 * E8)
    multi = _multi_ok(multi, "mint_zusd", vault="a", amount_e8=100 * E8)
    multi = _multi_ok(multi, "mint_zusd", vault="b", amount_e8=100 * E8)

    multi_withdraw = step_multi(
        multi,
        ZUSDMultiCommand(tag="withdraw_collateral", args={"vault": "a", "amount_e8": E8 // 2}),
    )
    assert multi_withdraw.ok, multi_withdraw.error
    assert multi_withdraw.state is not None
    assert multi_withdraw.effects == {"event": "collateral_withdrawn", "vault": "a", "amount_e8": E8 // 2}

    multi_repaid = step_multi(
        multi_withdraw.state,
        ZUSDMultiCommand(tag="repay_zusd", args={"vault": "a", "amount_e8": 10 * E8}),
    )
    assert multi_repaid.ok, multi_repaid.error
    assert multi_repaid.state is not None
    assert multi_repaid.effects == {"event": "zusd_repaid", "vault": "a", "amount_e8": 10 * E8}

    multi_sp_ready = _multi_ok(multi_repaid.state, "deposit_sp", amount_e8=20 * E8)
    multi_sp_withdraw = step_multi(
        multi_sp_ready,
        ZUSDMultiCommand(tag="withdraw_sp", args={"amount_e8": 5 * E8}),
    )
    assert multi_sp_withdraw.ok, multi_sp_withdraw.error
    assert multi_sp_withdraw.state is not None
    assert multi_sp_withdraw.effects == {"event": "sp_withdrawn", "amount_e8": 5 * E8}
