from __future__ import annotations

from types import SimpleNamespace

import pytest

from src.core.zusd import (
    E8,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDVault,
    check_multi_invariants,
    in_multi_recovery_mode,
    init_multi_state,
    step_multi,
)


def _ok(s: ZUSDMultiState, tag: str, **kwargs) -> ZUSDMultiState:
    r = step_multi(s, ZUSDMultiCommand(tag=tag, args=kwargs))
    assert r.ok, r.error
    assert r.state is not None
    return r.state


def _bootstrap(s: ZUSDMultiState, *, price_e8: int = 100 * E8) -> ZUSDMultiState:
    return _ok(s, "bootstrap_oracle", price_e8=price_e8, auth_ok=True)


def test_multi_supply_conservation_across_two_vaults() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=3 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=150 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=100 * E8)
    s = _ok(s, "deposit_sp", amount_e8=90 * E8)

    assert s.vault_a.debt_e8 == 150 * E8
    assert s.vault_b.debt_e8 == 100 * E8
    assert s.free_debt_e8 == 160 * E8
    assert s.sp_debt_e8 == 90 * E8
    assert check_multi_invariants(s) == []


def test_oracle_commit_requires_both_vaults_above_mcr_at_pending() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=2 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=150 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=100 * E8)
    s = _ok(s, "oracle_report", price_e8=50 * E8, auth_ok=True)

    r = step_multi(s, ZUSDMultiCommand(tag="oracle_commit", args={"auth_ok": True}))
    assert not r.ok
    assert "below MCR" in (r.error or "")


def test_multi_oracle_commit_rejects_stale_pending_observation() -> None:
    s = ZUSDMultiState(max_oracle_staleness_epochs=2)
    s = _bootstrap(s)
    s = _ok(s, "oracle_report", price_e8=90 * E8, auth_ok=True)
    s = _ok(s, "advance_epoch", delta=3)

    r = step_multi(s, ZUSDMultiCommand(tag="oracle_commit", args={"auth_ok": True}))

    assert not r.ok
    assert r.state is None
    assert r.error == "oracle_commit blocked: pending observation is stale"


def test_recovery_mode_blocks_risky_ops_multi() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=2 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=120 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=120 * E8)
    s = _ok(s, "oracle_report", price_e8=70 * E8, auth_ok=True)
    s = _ok(s, "oracle_commit", auth_ok=True)

    assert in_multi_recovery_mode(s) is True

    r_mint = step_multi(s, ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 1 * E8}))
    assert not r_mint.ok
    assert "recovery mode" in (r_mint.error or "")

    r_wd = step_multi(s, ZUSDMultiCommand(tag="withdraw_collateral", args={"vault": "b", "amount_e8": 1}))
    assert not r_wd.ok
    assert "recovery mode" in (r_wd.error or "")


def test_liquidate_single_vault_moves_only_target_debt_and_collateral() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=3 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=2 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=150 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=100 * E8)
    s = _ok(s, "deposit_sp", amount_e8=180 * E8)
    s = _ok(s, "oracle_report", price_e8=50 * E8, auth_ok=True)

    r = step_multi(s, ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}))
    assert r.ok, r.error
    assert r.state is not None
    ns = r.state

    assert ns.vault_a.debt_e8 == 0
    assert ns.vault_a.collateral_e8 == 0
    assert ns.vault_b.debt_e8 == 100 * E8
    assert ns.vault_b.collateral_e8 == 2 * E8
    assert ns.sp_debt_e8 == 30 * E8
    assert ns.sp_coll_e8 == 3 * E8


def test_pending_freeze_blocks_mint_until_commit() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=3 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=120 * E8)
    s = _ok(s, "oracle_report", price_e8=90 * E8, auth_ok=True)

    r = step_multi(s, ZUSDMultiCommand(tag="mint_zusd", args={"vault": "a", "amount_e8": 1 * E8}))
    assert not r.ok
    assert "freeze" in (r.error or "")


def test_multi_borrow_fee_and_redemption_flow_on_one_vault() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = ZUSDMultiState(
        **{
            **s.__dict__,
            "borrow_fee_floor_bps": 100,
            "borrow_fee_max_bps": 100,
            "redemption_fee_floor_bps": 100,
            "redemption_fee_max_bps": 100,
        }
    )
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=3 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=200 * E8)
    assert s.vault_a.debt_e8 == 202 * E8
    assert s.free_debt_e8 == 202 * E8
    assert s.protocol_revenue_zusd_cum_e8 == 2 * E8

    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 50 * E8}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.effects is not None
    ns = r.state
    assert ns.vault_a.debt_e8 == 152 * E8
    assert ns.vault_a.collateral_e8 == 250_000_000
    assert ns.free_debt_e8 == 152 * E8
    assert ns.protocol_collateral_e8 == 500_000
    assert r.effects["redemption_fee_collateral_e8"] == 500_000
    assert check_multi_invariants(ns) == []


def test_multi_repay_and_redemption_cannot_leave_sub_floor_debt() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=3 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=150 * E8)

    repay = step_multi(s, ZUSDMultiCommand(tag="repay_zusd", args={"vault": "a", "amount_e8": 75 * E8}))
    assert not repay.ok
    assert "below min_debt_open_e8" in (repay.error or "")

    redeem = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 75 * E8}))
    assert not redeem.ok
    assert "below min_debt_open_e8" in (redeem.error or "")

    full = step_multi(s, ZUSDMultiCommand(tag="repay_zusd", args={"vault": "a", "amount_e8": 150 * E8}))
    assert full.ok, full.error
    assert full.state is not None
    assert full.state.vault_a.debt_e8 == 0
    assert check_multi_invariants(full.state) == []


def test_multi_invariant_detection_for_sub_floor_debt() -> None:
    s = ZUSDMultiState(
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        free_debt_e8=50 * E8,
        vault_a=ZUSDVault(collateral_e8=2 * E8, debt_e8=50 * E8),
    )

    assert "inv_debt_floor_a" in check_multi_invariants(s)


def test_multi_debt_floor_sequence_grid_for_repay_and_redeem() -> None:
    for minted_e8 in (100 * E8, 150 * E8, 250 * E8):
        s = init_multi_state()
        s = _bootstrap(s)
        s = _ok(s, "deposit_collateral", vault="a", amount_e8=10 * E8)
        s = _ok(s, "mint_zusd", vault="a", amount_e8=minted_e8)

        for amt in tuple(a for a in (25 * E8, 50 * E8, 75 * E8, minted_e8) if a <= minted_e8):
            post_debt = minted_e8 - amt
            repay = step_multi(s, ZUSDMultiCommand(tag="repay_zusd", args={"vault": "a", "amount_e8": amt}))
            redeem = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": amt}))
            should_accept = post_debt == 0 or post_debt >= s.min_debt_open_e8
            assert repay.ok is should_accept
            assert redeem.ok is should_accept


def test_multi_redemption_blocked_when_pending_oracle_differs() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=3 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=120 * E8)
    s = _ok(s, "oracle_report", price_e8=90 * E8, auth_ok=True)

    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"vault": "a", "amount_e8": 10 * E8}))
    assert not r.ok
    assert "pending mismatch" in (r.error or "")


def test_multi_redemption_auto_selects_closest_to_mcr() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=5 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=5 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=200 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=300 * E8)

    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.effects is not None
    ns = r.state

    assert r.effects["vault"] == "b"
    assert r.effects["selection_policy"] == "closest_to_mcr"
    assert ns.vault_a.debt_e8 == 200 * E8
    assert ns.vault_b.debt_e8 == 250 * E8


def test_multi_redemption_allows_amount_equal_to_free_debt() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=5 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=5 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=200 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=300 * E8)
    s = _ok(s, "deposit_sp", amount_e8=450 * E8)

    assert s.free_debt_e8 == 50 * E8
    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.state.free_debt_e8 == 0


def test_multi_redemption_exceeding_free_debt_fails_before_auto_selection(monkeypatch: pytest.MonkeyPatch) -> None:
    import src.core.zusd as zusd_mod

    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=5 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=5 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=200 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=300 * E8)
    s = _ok(s, "deposit_sp", amount_e8=450 * E8)

    called = False

    def _selector(**_kwargs):
        nonlocal called
        called = True
        raise AssertionError("selector should not be called")

    monkeypatch.setattr(zusd_mod, "select_multi_redeem_vault", _selector)

    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 51 * E8}))
    assert not r.ok
    assert r.error == "redemption exceeds free debt"
    assert called is False


def test_multi_redemption_auto_tie_breaks_to_vault_a() -> None:
    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=4 * E8)
    s = _ok(s, "deposit_collateral", vault="b", amount_e8=4 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=200 * E8)
    s = _ok(s, "mint_zusd", vault="b", amount_e8=200 * E8)

    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8}))
    assert r.ok, r.error
    assert r.state is not None
    assert r.effects is not None

    assert r.effects["vault"] == "a"
    assert r.effects["selection_policy"] == "closest_to_mcr"
    assert r.state.vault_a.debt_e8 == 150 * E8
    assert r.state.vault_b.debt_e8 == 200 * E8


def test_multi_redemption_auto_fails_closed_when_selector_omits_post_state(monkeypatch: pytest.MonkeyPatch) -> None:
    import src.core.zusd as zusd_mod

    s = init_multi_state()
    s = _bootstrap(s)
    s = _ok(s, "deposit_collateral", vault="a", amount_e8=5 * E8)
    s = _ok(s, "mint_zusd", vault="a", amount_e8=200 * E8)

    monkeypatch.setattr(
        zusd_mod,
        "select_multi_redeem_vault",
        lambda **_kwargs: SimpleNamespace(
            selected_vault="a",
            selected_post_collateral_e8=None,
            selected_post_debt_e8=None,
        ),
    )
    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": 50 * E8}))
    assert not r.ok
    assert r.error == "redeem selection missing post-state"


def test_multi_redemption_auto_policy_matches_bounded_oracle() -> None:
    price_e8 = 100 * E8
    amount_e8 = 50 * E8
    gross_collateral_e8 = (amount_e8 * E8) // price_e8
    mcr_bps = 11_000

    def _headroom(collateral_e8: int, debt_e8: int) -> int:
        return (collateral_e8 * price_e8 * 10_000) - (debt_e8 * mcr_bps * E8)

    for coll_a in (2 * E8, 3 * E8, 4 * E8):
        for debt_a in (120 * E8, 160 * E8, 200 * E8, 240 * E8):
            for coll_b in (2 * E8, 3 * E8, 4 * E8):
                for debt_b in (120 * E8, 160 * E8, 200 * E8, 240 * E8):
                    s = ZUSDMultiState(
                        oracle_seen=True,
                        oracle_last_update_epoch=0,
                        price_e8=price_e8,
                        price_pending_e8=price_e8,
                        vault_a=ZUSDVault(collateral_e8=coll_a, debt_e8=debt_a),
                        vault_b=ZUSDVault(collateral_e8=coll_b, debt_e8=debt_b),
                        free_debt_e8=debt_a + debt_b,
                        sp_debt_e8=0,
                        sp_coll_e8=0,
                    )
                    if check_multi_invariants(s):
                        continue

                    candidates: list[tuple[int, str]] = []
                    for vid, coll, debt in (("a", coll_a, debt_a), ("b", coll_b, debt_b)):
                        if debt < amount_e8 or coll < gross_collateral_e8:
                            continue
                        post_debt = debt - amount_e8
                        if post_debt != 0 and post_debt < s.min_debt_open_e8:
                            continue
                        post_coll = coll - gross_collateral_e8
                        if (post_coll * price_e8 * 10_000) < (post_debt * mcr_bps * E8):
                            continue
                        candidates.append((_headroom(coll, debt), vid))

                    r = step_multi(s, ZUSDMultiCommand(tag="redeem_zusd", args={"amount_e8": amount_e8}))
                    if not candidates:
                        assert not r.ok
                        continue

                    candidates.sort(key=lambda x: (x[0], x[1]))
                    expected = candidates[0][1]
                    assert r.ok, r.error
                    assert r.effects is not None
                    assert r.effects["vault"] == expected
