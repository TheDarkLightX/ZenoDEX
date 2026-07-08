from __future__ import annotations

import pytest

from src.core.settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement


def test_delta_helpers_compute_net_delta() -> None:
    assert BalanceDelta(pubkey="pk", asset="A", delta_add=7, delta_sub=3).net_delta() == 4
    assert ReserveDelta(pool_id="pool", asset="A", delta_add=2, delta_sub=5).net_delta() == -3
    assert LPDelta(pubkey="pk", pool_id="pool", delta_add=9, delta_sub=4).net_delta() == 5


def test_settlement_rejects_invalid_module() -> None:
    with pytest.raises(ValueError, match="Invalid module"):
        Settlement(
            module="Bad",
            version="0.1",
            batch_ref="batch",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )


def test_settlement_rejects_duplicate_included_intents() -> None:
    with pytest.raises(ValueError, match="duplicate intent_id"):
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch",
            included_intents=[("i1", FillAction.REJECT), ("i1", FillAction.FILL)],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )


def test_settlement_rejects_duplicate_fill_ids() -> None:
    with pytest.raises(ValueError, match="fills contains duplicate intent_id"):
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch",
            included_intents=[("i1", FillAction.REJECT)],
            fills=[
                Fill(intent_id="i1", action=FillAction.REJECT),
                Fill(intent_id="i1", action=FillAction.REJECT),
            ],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )


def test_settlement_rejects_fill_ids_not_included() -> None:
    with pytest.raises(ValueError, match="not in included_intents"):
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch",
            included_intents=[("i1", FillAction.REJECT)],
            fills=[Fill(intent_id="i2", action=FillAction.REJECT)],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )


def test_settlement_rejects_fill_mismatch_for_fill_actions() -> None:
    with pytest.raises(ValueError, match="Fill mismatch"):
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch",
            included_intents=[("i1", FillAction.FILL)],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )


def test_settlement_allows_reject_actions_without_fill_records() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[("i1", FillAction.REJECT)],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )

    assert settlement.included_intents == [("i1", FillAction.REJECT)]
