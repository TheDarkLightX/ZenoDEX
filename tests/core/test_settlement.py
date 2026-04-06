from __future__ import annotations

import pytest

from src.core.settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement

INTENT_ID = "0x" + "11" * 32


def test_delta_helpers_return_net_difference() -> None:
    assert BalanceDelta("pk", "asset", 7, 3).net_delta() == 4
    assert ReserveDelta("pool", "asset", 2, 5).net_delta() == -3
    assert LPDelta("pk", "pool", 9, 1).net_delta() == 8


def test_settlement_accepts_matching_fill_set() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch-1",
        included_intents=[(INTENT_ID, FillAction.FILL)],
        fills=[Fill(intent_id=INTENT_ID, action=FillAction.FILL, amount_in_filled=5, amount_out_filled=4)],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )

    assert settlement.module == "TauSwap"
    assert settlement.fills[0].intent_id == INTENT_ID


def test_settlement_rejects_duplicate_and_extra_fill_ids() -> None:
    with pytest.raises(ValueError, match="duplicate intent_id"):
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch-1",
            included_intents=[(INTENT_ID, FillAction.FILL), (INTENT_ID, FillAction.REJECT)],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )

    with pytest.raises(ValueError, match="not in included_intents"):
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch-1",
            included_intents=[(INTENT_ID, FillAction.REJECT)],
            fills=[Fill(intent_id="0x" + "22" * 32, action=FillAction.FILL, amount_in_filled=1, amount_out_filled=1)],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )

    with pytest.raises(ValueError, match="Fill mismatch"):
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch-1",
            included_intents=[(INTENT_ID, FillAction.FILL)],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
        )
