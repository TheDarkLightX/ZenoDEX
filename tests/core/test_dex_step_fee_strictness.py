from __future__ import annotations

from src.core.dex import DexConfig, DexState, step_with_candidate_settlement
from src.core.settlement import Fill, FillAction, Settlement
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable


def test_dex_step_rejects_bool_fee_metadata_before_fee_split() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "01" * 32,
        sender_pubkey="alice",
        deadline=0,
        fields={},
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                fee_paid=False,
            )
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )

    result = step_with_candidate_settlement(
        DexConfig(settlement_validation="legacy"),
        DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()),
        [intent],
        candidate_settlement=settlement,
    )

    assert result.ok is False
    assert result.error == f"SWAP fill.fee_paid must be int for intent_id={intent.intent_id}"
