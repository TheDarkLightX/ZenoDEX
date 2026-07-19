"""Public-boundary reject/no-op regressions from the V4 oracle workbook."""

from __future__ import annotations

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation, parse_intents
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus
from src.state.state_root import compute_state_root

SENDER = "0x" + "11" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "aa" * 32


def _state() -> DexState:
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 10_000)
    balances.set(SENDER, ASSET1, 10_000)
    return DexState(
        balances=balances,
        pools={
            POOL_ID: PoolState(
                pool_id=POOL_ID,
                asset0=ASSET0,
                asset1=ASSET1,
                reserve0=1_000,
                reserve1=2_000,
                fee_bps=50,
                lp_supply=1_000,
                status=PoolStatus.ACTIVE,
                created_at=0,
                curve_tag="CPMM",
                curve_params="",
            )
        },
        lp_balances=LPTable(),
        nonces=NonceTable(),
    )


def _exact_in(*, intent_id: str, nonce: int, amount_in: int) -> dict[str, object]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": intent_id,
        "sender_pubkey": SENDER,
        "deadline": 9999999999,
        "nonce": nonce,
        "pool_id": POOL_ID,
        "asset_in": ASSET1,
        "asset_out": ASSET0,
        "amount_in": amount_in,
        "min_amount_out": 1,
    }


def _root(state: DexState) -> str:
    return compute_state_root(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
    )


@pytest.mark.parametrize("supplied", [False, True])
def test_rejected_settlement_is_atomic_independent_of_transport(supplied: bool) -> None:
    state = _state()
    intent = _exact_in(intent_id="0x" + "01" * 32, nonce=1, amount_in=2)
    operations: dict[str, object] = {"2": [intent]}
    if supplied:
        settlement = compute_settlement(
            intents=parse_intents(operations),
            pools=state.pools,
            balances=state.balances,
            lp_balances=state.lp_balances,
        )
        operations.update(create_settlement_operation(settlement))

    root_before = _root(state)
    result = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=not supplied,
            require_intent_signatures=False,
        ),
        state=state,
        operations=operations,
        block_timestamp=1,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.state is None
    assert result.settlement is None
    assert result.error == (
        "settlement contains rejected intent at public DEX boundary: "
        + str(intent["intent_id"])
    )
    assert _root(state) == root_before
    assert state.nonces.get_last(SENDER) == 0


def test_mixed_fill_and_reject_batch_is_atomic() -> None:
    state = _state()
    valid = _exact_in(intent_id="0x" + "02" * 32, nonce=1, amount_in=100)
    dust = _exact_in(intent_id="0x" + "03" * 32, nonce=2, amount_in=2)
    operations = {"2": [valid, dust]}
    settlement = compute_settlement(
        intents=parse_intents(operations),
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )
    assert [action.value for _intent_id, action in settlement.included_intents] == [
        "FILL",
        "REJECT",
    ]

    root_before = _root(state)
    result = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=operations,
        block_timestamp=1,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.state is None
    assert result.settlement is None
    assert result.error == (
        "settlement contains rejected intent at public DEX boundary: "
        + str(dust["intent_id"])
    )
    assert _root(state) == root_before
    assert state.nonces.get_last(SENDER) == 0
    assert state.balances.get(SENDER, ASSET0) == 10_000
    assert state.balances.get(SENDER, ASSET1) == 10_000
    assert state.pools[POOL_ID].reserve0 == 1_000
    assert state.pools[POOL_ID].reserve1 == 2_000
