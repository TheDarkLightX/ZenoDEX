from __future__ import annotations

import pytest

from src.core.dex import DexState
from src.integration import zusd_monetary_bridge as bridge
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    apply_zusd_monetary_ops,
)
from src.state import BalanceTable, LPTable

SENDER = "0x" + "11" * 48


def _state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def test_monetary_bridge_still_rejects_domain_errors() -> None:
    result = apply_zusd_monetary_ops(
        config=ZUSDMonetaryConfig(),
        state=_state(),
        zusd_state=None,
        operations=[
            {
                "action": "deposit_collateral",
                "nonce": 1,
                "amount_e8": 1,
            }
        ],
        tx_sender_pubkey=SENDER,
        block_timestamp=0,
    )

    assert result.ok is False
    assert result.error == "zusd op[0] insufficient native collateral balance"


def test_monetary_bridge_propagates_unexpected_apply_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def _boom(**_kwargs: object) -> object:
        raise RuntimeError("bridge implementation fault")

    monkeypatch.setattr(bridge, "_apply_one", _boom)

    with pytest.raises(RuntimeError, match="bridge implementation fault"):
        apply_zusd_monetary_ops(
            config=ZUSDMonetaryConfig(),
            state=_state(),
            zusd_state=None,
            operations=[
                {
                    "action": "advance_epoch",
                    "nonce": 1,
                    "delta": 1,
                }
            ],
            tx_sender_pubkey=SENDER,
            block_timestamp=0,
        )
