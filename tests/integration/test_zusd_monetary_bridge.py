from __future__ import annotations

import pytest

from src.core.dex import DexState
from src.integration import zusd_monetary_bridge
from src.integration.zusd_monetary_bridge import ZUSDMonetaryConfig, apply_zusd_monetary_ops
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _op(action: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "ZUSDFinance",
        "version": "0.1",
        "action": action,
        "nonce": 1,
    }
    op.update(kwargs)
    return op


def test_apply_zusd_monetary_ops_labels_internal_step_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    def _faulting_apply_one(**_kwargs: object) -> object:
        raise RuntimeError("internal repayment index leaked")

    monkeypatch.setattr(zusd_monetary_bridge, "_apply_one", _faulting_apply_one)

    result = apply_zusd_monetary_ops(
        config=ZUSDMonetaryConfig(),
        state=_state(),
        zusd_state=None,
        operations=[_op("advance_epoch", delta=1)],
        tx_sender_pubkey="aa" * 48,
        block_timestamp=0,
    )

    assert result.ok is False
    assert result.error == "zusd op[0] internal error: RuntimeError"
    assert "internal repayment index leaked" not in str(result.error)
