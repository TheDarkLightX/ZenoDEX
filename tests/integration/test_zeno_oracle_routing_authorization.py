from __future__ import annotations

from typing import Any

import pytest

from src.agents.intent_signer import create_swap_intent_from_quote_receipt
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.zeno_oracle_routing_authorization import protected_swap_runtime_facts
from src.state.intents import Intent
from src.state.pools import PoolState, PoolStatus


def _protected_swap_fixture() -> tuple[Intent, dict[str, Any]]:
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=1)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey="0x" + "aa" * 48,
        deadline=9_999_999_999,
        slippage_bps=0,
    )
    return intent, receipt


def test_protected_swap_runtime_facts_rejects_bool_now_epoch() -> None:
    intent, receipt = _protected_swap_fixture()

    with pytest.raises(ValueError, match="^now_epoch must be a non-negative int$"):
        protected_swap_runtime_facts(intent=intent, receipt=receipt, now_epoch=True)


def test_protected_swap_runtime_facts_rejects_numeric_string_now_epoch() -> None:
    intent, receipt = _protected_swap_fixture()

    with pytest.raises(ValueError, match="^now_epoch must be a non-negative int$"):
        protected_swap_runtime_facts(intent=intent, receipt=receipt, now_epoch="42")  # type: ignore[arg-type]
