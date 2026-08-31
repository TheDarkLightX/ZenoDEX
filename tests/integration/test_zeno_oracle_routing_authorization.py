from __future__ import annotations

from typing import Any

import pytest

from src.agents.intent_signer import create_swap_intent_from_quote_receipt
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.zeno_oracle_routing_authorization import (
    protected_swap_query_id,
    protected_swap_runtime_facts,
)
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


def test_protected_swap_query_id_is_canonical_hash_and_binds_direction() -> None:
    exact_in = protected_swap_query_id(
        kind="exact_in",
        asset_in="A",
        asset_out="B",
    )
    exact_out = protected_swap_query_id(
        kind="exact_out",
        asset_in="A",
        asset_out="B",
    )

    reversed_pair = protected_swap_query_id(
        kind="exact_in",
        asset_in="B",
        asset_out="A",
    )

    assert exact_in == "sha256:9140344cdc2c17c7a608f3d751af0f07cd3e5577cbdf37fc8f1d7b919a9a9ffe"
    assert exact_out == "sha256:8e21b1183b6b8a8f0403a118bae8ab3f505669e6cd2a17527d47af0281039f94"
    assert reversed_pair == "sha256:00c3229d685dc4aeba7dc17f0934da4f45186cd2c73f9ce5385f451de08662bb"


@pytest.mark.parametrize(
    ("kind", "asset_in", "asset_out", "message"),
    [
        ("unknown", "A", "B", "protected swap query kind must be exact_in or exact_out"),
        ("exact_in", "", "B", "protected swap query asset_in must be a non-empty string"),
        ("exact_in", "A", "", "protected swap query asset_out must be a non-empty string"),
        ("exact_in", 7, "B", "protected swap query asset_in must be a non-empty string"),
        ("exact_in", "A", 7, "protected swap query asset_out must be a non-empty string"),
    ],
)
def test_protected_swap_query_id_rejects_noncanonical_components(
    kind: str,
    asset_in: object,
    asset_out: object,
    message: str,
) -> None:
    with pytest.raises(ValueError, match=f"^{message}$"):
        protected_swap_query_id(
            kind=kind,
            asset_in=asset_in,  # type: ignore[arg-type]
            asset_out=asset_out,  # type: ignore[arg-type]
        )
