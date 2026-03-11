from __future__ import annotations

import pytest

from src.agents.intent_signer import create_swap_intent_from_quote_receipt
from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import RouteHop, RouteLeg, RouteQuote
from src.state.pools import PoolState, PoolStatus


def _mk_pool_cpmm(*, reserve0: int, reserve1: int, fee_bps: int = 0) -> PoolState:
    # asset0 must be lexicographically < asset1 for PoolState invariants.
    return PoolState(
        pool_id="pool_test_0",
        asset0="AGRS",
        asset1="USDC",
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag="CPMM",
        curve_params="",
    )


def test_create_swap_intent_from_quote_receipt_pokayoke_bva_max_action_threshold() -> None:
    # Boundary Value Analysis (BVA) for pokayoke_max_action:
    # - exactly at boundary ("confirm"): should FAIL when the decision is typed_confirm
    # - just above boundary ("typed_confirm"): should PASS for the same receipt
    pool = _mk_pool_cpmm(reserve0=20_000, reserve1=20_000, fee_bps=0)
    pools_by_id = {pool.pool_id: pool}

    amount_in = 101
    amount_out, _ = swap_exact_in_for_pool(pool, reserve_in=pool.reserve0, reserve_out=pool.reserve1, amount_in=amount_in)
    hop = RouteHop(pool_id=pool.pool_id, asset_in="AGRS", asset_out="USDC", amount_in=amount_in, amount_out=amount_out)
    leg = RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=amount_out)
    quote = RouteQuote(asset_in="AGRS", asset_out="USDC", amount_in=amount_in, amount_out=amount_out, legs=(leg,))
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools_by_id)

    with pytest.raises(ValueError, match=r"pokayoke_guardrail:typed_confirm:confirm:mev_conflict"):
        create_swap_intent_from_quote_receipt(
            receipt=receipt,
            pools_by_id=pools_by_id,
            sender_pubkey="pubkey_test_0",
            deadline=123,
            slippage_bps=10,
            pokayoke_max_action="confirm",
        )

    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools_by_id,
        sender_pubkey="pubkey_test_0",
        deadline=123,
        slippage_bps=10,
        pokayoke_max_action="typed_confirm",
    )
    assert intent.kind.value == "SWAP_EXACT_IN"
    assert intent.get_field("pool_id") == pool.pool_id
    assert int(intent.get_field("amount_in")) == int(amount_in)


def test_create_swap_intent_from_quote_receipt_pokayoke_exact_out_unsupported() -> None:
    pool = _mk_pool_cpmm(reserve0=10_000, reserve1=10_000, fee_bps=0)
    pools_by_id = {pool.pool_id: pool}

    amount_out = 50
    amount_in, _ = swap_exact_out_for_pool(pool, reserve_in=pool.reserve0, reserve_out=pool.reserve1, amount_out=amount_out)
    hop = RouteHop(pool_id=pool.pool_id, asset_in="AGRS", asset_out="USDC", amount_in=amount_in, amount_out=amount_out)
    leg = RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=amount_out)
    quote = RouteQuote(asset_in="AGRS", asset_out="USDC", amount_in=amount_in, amount_out=amount_out, legs=(leg,))
    receipt = make_route_quote_receipt(kind="exact_out", quote=quote, pools_by_id=pools_by_id)

    with pytest.raises(ValueError, match=r"pokayoke_exact_out_unsupported: kind='exact_out', pool_id='pool_test_0'"):
        create_swap_intent_from_quote_receipt(
            receipt=receipt,
            pools_by_id=pools_by_id,
            sender_pubkey="pubkey_test_0",
            deadline=123,
            slippage_bps=10,
            pokayoke_max_action="confirm",
        )
