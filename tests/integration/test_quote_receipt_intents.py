# [TESTER] v1

from __future__ import annotations

import pytest

from src.agents.intent_signer import create_swap_intent_from_quote_receipt, create_swap_intents_from_quote_receipt
from src.core.dex import DexState
from src.core.quote_receipts import make_route_quote_receipt, pool_state_fingerprint
from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import SignedIntentEnvelope, create_intent_operation, create_signed_intent_operation
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def test_create_swap_intent_from_quote_receipt_exact_in_single_hop() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 2000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 1

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        slippage_bps=0,
    )
    assert intent.kind.value == "SWAP_EXACT_IN"
    assert intent.get_field("pool_id") == "p_ab"
    assert intent.get_field("asset_in") == "A"
    assert intent.get_field("asset_out") == "B"
    assert int(intent.get_field("amount_in")) == 123
    assert int(intent.get_field("min_amount_out")) == int(q.amount_out)
    assert intent.get_field("quote_receipt_hash") == receipt["receipt_hash"]
    assert intent.get_field("quote_pool_fingerprint") == pool_state_fingerprint(pools["p_ab"])
    assert int(intent.get_field("quote_receipt_leg_index")) == 0


def test_create_swap_intent_from_quote_receipt_exact_out_single_hop() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 2000, 10),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=321)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 1

    receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey="0x" + "22" * 48,
        deadline=9999999999,
        slippage_bps=0,
    )
    assert intent.kind.value == "SWAP_EXACT_OUT"
    assert int(intent.get_field("amount_out")) == 321
    assert int(intent.get_field("max_amount_in")) == int(q.amount_in)
    assert intent.get_field("quote_receipt_hash") == receipt["receipt_hash"]
    assert intent.get_field("quote_pool_fingerprint") == pool_state_fingerprint(pools["p_ab"])
    assert int(intent.get_field("quote_receipt_leg_index")) == 0


def test_create_swap_intent_from_quote_receipt_rejects_split_receipt() -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)
    assert q is not None
    assert len(q.legs) == 2  # split

    receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools)
    with pytest.raises(
        ValueError,
        match=r"unsupported_multi_leg_receipt: leg_count=2, guidance='use create_swap_intents_from_quote_receipt for split receipts'",
    ):
        create_swap_intent_from_quote_receipt(
            receipt=receipt,
            pools_by_id=pools,
            sender_pubkey="0x" + "33" * 48,
            deadline=9999999999,
            slippage_bps=0,
        )


def test_create_swap_intents_from_quote_receipt_supports_exact_out_split_parallel_pools() -> None:
    pools = {
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)
    assert q is not None
    assert len(q.legs) == 2  # split

    receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey="0x" + "44" * 48,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=7,
    )
    assert len(intents) == 2
    # Deterministic ordering by pool_id + sequential nonces.
    assert [i.get_field("pool_id") for i in intents] == ["p1", "p2"]
    assert [int(i.get_field("nonce")) for i in intents] == [7, 8]
    assert all(i.kind.value == "SWAP_EXACT_OUT" for i in intents)
    # Per-leg amounts must match the quoted split.
    by_pool = {str(i.get_field("pool_id")): i for i in intents}
    leg_index_by_pool = {leg.hops[0].pool_id: idx for idx, leg in enumerate(q.legs)}
    for leg in q.legs:
        hop = leg.hops[0]
        ii = by_pool[hop.pool_id]
        assert int(ii.get_field("amount_out")) == int(hop.amount_out)
        assert int(ii.get_field("max_amount_in")) == int(hop.amount_in)
        assert ii.get_field("quote_receipt_hash") == receipt["receipt_hash"]
        assert ii.get_field("quote_pool_fingerprint") == pool_state_fingerprint(pools[hop.pool_id])
        assert int(ii.get_field("quote_receipt_leg_index")) == leg_index_by_pool[hop.pool_id]


def test_create_swap_intents_from_quote_receipt_supports_exact_in_split_parallel_pools() -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert q is not None
    assert len(q.legs) >= 2  # should split for large trade against identical pools
    assert all(len(leg.hops) == 1 for leg in q.legs)

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey="0x" + "55" * 48,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=100,
    )
    assert len(intents) == len(q.legs)
    assert [int(i.get_field("nonce")) for i in intents] == list(range(100, 100 + len(intents)))
    assert all(i.kind.value == "SWAP_EXACT_IN" for i in intents)
    by_pool = {str(i.get_field("pool_id")): i for i in intents}
    leg_index_by_pool = {leg.hops[0].pool_id: idx for idx, leg in enumerate(q.legs)}
    for leg in q.legs:
        hop = leg.hops[0]
        ii = by_pool[hop.pool_id]
        assert int(ii.get_field("amount_in")) == int(hop.amount_in)
        assert int(ii.get_field("min_amount_out")) == int(hop.amount_out)
        assert ii.get_field("quote_receipt_hash") == receipt["receipt_hash"]
        assert ii.get_field("quote_pool_fingerprint") == pool_state_fingerprint(pools[hop.pool_id])
        assert int(ii.get_field("quote_receipt_leg_index")) == leg_index_by_pool[hop.pool_id]


def test_create_swap_intents_from_quote_receipt_rejects_multi_hop_route_receipt() -> None:
    pools = {
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 2  # multi-hop

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    with pytest.raises(
        ValueError,
        match=r"unsupported_multi_hop_receipt: leg_index=0, hop_count=2, guidance='route-intent execution is not supported yet'",
    ):
        create_swap_intents_from_quote_receipt(
            receipt=receipt,
            pools_by_id=pools,
            sender_pubkey="0x" + "66" * 48,
            deadline=9999999999,
            slippage_bps=0,
            nonce_start=1,
        )


def test_create_swap_intents_from_quote_receipt_rejects_nonce_start_overflow() -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert q is not None
    assert len(q.legs) >= 2

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    with pytest.raises(
        ValueError,
        match=r"nonce_start_range_overflow: nonce_start=4294967295, intent_count=2, max_nonce=4294967295",
    ):
        create_swap_intents_from_quote_receipt(
            receipt=receipt,
            pools_by_id=pools,
            sender_pubkey="0x" + "67" * 48,
            deadline=9999999999,
            slippage_bps=0,
            nonce_start=0xFFFFFFFF,
        )


def test_receipt_derived_intent_rejects_when_pool_snapshot_has_drifted() -> None:
    sender = "0x" + "77" * 48
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 2000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent = intent.with_field("nonce", 1)

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)

    drifted_pool = PoolState(
        pool_id="p_ab",
        asset0="A",
        asset1="B",
        reserve0=1001,
        reserve1=2000,
        fee_bps=10,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    state = DexState(balances=balances, pools={"p_ab": drifted_pool}, lp_balances=LPTable())
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "invalid quote receipt" in res.error
    assert "pool_snapshot_mismatch" in res.error
