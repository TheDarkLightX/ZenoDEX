from __future__ import annotations

from src.core.amm_dispatch import swap_exact_in_for_pool
from src.core.quote_receipts import make_route_quote_receipt, verify_route_quote_receipt
from src.core.quote_receipts import pool_state_fingerprint, receipt_hash
from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop
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


def test_quote_receipt_exact_in_roundtrip() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 10),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 10),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 10),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=120)
    assert q is not None

    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err

    # Receipt hash should be deterministic across dict ordering.
    pools_flipped = dict(reversed(list(pools.items())))
    receipt2 = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools_flipped)
    assert receipt2["receipt_hash"] == receipt["receipt_hash"]

    # Mutate a pool snapshot: verification should fail-closed.
    pools_mut = dict(pools)
    p_ab = pools_mut["p_ab"]
    pools_mut["p_ab"] = PoolState(
        pool_id=p_ab.pool_id,
        asset0=p_ab.asset0,
        asset1=p_ab.asset1,
        reserve0=int(p_ab.reserve0) + 1,
        reserve1=int(p_ab.reserve1),
        fee_bps=int(p_ab.fee_bps),
        lp_supply=int(p_ab.lp_supply),
        status=p_ab.status,
        created_at=int(p_ab.created_at),
        curve_tag=p_ab.curve_tag,
        curve_params=p_ab.curve_params,
    )
    ok2, err2 = verify_route_quote_receipt(receipt, pools_by_id=pools_mut)
    assert not ok2
    assert err2 in {"pool_snapshot_mismatch", "hop_quote_mismatch", "hop_quote_error"}


def test_quote_receipt_exact_out_split_roundtrip() -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)
    assert q is not None
    assert len(q.legs) == 2

    receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok, err


def test_quote_receipt_verifier_rejects_missing_pool_fingerprint_for_hop() -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)
    assert q is not None
    assert len(q.legs) == 2

    receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools)
    # Attacker-style mutation: remove a hop's pool fingerprint but keep hash consistent.
    body = dict(receipt["body"])
    pools_map = dict(body["pools"])
    pools_map.pop("p2")
    body["pools"] = pools_map
    receipt2 = {"body": body, "receipt_hash": receipt_hash(body)}

    ok, err = verify_route_quote_receipt(receipt2, pools_by_id=pools)
    assert not ok
    assert err == "missing_pool_fingerprint"


def test_quote_receipt_verifier_rejects_asset_chain_mismatch() -> None:
    # Build a receipt that is numerically consistent hop-by-hop but semantically invalid
    # because the asset chain is broken between hops.
    pools = {
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_db": _pool("p_db", "D", "B", 1000, 1000, 0),
    }
    p_ac = pools["p_ac"]
    p_db = pools["p_db"]

    amt_in = 100
    out_ac, _ = swap_exact_in_for_pool(p_ac, reserve_in=int(p_ac.reserve0), reserve_out=int(p_ac.reserve1), amount_in=amt_in)
    # p_db has canonical ordering (B < D), but the hop we want is D -> B.
    out_db, _ = swap_exact_in_for_pool(p_db, reserve_in=int(p_db.reserve1), reserve_out=int(p_db.reserve0), amount_in=int(out_ac))

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": int(amt_in),
        "amount_out": int(out_db),
        "legs": [
            {
                "amount_in": int(amt_in),
                "amount_out": int(out_db),
                "hops": [
                    {
                        "pool_id": "p_ac",
                        "asset_in": "A",
                        "asset_out": "C",
                        "amount_in": int(amt_in),
                        "amount_out": int(out_ac),
                    },
                    {
                        "pool_id": "p_db",
                        "asset_in": "D",  # breaks the A->C->B chain (should be C)
                        "asset_out": "B",
                        "amount_in": int(out_ac),
                        "amount_out": int(out_db),
                    },
                ],
            }
        ],
        "pools": {
            "p_ac": pool_state_fingerprint(p_ac),
            "p_db": pool_state_fingerprint(p_db),
        },
    }
    receipt = {"body": body, "receipt_hash": receipt_hash(body)}
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert not ok
    assert err == "hop_asset_chain_mismatch"
