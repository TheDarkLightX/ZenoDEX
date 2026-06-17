from __future__ import annotations

from src.integration.exact_in_route_certificate import (
    build_exact_in_route_guarded_quote_packet,
    verify_exact_in_route_guarded_quote_packet_payload,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=r0,
        reserve1=r1,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def test_exact_in_route_guarded_packet_accepts_staircase_exact_profile() -> None:
    pools = {
        "p_ab_0": _pool("p_ab_0", 87, 80, 75),
        "p_ab_1": _pool("p_ab_1", 46, 66, 11),
    }

    packet = build_exact_in_route_guarded_quote_packet(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=4_999,
        split_search_profile="staircase_exact",
        enable_mixed_direct_twohop_split=True,
    )
    payload = packet.to_dict()

    assert packet.guard_ok is True
    assert payload["contract"]["split_search_profile"] == "staircase_exact"
    ok, err = verify_exact_in_route_guarded_quote_packet_payload(payload)
    assert ok is True
    assert err is None
