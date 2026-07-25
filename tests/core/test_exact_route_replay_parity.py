from __future__ import annotations

import pytest

from src.core.quote_receipts import make_route_quote_receipt
from src.core.route_settlement import (
    ROUTE_REJECT_POOL_NOT_ACTIVE,
    ROUTE_REJECT_POOL_NOT_FOUND,
    ROUTE_REJECT_POOL_STATE_DRIFT,
    RouteBinding,
    replay_route_legs,
    replay_route_legs_committed_v1,
    resolve_route_binding_from_receipt,
    route_binding_pins_committed_snapshot_v1,
    route_binding_pins_snapshot,
)
from src.core.routing import best_route_exact_in_2hop
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshots import snapshot_pool_map

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _pool(
    fee_bps: int,
    *,
    reserve0: int = 1_000_000,
    reserve1: int = 1_000_000,
    status: PoolStatus = PoolStatus.ACTIVE,
) -> PoolState:
    pool_id = compute_pool_id(ASSET0, ASSET1, fee_bps)
    return PoolState(
        pool_id=pool_id,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1_000_000,
        status=status,
        created_at=0,
    )


def _pools() -> dict[str, PoolState]:
    pools = (_pool(10), _pool(30))
    return {pool.pool_id: pool for pool in pools}


def _binding_for(pools: dict[str, PoolState]) -> RouteBinding:
    quote = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_in=10_000,
    )
    assert quote is not None
    receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=quote,
        pools_by_id=pools,
    )
    binding, error = resolve_route_binding_from_receipt(receipt)
    assert binding is not None, error
    return binding


def test_exact_route_replay_and_snapshot_pin_match_legacy() -> None:
    pools = _pools()
    binding = _binding_for(pools)
    committed = snapshot_pool_map(pools)

    assert replay_route_legs_committed_v1(
        binding=binding,
        pools=committed,
    ) == replay_route_legs(binding=binding, pools=pools)
    assert route_binding_pins_committed_snapshot_v1(binding, committed)
    assert route_binding_pins_snapshot(binding, pools)


def test_exact_route_replay_rejection_precedence_matches_legacy() -> None:
    pools = _pools()
    binding = _binding_for(pools)
    pool_ids = sorted(pools)

    cases = (
        (
            {pool_ids[1]: pools[pool_ids[1]]},
            ROUTE_REJECT_POOL_NOT_FOUND,
        ),
        (
            {
                **pools,
                pool_ids[0]: _pool(
                    pools[pool_ids[0]].fee_bps,
                    status=PoolStatus.FROZEN,
                ),
            },
            ROUTE_REJECT_POOL_NOT_ACTIVE,
        ),
        (
            {
                **pools,
                pool_ids[0]: _pool(
                    pools[pool_ids[0]].fee_bps,
                    reserve0=pools[pool_ids[0]].reserve0 + 1,
                ),
            },
            ROUTE_REJECT_POOL_STATE_DRIFT,
        ),
    )

    for current_pools, expected_reason in cases:
        legacy = replay_route_legs(binding=binding, pools=current_pools)
        exact = replay_route_legs_committed_v1(
            binding=binding,
            pools=snapshot_pool_map(current_pools),
        )
        assert legacy == exact
        assert exact.reject_reason == expected_reason


def test_fingerprint_map_insertion_order_cannot_choose_the_rejection() -> None:
    pools = _pools()
    binding = _binding_for(pools)
    low_id, high_id = sorted(pools)
    current = {
        high_id: _pool(
            pools[high_id].fee_bps,
            status=PoolStatus.FROZEN,
        )
    }
    forward = RouteBinding(
        kind=binding.kind,
        asset_in=binding.asset_in,
        asset_out=binding.asset_out,
        total_amount_in=binding.total_amount_in,
        total_amount_out=binding.total_amount_out,
        legs=binding.legs,
        pool_fingerprints={
            low_id: binding.pool_fingerprints[low_id],
            high_id: binding.pool_fingerprints[high_id],
        },
    )
    reverse = RouteBinding(
        kind=binding.kind,
        asset_in=binding.asset_in,
        asset_out=binding.asset_out,
        total_amount_in=binding.total_amount_in,
        total_amount_out=binding.total_amount_out,
        legs=binding.legs,
        pool_fingerprints={
            high_id: binding.pool_fingerprints[high_id],
            low_id: binding.pool_fingerprints[low_id],
        },
    )

    assert (
        replay_route_legs(
            binding=forward,
            pools=current,
        ).reject_reason
        == ROUTE_REJECT_POOL_NOT_FOUND
    )
    assert (
        replay_route_legs(
            binding=reverse,
            pools=current,
        ).reject_reason
        == ROUTE_REJECT_POOL_NOT_FOUND
    )


def test_exact_route_replay_rejects_a_plain_mapping_boundary() -> None:
    pools = _pools()
    binding = _binding_for(pools)

    with pytest.raises(TypeError, match="exact committed pool map"):
        replay_route_legs_committed_v1(  # type: ignore[arg-type]
            binding=binding,
            pools=pools,
        )
