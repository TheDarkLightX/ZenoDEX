"""
Python/Rust route protocol-fee parity tests.

Verifies that the Python route execution module
(src/core/route_protocol_fee_parity.py) produces identical results to the
Rust ZK proof kernel (zk/state_proof_risc0/shared/src/lib.rs) for route
exact-in and exact-out with per-leg protocol fee capture.

The Rust side is verified by its own unit tests
(route_exact_in_captures_protocol_fee_per_leg,
route_exact_out_captures_protocol_fee_in_input_asset). These tests verify
the Python side produces the same numeric results using the same fixtures.
"""

from __future__ import annotations

import pytest

from src.core.route_protocol_fee_parity import (
    RouteLeg,
    RouteLegHop,
    RouteLegPool,
    execute_route_exact_in,
    execute_route_exact_out,
)

ASSET0 = "0x" + "11" * 32
ASSET1 = "0x" + "22" * 32
ASSET2 = "0x" + "33" * 32
POOL_ID = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686"
CHAIN_POOL = "CHAIN_POOL"
SENDER = "0x" + "aa" * 48
RECIPIENT = "0x" + "bb" * 48
PROTOCOL_FEE_RECIPIENT = "0x" + "ee" * 48

BPS_DENOM = 10_000


def _ceil_div(n: int, d: int) -> int:
    return (n + d - 1) // d


def _two_pool_chain() -> dict[str, RouteLegPool]:
    """Two-pool chain matching Rust `chained_two_pool_snapshot` exactly.

    Rust fixtures (zk/state_proof_risc0/shared/src/lib.rs):
    - POOL_ID: ASSET0/ASSET1, 1_000_000/1_000_000, fee_bps=30
    - CHAIN_POOL: ASSET1/ASSET2, 1_500_000/3_000_000, fee_bps=100
    """
    return {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        ),
        CHAIN_POOL: RouteLegPool(
            pool_id=CHAIN_POOL,
            asset0=ASSET1,
            asset1=ASSET2,
            reserve0=1_500_000,
            reserve1=3_000_000,
            fee_bps=100,
        ),
    }


def _single_pool() -> dict[str, RouteLegPool]:
    return {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        ),
    }


def _two_leg_route() -> list[RouteLeg]:
    return [
        RouteLeg(hops=(RouteLegHop(pool_id=POOL_ID),)),
        RouteLeg(hops=(RouteLegHop(pool_id=CHAIN_POOL),)),
    ]


def _single_leg_route() -> list[RouteLeg]:
    return [RouteLeg(hops=(RouteLegHop(pool_id=POOL_ID),))]


# ---------------------------------------------------------------------------
# Route exact-in parity
# ---------------------------------------------------------------------------


def test_route_exact_in_no_fee_matches_rust_no_fee() -> None:
    """With share_bps=0, route exact-in produces same output as Rust no-fee."""
    pools = _two_pool_chain()
    total_amount_in = 100_000

    result = execute_route_exact_in(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_in=total_amount_in,
        total_min_amount_out=0,
        protocol_fee_share_bps=0,
        protocol_fee_recipient=None,
    )

    # Compute expected values using the same formulas as the Rust test
    first_pool = pools[POOL_ID]
    second_pool = pools[CHAIN_POOL]
    first_fee = _ceil_div(total_amount_in * first_pool.fee_bps, BPS_DENOM)
    first_net_in = total_amount_in - first_fee
    first_out = (first_pool.reserve1 * first_net_in) // (
        first_pool.reserve0 + first_net_in
    )
    second_fee = _ceil_div(first_out * second_pool.fee_bps, BPS_DENOM)
    second_net_in = first_out - second_fee
    second_out = (second_pool.reserve1 * second_net_in) // (
        second_pool.reserve0 + second_net_in
    )

    assert result.sender_debit == total_amount_in
    assert result.recipient_credit == second_out
    assert len(result.leg_results) == 2
    assert result.leg_results[0].amount_out == first_out
    assert result.leg_results[1].amount_out == second_out
    assert result.leg_results[0].protocol_fee == 0
    assert result.leg_results[1].protocol_fee == 0
    assert result.fee_credits == {}


def test_route_exact_in_captures_protocol_fee_per_leg() -> None:
    """Python route exact-in per-leg fee matches Rust test fixture exactly."""
    pools = _two_pool_chain()
    total_amount_in = 100_000
    share_bps = 5_000

    result = execute_route_exact_in(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_in=total_amount_in,
        total_min_amount_out=0,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
    )

    # Compute expected values using the same formulas as the Rust test
    first_pool = pools[POOL_ID]
    second_pool = pools[CHAIN_POOL]
    first_fee = _ceil_div(total_amount_in * first_pool.fee_bps, BPS_DENOM)
    first_protocol_fee = (first_fee * share_bps) // BPS_DENOM
    first_net_in = total_amount_in - first_fee
    first_out = (first_pool.reserve1 * first_net_in) // (
        first_pool.reserve0 + first_net_in
    )
    second_fee = _ceil_div(first_out * second_pool.fee_bps, BPS_DENOM)
    second_protocol_fee = (second_fee * share_bps) // BPS_DENOM
    second_net_in = first_out - second_fee
    second_out = (second_pool.reserve1 * second_net_in) // (
        second_pool.reserve0 + second_net_in
    )

    # Sender debited total_amount_in
    assert result.sender_debit == total_amount_in

    # Recipient gets second_out
    assert result.recipient_credit == second_out

    # Protocol fee credited in each leg's input asset
    assert result.fee_credits[(PROTOCOL_FEE_RECIPIENT, ASSET0)] == first_protocol_fee
    assert result.fee_credits[(PROTOCOL_FEE_RECIPIENT, ASSET1)] == second_protocol_fee

    # Pool reserves match Rust test assertions
    assert result.pool_updates[POOL_ID] == (
        first_pool.reserve0 + total_amount_in - first_protocol_fee,
        first_pool.reserve1 - first_out,
    )
    assert result.pool_updates[CHAIN_POOL] == (
        second_pool.reserve0 + first_out - second_protocol_fee,
        second_pool.reserve1 - second_out,
    )

    # Per-leg results
    assert result.leg_results[0].protocol_fee == first_protocol_fee
    assert result.leg_results[1].protocol_fee == second_protocol_fee
    assert result.leg_results[0].reserve_in_delta == total_amount_in - first_protocol_fee
    assert result.leg_results[1].reserve_in_delta == first_out - second_protocol_fee


def test_route_exact_in_rejects_nonzero_fee_without_recipient() -> None:
    """Fail-closed: nonzero share_bps without recipient raises."""
    with pytest.raises(ValueError, match="protocol_fee_recipient required"):
        execute_route_exact_in(
            pools=_two_pool_chain(),
            legs=_two_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient=None,
        )


def test_route_exact_in_rejects_whitespace_recipient() -> None:
    """Fail-closed: whitespace-only recipient raises (matches Rust trim check)."""
    with pytest.raises(ValueError, match="protocol_fee_recipient required"):
        execute_route_exact_in(
            pools=_two_pool_chain(),
            legs=_two_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient="   ",
        )


def test_route_exact_in_rejects_oversized_share_before_recipient() -> None:
    """Reject precedence: range check fires before recipient check (matches Rust)."""
    with pytest.raises(ValueError, match="protocol_fee_share_bps must be in"):
        execute_route_exact_in(
            pools=_two_pool_chain(),
            legs=_two_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=20_000,
            protocol_fee_recipient=None,
        )


def test_route_exact_in_min_output_rejects() -> None:
    """Min output not met raises ValueError."""
    pools = _two_pool_chain()
    result = execute_route_exact_in(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_in=100_000,
        total_min_amount_out=0,
    )
    with pytest.raises(ValueError, match="total_min_amount_out not met"):
        execute_route_exact_in(
            pools=pools,
            legs=_two_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_in=100_000,
            total_min_amount_out=result.recipient_credit + 1,
        )


# ---------------------------------------------------------------------------
# Route exact-out parity
# ---------------------------------------------------------------------------


def test_route_exact_out_captures_protocol_fee_in_input_asset() -> None:
    """Python route exact-out per-leg fee matches Rust test fixture exactly."""
    pools = _single_pool()
    total_amount_out = 10_000
    total_max_amount_in = 100_000
    share_bps = 5_000

    result = execute_route_exact_out(
        pools=pools,
        legs=_single_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET1,
        total_amount_out=total_amount_out,
        total_max_amount_in=total_max_amount_in,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
    )

    # Compute expected values using the same formulas as the Rust test
    pool = pools[POOL_ID]
    net_in = _ceil_div(
        pool.reserve0 * total_amount_out,
        pool.reserve1 - total_amount_out,
    )
    gross_in = _ceil_div(net_in * BPS_DENOM, BPS_DENOM - pool.fee_bps)
    fee_total = gross_in - net_in
    protocol_fee = (fee_total * share_bps) // BPS_DENOM

    # Sender debited gross_in
    assert result.sender_debit == gross_in

    # Recipient gets exactly total_amount_out
    assert result.recipient_credit == total_amount_out

    # Protocol fee credited in input asset
    assert result.fee_credits[(PROTOCOL_FEE_RECIPIENT, ASSET0)] == protocol_fee

    # Pool reserves match Rust test assertions
    assert result.pool_updates[POOL_ID] == (
        pool.reserve0 + gross_in - protocol_fee,
        pool.reserve1 - total_amount_out,
    )

    # Per-leg results
    assert result.leg_results[0].protocol_fee == protocol_fee
    assert result.leg_results[0].reserve_in_delta == gross_in - protocol_fee


def test_route_exact_out_no_fee_matches_rust_no_fee() -> None:
    """With share_bps=0, route exact-out produces same output as Rust no-fee."""
    pools = _single_pool()
    total_amount_out = 10_000

    result = execute_route_exact_out(
        pools=pools,
        legs=_single_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET1,
        total_amount_out=total_amount_out,
        total_max_amount_in=100_000,
        protocol_fee_share_bps=0,
        protocol_fee_recipient=None,
    )

    pool = pools[POOL_ID]
    net_in = _ceil_div(
        pool.reserve0 * total_amount_out,
        pool.reserve1 - total_amount_out,
    )
    gross_in = _ceil_div(net_in * BPS_DENOM, BPS_DENOM - pool.fee_bps)

    assert result.sender_debit == gross_in
    assert result.recipient_credit == total_amount_out
    assert result.leg_results[0].protocol_fee == 0
    assert result.fee_credits == {}


def test_route_exact_out_rejects_nonzero_fee_without_recipient() -> None:
    """Fail-closed: nonzero share_bps without recipient raises."""
    with pytest.raises(ValueError, match="protocol_fee_recipient required"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=10_000,
            total_max_amount_in=100_000,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient=None,
        )


def test_route_exact_out_rejects_whitespace_recipient() -> None:
    """Fail-closed: whitespace-only recipient raises (matches Rust trim check)."""
    with pytest.raises(ValueError, match="protocol_fee_recipient required"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=10_000,
            total_max_amount_in=100_000,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient="   ",
        )


def test_route_exact_out_rejects_oversized_share_before_recipient() -> None:
    """Reject precedence: range check fires before recipient check (matches Rust)."""
    with pytest.raises(ValueError, match="protocol_fee_share_bps must be in"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=10_000,
            total_max_amount_in=100_000,
            protocol_fee_share_bps=20_000,
            protocol_fee_recipient=None,
        )


def test_route_exact_out_max_input_rejects() -> None:
    """Max input exceeded raises ValueError."""
    pools = _single_pool()
    pool = pools[POOL_ID]
    net_in = _ceil_div(pool.reserve0 * 10_000, pool.reserve1 - 10_000)
    gross_in = _ceil_div(net_in * BPS_DENOM, BPS_DENOM - pool.fee_bps)

    with pytest.raises(ValueError, match="total_max_amount_in exceeded"):
        execute_route_exact_out(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=10_000,
            total_max_amount_in=gross_in - 1,
        )


# ---------------------------------------------------------------------------
# Conservation invariant checks
# ---------------------------------------------------------------------------


def test_route_exact_in_conservation_holds() -> None:
    """Verify route exact-in conservation equations."""
    pools = _two_pool_chain()
    share_bps = 5_000

    result = execute_route_exact_in(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_in=100_000,
        total_min_amount_out=0,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
    )

    # first_leg.reserve_in_delta + first_leg.protocol_fee == sender_debit
    leg0 = result.leg_results[0]
    assert leg0.reserve_in_delta + leg0.protocol_fee == result.sender_debit

    # leg_i.reserve_out_delta == leg_{i+1}.reserve_in_delta + leg_{i+1}.protocol_fee
    leg1 = result.leg_results[1]
    assert leg0.reserve_out_delta == leg1.reserve_in_delta + leg1.protocol_fee

    # last_leg.reserve_out_delta == recipient_credit
    assert leg1.reserve_out_delta == result.recipient_credit

    # Total fee credits sum to sum of per-leg protocol fees
    total_fee = sum(leg.protocol_fee for leg in result.leg_results)
    total_credit = sum(result.fee_credits.values())
    assert total_fee == total_credit


def test_route_exact_out_conservation_holds() -> None:
    """Verify route exact-out conservation equations.

    For exact-out, reserve_out_delta == target_out (not amount_out).
    Rounded overdelivery (amount_out - target_out) stays in pool reserves.
    The chain equation is:
        leg_i.reserve_out_delta == leg_{i+1}.reserve_in_delta + leg_{i+1}.protocol_fee
    """
    pools = _two_pool_chain()
    share_bps = 3_000
    total_amount_out = 5_000

    result = execute_route_exact_out(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_out=total_amount_out,
        total_max_amount_in=1_000_000,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
    )

    # first_leg.reserve_in_delta + first_leg.protocol_fee == sender_debit
    leg0 = result.leg_results[0]
    assert leg0.reserve_in_delta + leg0.protocol_fee == result.sender_debit

    # leg_i.reserve_out_delta == leg_{i+1}.reserve_in_delta + leg_{i+1}.protocol_fee
    leg1 = result.leg_results[1]
    assert leg0.reserve_out_delta == leg1.reserve_in_delta + leg1.protocol_fee

    # last_leg.reserve_out_delta == recipient_credit (exact target)
    assert leg1.reserve_out_delta == result.recipient_credit

    # Overdelivery: amount_out >= target_out (reserve_out_delta)
    for leg in result.leg_results:
        assert leg.amount_out >= leg.reserve_out_delta

    # Total fee credits sum to sum of per-leg protocol fees
    total_fee = sum(leg.protocol_fee for leg in result.leg_results)
    total_credit = sum(result.fee_credits.values())
    assert total_fee == total_credit


def test_route_exact_in_k_invariant_holds_per_leg() -> None:
    """Verify k-invariant holds for every pool after route exact-in."""
    pools = _two_pool_chain()
    share_bps = 5_000

    result = execute_route_exact_in(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_in=100_000,
        total_min_amount_out=0,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
    )

    for leg in result.leg_results:
        pool = pools[leg.pool_id]
        k_before = pool.reserve0 * pool.reserve1
        new_r0, new_r1 = result.pool_updates[leg.pool_id]
        k_after = new_r0 * new_r1
        assert k_after >= k_before, f"k-invariant violated for pool {leg.pool_id}"


def test_route_exact_out_k_invariant_holds_per_leg() -> None:
    """Verify k-invariant holds for every pool after route exact-out."""
    pools = _two_pool_chain()
    share_bps = 3_000

    result = execute_route_exact_out(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_out=5_000,
        total_max_amount_in=1_000_000,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
    )

    for leg in result.leg_results:
        pool = pools[leg.pool_id]
        k_before = pool.reserve0 * pool.reserve1
        new_r0, new_r1 = result.pool_updates[leg.pool_id]
        k_after = new_r0 * new_r1
        assert k_after >= k_before, f"k-invariant violated for pool {leg.pool_id}"


# ---------------------------------------------------------------------------
# Route envelope validation (matching Rust kernel rejects)
# ---------------------------------------------------------------------------


def test_route_rejects_empty_legs() -> None:
    """Empty route legs raises ValueError."""
    with pytest.raises(ValueError, match="at least one leg"):
        execute_route_exact_in(
            pools=_two_pool_chain(),
            legs=[],
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_multihop_leg() -> None:
    """Leg with more than one hop raises ValueError (proof v1)."""
    with pytest.raises(ValueError, match="exactly one hop"):
        execute_route_exact_in(
            pools=_two_pool_chain(),
            legs=[RouteLeg(hops=(RouteLegHop(POOL_ID), RouteLegHop(CHAIN_POOL)))],
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_duplicate_pool_ids() -> None:
    """Duplicate pool ids across legs raises ValueError."""
    with pytest.raises(ValueError, match="duplicate pool_id"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=[
                RouteLeg(hops=(RouteLegHop(POOL_ID),)),
                RouteLeg(hops=(RouteLegHop(POOL_ID),)),
            ],
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_pool_not_found() -> None:
    """Non-existent pool id raises ValueError."""
    with pytest.raises(ValueError, match="pool not found"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=[RouteLeg(hops=(RouteLegHop("NONEXISTENT_POOL"),))],
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_inactive_pool() -> None:
    """Inactive pool raises ValueError."""
    pools = {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
            status="FROZEN",
        ),
    }
    with pytest.raises(ValueError, match="pool not active"):
        execute_route_exact_in(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_exact_out_rejects_empty_legs() -> None:
    """Empty route legs raises ValueError for exact-out too."""
    with pytest.raises(ValueError, match="at least one leg"):
        execute_route_exact_out(
            pools=_two_pool_chain(),
            legs=[],
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_out=5_000,
            total_max_amount_in=1_000_000,
        )


def test_route_exact_out_rejects_duplicate_pool_ids() -> None:
    """Duplicate pool ids across legs raises ValueError for exact-out too."""
    with pytest.raises(ValueError, match="duplicate pool_id"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=[
                RouteLeg(hops=(RouteLegHop(POOL_ID),)),
                RouteLeg(hops=(RouteLegHop(POOL_ID),)),
            ],
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=5_000,
            total_max_amount_in=1_000_000,
        )
