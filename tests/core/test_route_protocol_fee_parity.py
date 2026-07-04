"""
Python route protocol-fee parity tests.

Verifies that the Python route execution module
(src/core/route_protocol_fee_parity.py) mirrors the Rust ZK proof kernel's
(zk/state_proof_risc0/shared/src/lib.rs) route arithmetic/accounting path
for exact-in and exact-out with per-leg protocol fee capture.

The Rust side is verified by its own unit tests. The Python helper is a
subset of the Rust transition (it does not cover Rust-only envelope checks
like leg_indices or quote_receipt_hash). The pinned regression corpus is
Python-generated, not a mechanical Rust/Python differential corpus. These
tests verify the Python side produces correct numeric results using the
same formula structure as Rust, plus boundary, type-validation, and
overflow-rejection coverage.
"""

from __future__ import annotations

import json
import os

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
    with pytest.raises(ValueError, match="protocol_fee_recipient must not be blank"):
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


def test_route_exact_in_rejects_bytes_recipient() -> None:
    """Fail-closed: bytes recipient raises (Rust rejects non-string at context parsing)."""
    with pytest.raises(ValueError, match="protocol_fee_recipient must be a string"):
        execute_route_exact_in(
            pools=_two_pool_chain(),
            legs=_two_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET2,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient=b"0xbbbb",  # type: ignore[arg-type]
        )


def test_route_exact_out_rejects_bytes_recipient() -> None:
    """Fail-closed: bytes recipient raises for exact-out too."""
    with pytest.raises(ValueError, match="protocol_fee_recipient must be a string"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=500,
            total_max_amount_in=1_000_000,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient=b"0xbbbb",  # type: ignore[arg-type]
        )


def test_route_exact_in_rejects_bytes_recipient_zero_share() -> None:
    """Fail-closed: bytes recipient rejected even when share=0 (Rust rejects at parse)."""
    with pytest.raises(ValueError, match="protocol_fee_recipient must be a string"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=0,
            protocol_fee_recipient=b"0xbbbb",  # type: ignore[arg-type]
        )


def test_route_exact_out_rejects_int_recipient_zero_share() -> None:
    """Fail-closed: int recipient rejected even when share=0."""
    with pytest.raises(ValueError, match="protocol_fee_recipient must be a string"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=500,
            total_max_amount_in=1_000_000,
            protocol_fee_share_bps=0,
            protocol_fee_recipient=12345,  # type: ignore[arg-type]
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
    with pytest.raises(ValueError, match="protocol_fee_recipient must not be blank"):
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


# ---------------------------------------------------------------------------
# String boundary validation: pool_id, asset0, asset1, hop pool_id, asset_in/out
# ---------------------------------------------------------------------------


def test_pool_rejects_non_string_pool_id() -> None:
    """Non-string pool_id raises ValueError (Rust JSON parsing is string-only)."""
    with pytest.raises(ValueError, match="pool_id must be a string"):
        RouteLegPool(
            pool_id=99,  # type: ignore[arg-type]
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_pool_rejects_non_string_asset0() -> None:
    """Non-string asset0 raises ValueError."""
    with pytest.raises(ValueError, match="asset0 must be a string"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=1,  # type: ignore[arg-type]
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_pool_rejects_non_string_asset1() -> None:
    """Non-string asset1 raises ValueError."""
    with pytest.raises(ValueError, match="asset1 must be a string"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=2,  # type: ignore[arg-type]
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_hop_rejects_non_string_pool_id() -> None:
    """Non-string hop pool_id raises ValueError."""
    with pytest.raises(ValueError, match="hop pool_id must be a string"):
        RouteLegHop(pool_id=99)  # type: ignore[arg-type]


def test_route_exact_in_rejects_non_string_asset_in() -> None:
    """Non-string asset_in raises ValueError."""
    with pytest.raises(ValueError, match="asset_in must be a string"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=1,  # type: ignore[arg-type]
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_exact_in_rejects_non_string_asset_out() -> None:
    """Non-string asset_out raises ValueError."""
    with pytest.raises(ValueError, match="asset_out must be a string"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=2,  # type: ignore[arg-type]
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


# ---------------------------------------------------------------------------
# Domain validation: malformed states outside Rust u128 domain
# ---------------------------------------------------------------------------


def test_pool_rejects_negative_reserve0() -> None:
    """Negative reserve0 raises ValueError (Rust u128 cannot represent)."""
    with pytest.raises(ValueError, match="reserve0 must be non-negative"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=-1,
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_pool_rejects_negative_reserve1() -> None:
    """Negative reserve1 raises ValueError (Rust u128 cannot represent)."""
    with pytest.raises(ValueError, match="reserve1 must be non-negative"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=-100,
            fee_bps=30,
        )


def test_pool_rejects_u128_overflow_reserve() -> None:
    """Reserve exceeding u128 max raises ValueError."""
    with pytest.raises(ValueError, match="exceeds u128 max"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=(1 << 128),
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_pool_rejects_negative_fee_bps() -> None:
    """Negative fee_bps raises ValueError (u128 domain check fires first)."""
    with pytest.raises(ValueError, match="fee_bps must be non-negative"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=-1,
        )


def test_pool_rejects_oversized_fee_bps() -> None:
    """fee_bps > 10000 raises ValueError."""
    with pytest.raises(ValueError, match="fee_bps must be in"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=10_001,
        )


def test_pool_rejects_float_reserve() -> None:
    """Float reserve raises ValueError (Rust u128 rejects non-integer JSON)."""
    with pytest.raises(ValueError, match="must be an integer"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000.5,  # type: ignore[arg-type]
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_pool_rejects_float_fee_bps() -> None:
    """Float fee_bps raises ValueError (Rust rejects non-integer)."""
    with pytest.raises(ValueError, match="must be an integer"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30.5,  # type: ignore[arg-type]
        )


def test_route_exact_in_rejects_float_amount_in() -> None:
    """Float total_amount_in raises ValueError (Rust rejects non-integer)."""
    with pytest.raises(ValueError, match="must be an integer"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000.5,  # type: ignore[arg-type]
            total_min_amount_out=0,
        )


def test_route_exact_in_rejects_float_protocol_fee_share_bps() -> None:
    """Float protocol_fee_share_bps raises ValueError (Rust u32 rejects floats)."""
    with pytest.raises(ValueError, match="must be an integer"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=5000.5,  # type: ignore[arg-type]
            protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
        )


def test_route_exact_in_rejects_bool_protocol_fee_share_bps() -> None:
    """Bool protocol_fee_share_bps raises ValueError (Python bool is int subclass but semantically wrong)."""
    with pytest.raises(ValueError, match="must be an integer"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=True,  # bool is int subclass; runtime rejects via type() is not int
            protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
        )


def test_route_exact_out_rejects_float_protocol_fee_share_bps() -> None:
    """Float protocol_fee_share_bps raises ValueError for exact-out too."""
    with pytest.raises(ValueError, match="must be an integer"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=500,
            total_max_amount_in=1_000_000,
            protocol_fee_share_bps=5000.5,  # type: ignore[arg-type]
            protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
        )


def test_route_exact_in_rejects_intermediate_mul_overflow() -> None:
    """Intermediate multiplication overflow raises ValueError.

    With reserve0=U128_MAX, reserve1=U128_MAX, fee_bps=0, total_amount_in=2:
      amount_out numerator = reserve_out * net_in = U128_MAX * 2 > u128.
    Rust rejects via checked arithmetic; Python must too.
    """
    from src.core.route_protocol_fee_parity import U128_MAX
    pools = {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=U128_MAX,
            reserve1=U128_MAX,
            fee_bps=0,
        ),
    }
    with pytest.raises(ValueError, match="exceeds u128 max"):
        execute_route_exact_in(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=2,
            total_min_amount_out=0,
        )


def test_route_exact_in_rejects_denom_add_overflow() -> None:
    """Denominator addition overflow raises ValueError.

    With reserve_in=U128_MAX, net_in=1: denom = U128_MAX + 1 > u128.
    """
    from src.core.route_protocol_fee_parity import U128_MAX
    pools = {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=U128_MAX,
            reserve1=1_000_000,
            fee_bps=0,
        ),
    }
    with pytest.raises(ValueError, match="exceeds u128 max"):
        execute_route_exact_in(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=1,
            total_min_amount_out=0,
        )


def test_route_exact_in_rejects_new_reserve_in_overflow() -> None:
    """Post-state reserve_in overflow raises ValueError.

    With fee_bps=9999, protocol_fee_share_bps=1000, current_amount=10000:
      fee_total=9999, net_in=1, protocol_fee=999, reserve_in_delta=9001.
    reserve_in=U128_MAX-9000, reserve_out=U128_MAX-8999:
      denom = reserve_in + net_in = U128_MAX-8999 (no overflow)
      amount_out = (reserve_out * 1) // denom = 1 (no mul overflow)
      new_reserve_in = reserve_in + 9001 = U128_MAX+1 (overflow).
    """
    from src.core.route_protocol_fee_parity import U128_MAX
    pools = {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=U128_MAX - 9000,
            reserve1=U128_MAX - 8999,
            fee_bps=9999,
        ),
    }
    with pytest.raises(ValueError, match="new_reserve_in exceeds u128 max"):
        execute_route_exact_in(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=10_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
        )


def test_route_exact_in_rejects_negative_amount_in() -> None:
    """Negative total_amount_in raises ValueError (Rust u32/u128 domain)."""
    with pytest.raises(ValueError, match="total_amount_in must be non-negative"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=-1,
            total_min_amount_out=0,
        )


def test_route_exact_in_rejects_u128_overflow_amount() -> None:
    """total_amount_in exceeding u128 max raises ValueError."""
    with pytest.raises(ValueError, match="total_amount_in exceeds u128 max"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=(1 << 128),
            total_min_amount_out=0,
        )


def test_route_exact_out_rejects_negative_amount_out() -> None:
    """Negative total_amount_out raises ValueError (Rust u128 domain)."""
    with pytest.raises(ValueError, match="total_amount_out must be non-negative"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=-1,
            total_max_amount_in=1_000_000,
        )


def test_route_exact_out_rejects_u128_overflow_amount() -> None:
    """total_amount_out exceeding u128 max raises ValueError."""
    with pytest.raises(ValueError, match="total_amount_out exceeds u128 max"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=(1 << 128),
            total_max_amount_in=1_000_000,
        )


def test_route_exact_in_rejects_zero_total_amount_in() -> None:
    """Zero total_amount_in raises ValueError early (matching Rust admission reject)."""
    with pytest.raises(ValueError, match="total_amount_in must be positive"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=0,
            total_min_amount_out=0,
        )


def test_route_exact_out_rejects_zero_total_amount_out() -> None:
    """Zero total_amount_out raises ValueError early (matching Rust admission reject)."""
    with pytest.raises(ValueError, match="total_amount_out must be positive"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=0,
            total_max_amount_in=1_000_000,
        )


def test_route_exact_out_rejects_zero_total_max_amount_in() -> None:
    """Zero total_max_amount_in raises ValueError early (matching Rust CLI admission)."""
    with pytest.raises(ValueError, match="total_max_amount_in must be positive"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=500,
            total_max_amount_in=0,
        )


def test_route_exact_in_rejects_blank_recipient() -> None:
    """Blank/whitespace protocol_fee_recipient raises ValueError (Rust trims blanks)."""
    with pytest.raises(ValueError, match="protocol_fee_recipient must not be blank"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient="   ",
        )


def test_route_exact_out_rejects_blank_recipient() -> None:
    """Blank/whitespace protocol_fee_recipient raises ValueError for exact-out too."""
    with pytest.raises(ValueError, match="protocol_fee_recipient must not be blank"):
        execute_route_exact_out(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_out=500,
            total_max_amount_in=1_000_000,
            protocol_fee_share_bps=1_000,
            protocol_fee_recipient="  ",
        )


def test_pool_rejects_non_string_status() -> None:
    """Non-string status raises ValueError (all string fields must be runtime-checked)."""
    with pytest.raises(ValueError, match="status must be a string"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
            status=123,  # type: ignore[arg-type]
        )


def test_route_rejects_lookalike_leg_object() -> None:
    """Non-RouteLeg object in legs raises ValueError (dataclass boundary check)."""
    class FakeLeg:
        hops = (RouteLegHop(POOL_ID),)

    with pytest.raises(ValueError, match="route leg must be a RouteLeg instance"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=[FakeLeg()],  # type: ignore[list-item]
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_lookalike_pool_object() -> None:
    """Non-RouteLegPool object in pools raises ValueError (dataclass boundary check)."""
    class FakePool:
        pool_id = POOL_ID
        asset0 = ASSET0
        asset1 = ASSET1
        reserve0 = 1_000_000
        reserve1 = 1_000_000
        fee_bps = 30
        status = "ACTIVE"

    with pytest.raises(ValueError, match="route pool must be a RouteLegPool instance"):
        execute_route_exact_in(
            pools={POOL_ID: FakePool()},  # type: ignore[dict-item]
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_leg_rejects_non_routeleghop_hops() -> None:
    """RouteLeg with non-RouteLegHop in hops raises ValueError (not AttributeError)."""
    with pytest.raises(ValueError, match="must be a RouteLegHop instance"):
        RouteLeg(hops=("POOL_ID",))  # type: ignore[arg-type]


def test_route_leg_rejects_non_tuple_hops() -> None:
    """RouteLeg with non-tuple hops raises ValueError."""
    with pytest.raises(ValueError, match="hops must be a tuple"):
        RouteLeg(hops=[RouteLegHop(POOL_ID)])  # type: ignore[arg-type]


def test_route_rejects_pool_key_pool_id_mismatch() -> None:
    """Pool dict key differing from pool's pool_id raises ValueError.

    Rust snapshots key pools by the pool's own pool_id, so a key/pool_id
    split is outside Rust-representable state. The dict key must match
    the leg's pool_id (so the pool is found), but the pool's internal
    pool_id must differ from the key.
    """
    pools = {
        POOL_ID: RouteLegPool(
            pool_id="DIFFERENT_POOL_ID",
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        ),
    }
    with pytest.raises(ValueError, match="key/pool_id mismatch"):
        execute_route_exact_in(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_unreferenced_mismatched_pool() -> None:
    """Unreferenced pool with key/pool_id mismatch also rejected (full snapshot parity)."""
    pools = {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        ),
        "EXTRA_KEY": RouteLegPool(
            pool_id="DIFFERENT_EXTRA",
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=500_000,
            reserve1=500_000,
            fee_bps=30,
        ),
    }
    with pytest.raises(ValueError, match="key/pool_id mismatch"):
        execute_route_exact_in(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_non_dict_pools() -> None:
    """Non-dict pools raises ValueError (not AttributeError)."""
    with pytest.raises(ValueError, match="pools must be a dict"):
        execute_route_exact_in(
            pools=[("POOL_ID", _single_pool()[POOL_ID])],  # type: ignore[arg-type]
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_route_rejects_non_iterable_legs() -> None:
    """Non-iterable legs raises ValueError (not TypeError)."""
    with pytest.raises(ValueError, match="legs must be a list or tuple"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=42,  # type: ignore[arg-type]
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


def test_pool_rejects_empty_pool_id() -> None:
    """Empty pool_id raises ValueError (Rust rejects empty snapshot/read-set pool ids)."""
    with pytest.raises(ValueError, match="pool_id must not be empty"):
        RouteLegPool(
            pool_id="",
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_pool_rejects_empty_asset0() -> None:
    """Empty asset0 raises ValueError."""
    with pytest.raises(ValueError, match="asset0 must not be empty"):
        RouteLegPool(
            pool_id=POOL_ID,
            asset0="",
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=30,
        )


def test_route_rejects_empty_asset_in() -> None:
    """Empty asset_in raises ValueError."""
    with pytest.raises(ValueError, match="asset_in must not be empty"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in="",
            asset_out=ASSET1,
            total_amount_in=100_000,
            total_min_amount_out=0,
        )


# ---------------------------------------------------------------------------
# Pinned boundary corpus: hardcoded expected values (not formula recomputation)
# These pin specific small/edge cases that a Rust-generated corpus would cover.
# ---------------------------------------------------------------------------


def test_pinned_single_leg_exact_in_tiny_amount_rejects() -> None:
    """Pinned: 1-unit input, fee 30bps -> net_in=0 -> reject."""
    with pytest.raises(ValueError, match="net_in must be positive"):
        execute_route_exact_in(
            pools=_single_pool(),
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=1,
            total_min_amount_out=0,
        )


def test_pinned_single_leg_exact_in_boundary_amount() -> None:
    """Pinned: 334 units, fee 30bps -> fee=ceil(334*30/10000)=2, net_in=332.

    amount_out = floor(1000000*332/(1000000+332)) = floor(332*1000000/1000332)
    = floor(331.89...) = 331
    """
    pools = _single_pool()
    result = execute_route_exact_in(
        pools=pools,
        legs=_single_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET1,
        total_amount_in=334,
        total_min_amount_out=0,
    )
    assert result.sender_debit == 334
    assert result.recipient_credit == 331
    assert result.leg_results[0].fee_total == 2
    assert result.leg_results[0].net_in == 332
    assert result.leg_results[0].amount_out == 331


def test_pinned_single_leg_exact_in_zero_fee() -> None:
    """Pinned: 1000 units, fee 0bps -> fee=0, net_in=1000.

    amount_out = floor(1000000*1000/(1000000+1000)) = floor(999000000/1001000)
    = floor(999.000...) = 999
    """
    pools = {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=0,
        ),
    }
    result = execute_route_exact_in(
        pools=pools,
        legs=_single_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET1,
        total_amount_in=1_000,
        total_min_amount_out=0,
    )
    assert result.sender_debit == 1_000
    assert result.recipient_credit == 999
    assert result.leg_results[0].fee_total == 0
    assert result.leg_results[0].net_in == 1_000
    assert result.leg_results[0].amount_out == 999


def test_pinned_single_leg_exact_in_max_fee_boundary() -> None:
    """Pinned: 10000 units, fee 10000bps (100%) -> fee=10000, net_in=0 -> reject."""
    pools = {
        POOL_ID: RouteLegPool(
            pool_id=POOL_ID,
            asset0=ASSET0,
            asset1=ASSET1,
            reserve0=1_000_000,
            reserve1=1_000_000,
            fee_bps=10_000,
        ),
    }
    with pytest.raises(ValueError, match="net_in must be positive"):
        execute_route_exact_in(
            pools=pools,
            legs=_single_leg_route(),
            asset_in=ASSET0,
            asset_out=ASSET1,
            total_amount_in=10_000,
            total_min_amount_out=0,
        )


def test_pinned_two_leg_exact_out_boundary() -> None:
    """Pinned: 2-leg exact-out, target 1000 ASSET2. Hardcoded expected values.

    Reverse pass:
    - Leg 2 (CHAIN_POOL: ASSET1/ASSET2, 1.5M/3M, fee 100bps):
      target_out=1000, reserve_in=1.5M, reserve_out=3M
      net_in = ceil(1.5M*1000/(3M-1000)) = ceil(1500000000/2999000) = ceil(500.16...) = 501
      gross_in = ceil(501*10000/(10000-100)) = ceil(5010000/9900) = ceil(506.06...) = 507
    - Leg 1 (POOL_ID: ASSET0/ASSET1, 1M/1M, fee 30bps):
      target_out=507, reserve_in=1M, reserve_out=1M
      net_in = ceil(1M*507/(1M-507)) = ceil(507000000/999493) = ceil(507.25...) = 508
      gross_in = ceil(508*10000/(10000-30)) = ceil(5080000/9970) = ceil(509.52...) = 510

    Forward pass (no protocol fee):
    - Leg 1: fee=ceil(510*30/10000)=ceil(1.53)=2, net_in=508
      amount_out = floor(1M*508/(1M+508)) = floor(508000000/1000508) = floor(507.74...) = 507
    - Leg 2: fee=ceil(507*100/10000)=ceil(5.07)=6, net_in=501
      amount_out = floor(3M*501/(1.5M+501)) = floor(1503000000/1500501) = floor(1001.66...) = 1001

    recipient_credit = 1000 (target_out for last leg)
    sender_debit = 510 (required_in)
    """
    pools = _two_pool_chain()
    result = execute_route_exact_out(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_out=1_000,
        total_max_amount_in=1_000_000,
    )
    assert result.sender_debit == 510
    assert result.recipient_credit == 1_000
    assert result.leg_results[0].amount_out == 507
    assert result.leg_results[1].amount_out == 1_001
    assert result.leg_results[0].fee_total == 2
    assert result.leg_results[1].fee_total == 6


def test_pinned_single_leg_exact_out_overdelivery() -> None:
    """Pinned: exact-out overdelivery. target=500, expect amount_out >= 500.

    Reverse: net_in = ceil(1M*500/(1M-500)) = ceil(500000000/999500) = ceil(500.25) = 501
    gross_in = ceil(501*10000/9970) = ceil(5010000/9970) = ceil(502.50...) = 503

    Forward: fee = ceil(503*30/10000) = ceil(1.509) = 2, net_in = 501
    amount_out = floor(1M*501/(1M+501)) = floor(501000000/1000501) = floor(500.74...) = 500

    Overdelivery = amount_out - target_out = 500 - 500 = 0 (exact in this case)
    """
    pools = _single_pool()
    result = execute_route_exact_out(
        pools=pools,
        legs=_single_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET1,
        total_amount_out=500,
        total_max_amount_in=1_000_000,
    )
    assert result.sender_debit == 503
    assert result.recipient_credit == 500
    assert result.leg_results[0].amount_out == 500
    assert result.leg_results[0].amount_out >= 500  # overdelivery >= 0


def test_pinned_two_leg_exact_in_protocol_fee_boundary() -> None:
    """Pinned: 2-leg exact-in with 50% protocol fee. Hardcoded expected.

    Leg 1: amount_in=100000, fee_bps=30
      fee_total = ceil(100000*30/10000) = 300
      protocol_fee = floor(300*5000/10000) = 150
      net_in = 100000-300 = 99700
      amount_out = floor(1M*99700/(1M+99700)) = floor(99700000000/1099700) = floor(90661.08...) = 90661

    Leg 2: amount_in=90661, fee_bps=100
      fee_total = ceil(90661*100/10000) = ceil(906.61) = 907
      protocol_fee = floor(907*5000/10000) = floor(453.5) = 453
      net_in = 90661-907 = 89754
      amount_out = floor(3M*89754/(1.5M+89754)) = floor(269262000000/1589754) = floor(169373.41...) = 169373
    """
    pools = _two_pool_chain()
    result = execute_route_exact_in(
        pools=pools,
        legs=_two_leg_route(),
        asset_in=ASSET0,
        asset_out=ASSET2,
        total_amount_in=100_000,
        total_min_amount_out=0,
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient=PROTOCOL_FEE_RECIPIENT,
    )
    assert result.sender_debit == 100_000
    assert result.recipient_credit == 169_373
    assert result.leg_results[0].fee_total == 300
    assert result.leg_results[0].protocol_fee == 150
    assert result.leg_results[0].net_in == 99_700
    assert result.leg_results[0].amount_out == 90_661
    assert result.leg_results[1].fee_total == 907
    assert result.leg_results[1].protocol_fee == 453
    assert result.leg_results[1].net_in == 89_754
    assert result.leg_results[1].amount_out == 169_373
    assert result.fee_credits[(PROTOCOL_FEE_RECIPIENT, ASSET0)] == 150
    assert result.fee_credits[(PROTOCOL_FEE_RECIPIENT, ASSET1)] == 453


# ---------------------------------------------------------------------------
# Pinned Python regression corpus: load JSON fixture and compare
# These are pinned regression vectors using Rust unit-test fixtures.
# NOT a mechanical Rust/Python differential corpus (no Rust-side JSON exporter).
# ---------------------------------------------------------------------------

_FIXTURE_PATH = os.path.join(os.path.dirname(__file__), "route_fee_parity_fixture_corpus.json")


def _load_fixture_corpus() -> list[dict]:
    """Load the pinned regression fixture corpus."""
    with open(_FIXTURE_PATH) as f:
        data = json.load(f)
    return data["fixtures"]


def _build_pools_from_fixture(fixture: dict) -> dict[str, RouteLegPool]:
    """Build pool dict from fixture JSON."""
    pools = {}
    for pool_id, p in fixture["pools"].items():
        pools[pool_id] = RouteLegPool(
            pool_id=pool_id,
            asset0=p["asset0"],
            asset1=p["asset1"],
            reserve0=p["reserve0"],
            reserve1=p["reserve1"],
            fee_bps=p["fee_bps"],
        )
    return pools


def _build_legs_from_fixture(fixture: dict) -> list[RouteLeg]:
    """Build legs list from fixture JSON."""
    return [RouteLeg(hops=tuple(RouteLegHop(pool_id=h) for h in leg)) for leg in fixture["legs"]]


@pytest.mark.parametrize("fixture", _load_fixture_corpus(), ids=lambda f: f["id"])
def test_fixture_corpus_matches_python(fixture: dict) -> None:
    """Pinned regression: Python output must match hardcoded fixture values.

    This is NOT formula recomputation. The expected values in the JSON corpus are
    pinned from Python output against Rust unit-test fixtures. If Python output
    drifts from these hardcoded values, the test fails.
    """
    pools = _build_pools_from_fixture(fixture)
    legs = _build_legs_from_fixture(fixture)
    expected = fixture["expected"]
    share_bps = fixture.get("protocol_fee_share_bps", 0)
    recipient = PROTOCOL_FEE_RECIPIENT if share_bps > 0 else None

    if fixture["route_type"] == "exact_in":
        result = execute_route_exact_in(
            pools=pools,
            legs=legs,
            asset_in=fixture["asset_in"],
            asset_out=fixture["asset_out"],
            total_amount_in=fixture["total_amount_in"],
            total_min_amount_out=fixture["total_min_amount_out"],
            protocol_fee_share_bps=share_bps,
            protocol_fee_recipient=recipient,
        )
    else:
        result = execute_route_exact_out(
            pools=pools,
            legs=legs,
            asset_in=fixture["asset_in"],
            asset_out=fixture["asset_out"],
            total_amount_out=fixture["total_amount_out"],
            total_max_amount_in=fixture["total_max_amount_in"],
            protocol_fee_share_bps=share_bps,
            protocol_fee_recipient=recipient,
        )

    assert result.sender_debit == expected["sender_debit"], f"sender_debit mismatch in {fixture['id']}"
    assert result.recipient_credit == expected["recipient_credit"], f"recipient_credit mismatch in {fixture['id']}"

    for i, leg_expected in enumerate(expected["leg_results"]):
        leg = result.leg_results[i]
        assert leg.fee_total == leg_expected["fee_total"], f"leg {i} fee_total mismatch in {fixture['id']}"
        assert leg.protocol_fee == leg_expected["protocol_fee"], f"leg {i} protocol_fee mismatch in {fixture['id']}"
        assert leg.net_in == leg_expected["net_in"], f"leg {i} net_in mismatch in {fixture['id']}"
        assert leg.amount_out == leg_expected["amount_out"], f"leg {i} amount_out mismatch in {fixture['id']}"

    if "fee_credits" in expected:
        expected_credits = {
            (PROTOCOL_FEE_RECIPIENT, asset_id): fee
            for asset_id, fee in expected["fee_credits"].items()
        }
        assert result.fee_credits == expected_credits, \
            f"fee_credits dict mismatch in {fixture['id']}: " \
            f"got {result.fee_credits}, expected {expected_credits}"
