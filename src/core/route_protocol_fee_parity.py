"""
Python route execution with per-leg protocol fee capture.

This module mirrors the Rust ZK proof kernel's per-leg route protocol fee
accounting model (RC25_ROUTE_PROTOCOL_FEE_PER_LEG_20260703.md).

Per leg:
    fee_total = ceil(current_input * pool.fee_bps / 10_000)
    protocol_fee = floor(fee_total * protocol_fee_share_bps / 10_000)
    net_in = current_input - fee_total
    amount_out = floor(reserve_out * net_in / (reserve_in + net_in))
    reserve_in_delta = current_input - protocol_fee

The protocol fee is credited in the leg input asset. The output amount is not
reduced by the protocol fee. This matches the single-swap protocol-fee model.

Conservation equations (route exact-in):
    first_leg.reserve_in_delta + first_leg.protocol_fee = sender_debit
    leg_i.reserve_out_delta = leg_{i+1}.reserve_in_delta + leg_{i+1}.protocol_fee
    last_leg.reserve_out_delta = recipient_credit

For route exact-out, the reverse pass computes required_in using the same
ceil-identity that guarantees amount_out >= target_out. The forward pass then
captures protocol fees per leg identically to exact-in.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

BPS_DENOM = 10_000
U128_MAX = (1 << 128) - 1


def _check_u128(value: int, name: str) -> None:
    """Validate that value is a Python int in Rust u128 domain [0, 2^128-1]."""
    if type(value) is not int:
        raise ValueError(f"{name} must be an integer, got {type(value).__name__}")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if value > U128_MAX:
        raise ValueError(f"{name} exceeds u128 max")


def _check_str(value: object, name: str) -> None:
    """Validate that value is a non-empty Python str.

    Rust JSON parsing is string-only, so non-string types are rejected.
    Empty strings are rejected as stricter Python admission. Rust clearly
    rejects empty pool_id and route asset_in, but does not have equivalent
    snapshot rejection for pool asset0/asset1. The empty-string check for
    asset0/asset1 is therefore stricter-than-Rust Python admission, not
    exact Rust parity for every string field.
    """
    if type(value) is not str:
        raise ValueError(f"{name} must be a string, got {type(value).__name__}")
    if value == "":
        raise ValueError(f"{name} must not be empty")


def _check_u128_add(a: int, b: int, name: str) -> int:
    """Checked addition: result must fit in u128."""
    result = a + b
    if result > U128_MAX:
        raise ValueError(f"{name} exceeds u128 max")
    return result


def _check_u128_mul(a: int, b: int, name: str) -> int:
    """Checked multiplication: result must fit in u128."""
    result = a * b
    if result > U128_MAX:
        raise ValueError(f"{name} exceeds u128 max")
    return result


def _ceil_div_nonneg(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    return (numerator + denominator - 1) // denominator


@dataclass(frozen=True)
class RouteLegPool:
    """Single pool in a route leg (proof v1: one pool per leg)."""
    pool_id: str
    asset0: str
    asset1: str
    reserve0: int
    reserve1: int
    fee_bps: int
    status: str = "ACTIVE"

    def __post_init__(self) -> None:
        _check_str(self.pool_id, "pool_id")
        _check_str(self.asset0, "asset0")
        _check_str(self.asset1, "asset1")
        _check_str(self.status, "status")
        _check_u128(self.reserve0, "reserve0")
        _check_u128(self.reserve1, "reserve1")
        _check_u128(self.fee_bps, "fee_bps")
        if self.fee_bps > BPS_DENOM:
            raise ValueError("fee_bps must be in [0, 10000]")


@dataclass(frozen=True)
class RouteLegHop:
    """Single hop in a route leg."""
    pool_id: str

    def __post_init__(self) -> None:
        _check_str(self.pool_id, "hop pool_id")


@dataclass(frozen=True)
class RouteLeg:
    """Route leg containing one hop (proof v1: one pool per leg)."""
    hops: Tuple[RouteLegHop, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.hops, tuple):
            raise ValueError("RouteLeg.hops must be a tuple")
        for i, hop in enumerate(self.hops):
            if not isinstance(hop, RouteLegHop):
                raise ValueError(f"RouteLeg.hops[{i}] must be a RouteLegHop instance")


@dataclass(frozen=True)
class RouteExecutionResult:
    """Result of executing a route with per-leg protocol fee capture."""
    sender_debit: int
    recipient_credit: int
    leg_results: Tuple["RouteLegResult", ...]
    fee_credits: Dict[Tuple[str, str], int]
    pool_updates: Dict[str, Tuple[int, int]]
    asset_in: str
    asset_out: str


@dataclass(frozen=True)
class RouteLegResult:
    """Per-leg execution result."""
    pool_id: str
    asset_in: str
    asset_out: str
    current_amount: int
    fee_total: int
    protocol_fee: int
    net_in: int
    amount_out: int
    reserve_in_delta: int
    reserve_out_delta: int
    new_reserve_in: int
    new_reserve_out: int


def _recipient_is_valid(recipient: Optional[str]) -> bool:
    """
    Check that a protocol-fee recipient is a non-blank string.

    Mirrors the Rust kernel's `filter(|r| !r.trim().is_empty())` check:
    None, empty string, whitespace-only strings, and non-string types
    (bytes, int, etc.) are all rejected. Rust rejects non-string recipients
    at context parsing (main.rs).
    """
    if recipient is None:
        return False
    if type(recipient) is not str:
        return False
    return recipient.strip() != ""


def _validate_route_envelope(
    *,
    pools: Dict[str, RouteLegPool],
    legs: List[RouteLeg],
    asset_in: str,
    asset_out: str,
) -> None:
    """
    Validate route envelope constraints matching the Rust kernel's structural
    admission rejects.

    This covers the subset of Rust route admission checks that apply to the
    Python helper's dataclass API: empty legs, multi-hop legs, duplicate pool
    ids, missing pools, and inactive pools. It does NOT cover Rust-only
    envelope checks that require fields absent from this helper, such as
    ``leg_indices`` coverage, ``quote_receipt_hash`` binding, positive amount
    guards, or empty ``pool_id`` in read-set handling. Those are enforced by
    the Rust ZK proof kernel at the transition boundary.
    """
    _check_str(asset_in, "asset_in")
    _check_str(asset_out, "asset_out")
    if not isinstance(pools, Mapping):
        raise ValueError("pools must be a mapping")
    if not isinstance(legs, (list, tuple)):
        raise ValueError("legs must be a list or tuple")
    if not legs:
        raise ValueError("route must have at least one leg")
    # Validate all pools for key/pool_id consistency (Rust snapshots by pool's own pool_id)
    for key, pool in pools.items():
        if not isinstance(pool, RouteLegPool):
            raise ValueError(f"route pool must be a RouteLegPool instance: {key}")
        if pool.pool_id != key:
            raise ValueError(
                f"route pool key/pool_id mismatch: key={key} pool_id={pool.pool_id}"
            )
    seen_pool_ids: set[str] = set()
    for leg in legs:
        if not isinstance(leg, RouteLeg):
            raise ValueError("route leg must be a RouteLeg instance")
        if len(leg.hops) != 1:
            raise ValueError("route leg must have exactly one hop (proof v1)")
        pool_id = leg.hops[0].pool_id
        if pool_id in seen_pool_ids:
            raise ValueError(f"route duplicate pool_id across legs: {pool_id}")
        seen_pool_ids.add(pool_id)
        referenced_pool = pools.get(pool_id)
        if referenced_pool is None:
            raise ValueError(f"route pool not found: {pool_id}")
        if not getattr(referenced_pool, "status", "ACTIVE") == "ACTIVE":
            raise ValueError(f"route pool not active: {pool_id}")


def execute_route_exact_in(
    *,
    pools: Dict[str, RouteLegPool],
    legs: List[RouteLeg],
    asset_in: str,
    asset_out: str,
    total_amount_in: int,
    total_min_amount_out: int,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient: Optional[str] = None,
) -> RouteExecutionResult:
    """
    Execute a ROUTE_EXACT_IN with per-leg protocol fee capture.

    Mirrors the Rust `apply_route` ROUTE_EXACT_IN route arithmetic/accounting
    path (fee_total, protocol_fee, net_in, amount_out, reserve deltas):
    1. Validate route envelope (legs, hops, duplicate pools, pool status).
    2. Walk legs forward, computing per-leg swap with fee capture.
    3. Verify total_min_amount_out is met.
    4. Return per-leg results, fee credits, and pool updates.

    This is a Python helper subset of the Rust transition; it does not cover
    Rust-only envelope checks (leg_indices, quote_receipt_hash, etc.).
    """
    _check_u128(protocol_fee_share_bps, "protocol_fee_share_bps")
    if not (0 <= protocol_fee_share_bps <= BPS_DENOM):
        raise ValueError("protocol_fee_share_bps must be in [0, 10000]")
    if protocol_fee_recipient is not None and type(protocol_fee_recipient) is not str:
        raise ValueError("protocol_fee_recipient must be a string or None")
    if protocol_fee_share_bps > 0:
        if protocol_fee_recipient is not None and protocol_fee_recipient.strip() == "":
            raise ValueError("protocol_fee_recipient must not be blank")
        if not _recipient_is_valid(protocol_fee_recipient):
            raise ValueError(
                "protocol_fee_recipient required when protocol_fee_share_bps > 0"
            )
    _check_u128(total_amount_in, "total_amount_in")
    _check_u128(total_min_amount_out, "total_min_amount_out")
    if total_amount_in == 0:
        raise ValueError("total_amount_in must be positive")
    _validate_route_envelope(
        pools=pools, legs=legs, asset_in=asset_in, asset_out=asset_out
    )

    current_asset = asset_in
    current_amount = total_amount_in
    leg_results: List[RouteLegResult] = []
    fee_credits: Dict[Tuple[str, str], int] = {}
    pool_updates: Dict[str, Tuple[int, int]] = {}

    for leg in legs:
        pool_id = leg.hops[0].pool_id
        pool = pools[pool_id]

        if current_asset == pool.asset0:
            asset_out_leg = pool.asset1
            reserve_in = pool.reserve0
            reserve_out = pool.reserve1
        elif current_asset == pool.asset1:
            asset_out_leg = pool.asset0
            reserve_in = pool.reserve1
            reserve_out = pool.reserve0
        else:
            raise ValueError(f"route asset chain mismatch at pool {pool_id}")

        fee_total = _ceil_div_nonneg(
            _check_u128_mul(current_amount, pool.fee_bps, "fee_total numerator"),
            BPS_DENOM,
        )
        if fee_total > current_amount:
            raise ValueError("route fee_total exceeds current_amount")
        net_in = current_amount - fee_total
        if net_in <= 0:
            raise ValueError("route net_in must be positive after fees")

        protocol_fee = (_check_u128_mul(fee_total, protocol_fee_share_bps, "protocol_fee numerator")) // BPS_DENOM
        if protocol_fee > fee_total:
            raise ValueError("route protocol_fee exceeds fee_total")

        reserve_in_delta = current_amount - protocol_fee

        denom = _check_u128_add(reserve_in, net_in, "denominator")
        if denom <= 0:
            raise ValueError("route denominator must be positive")
        amount_out = (_check_u128_mul(reserve_out, net_in, "amount_out numerator")) // denom
        if amount_out == 0:
            raise ValueError("route amount_out is zero")
        if amount_out > reserve_out:
            raise ValueError("route amount_out exceeds reserve_out")

        new_reserve_in = _check_u128_add(reserve_in, reserve_in_delta, "new_reserve_in")
        new_reserve_out = reserve_out - amount_out

        if current_asset == pool.asset0:
            pool_updates[pool_id] = (new_reserve_in, new_reserve_out)
        else:
            pool_updates[pool_id] = (new_reserve_out, new_reserve_in)

        if protocol_fee > 0 and protocol_fee_recipient is not None:
            key = (protocol_fee_recipient, current_asset)
            fee_credits[key] = _check_u128_add(
                fee_credits.get(key, 0), protocol_fee, "fee_credits accumulation"
            )

        leg_results.append(
            RouteLegResult(
                pool_id=pool_id,
                asset_in=current_asset,
                asset_out=asset_out_leg,
                current_amount=current_amount,
                fee_total=fee_total,
                protocol_fee=protocol_fee,
                net_in=net_in,
                amount_out=amount_out,
                reserve_in_delta=reserve_in_delta,
                reserve_out_delta=amount_out,
                new_reserve_in=new_reserve_in,
                new_reserve_out=new_reserve_out,
            )
        )

        current_asset = asset_out_leg
        current_amount = amount_out

    if current_asset != asset_out:
        raise ValueError("route final asset mismatch")
    if current_amount < total_min_amount_out:
        raise ValueError("route total_min_amount_out not met")

    return RouteExecutionResult(
        sender_debit=total_amount_in,
        recipient_credit=current_amount,
        leg_results=tuple(leg_results),
        fee_credits=fee_credits,
        pool_updates=pool_updates,
        asset_in=asset_in,
        asset_out=asset_out,
    )


def execute_route_exact_out(
    *,
    pools: Dict[str, RouteLegPool],
    legs: List[RouteLeg],
    asset_in: str,
    asset_out: str,
    total_amount_out: int,
    total_max_amount_in: int,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient: Optional[str] = None,
) -> RouteExecutionResult:
    """
    Execute a ROUTE_EXACT_OUT with per-leg protocol fee capture.

    Mirrors the Rust `apply_route` ROUTE_EXACT_OUT route arithmetic/accounting
    path (reverse pass, fee_total, protocol_fee, net_in, amount_out, reserve
    deltas):
    1. Walk legs in reverse to compute required_in and target_outs.
    2. Walk legs forward, capturing protocol fees per leg.
    3. Verify each leg's amount_out >= target_out.
    4. Return per-leg results, fee credits, and pool updates.

    This is a Python helper subset of the Rust transition; it does not cover
    Rust-only envelope checks (leg_indices, quote_receipt_hash, etc.).
    """
    _check_u128(protocol_fee_share_bps, "protocol_fee_share_bps")
    if not (0 <= protocol_fee_share_bps <= BPS_DENOM):
        raise ValueError("protocol_fee_share_bps must be in [0, 10000]")
    if protocol_fee_recipient is not None and type(protocol_fee_recipient) is not str:
        raise ValueError("protocol_fee_recipient must be a string or None")
    if protocol_fee_share_bps > 0:
        if protocol_fee_recipient is not None and protocol_fee_recipient.strip() == "":
            raise ValueError("protocol_fee_recipient must not be blank")
        if not _recipient_is_valid(protocol_fee_recipient):
            raise ValueError(
                "protocol_fee_recipient required when protocol_fee_share_bps > 0"
            )
    _check_u128(total_amount_out, "total_amount_out")
    _check_u128(total_max_amount_in, "total_max_amount_in")
    if total_amount_out == 0:
        raise ValueError("total_amount_out must be positive")
    if total_max_amount_in == 0:
        raise ValueError("total_max_amount_in must be positive")
    _validate_route_envelope(
        pools=pools, legs=legs, asset_in=asset_in, asset_out=asset_out
    )

    # Reverse pass: compute required_in and target_outs
    required_in = total_amount_out
    assets: List[str] = [asset_out]
    target_outs: List[int] = []

    for leg in reversed(legs):
        pool_id = leg.hops[0].pool_id
        pool = pools[pool_id]

        out_asset = assets[-1]
        if out_asset == pool.asset0:
            in_asset = pool.asset1
            reserve_in = pool.reserve1
            reserve_out = pool.reserve0
        elif out_asset == pool.asset1:
            in_asset = pool.asset0
            reserve_in = pool.reserve0
            reserve_out = pool.reserve1
        else:
            raise ValueError(f"route asset chain mismatch at pool {pool_id}")

        target_outs.append(required_in)

        if required_in >= reserve_out:
            raise ValueError("route amount_out >= reserve_out")

        net_in_num = _check_u128_mul(reserve_in, required_in, "net_in numerator")
        net_in = _ceil_div_nonneg(net_in_num, reserve_out - required_in)

        denom_fee = BPS_DENOM - pool.fee_bps
        if denom_fee <= 0:
            raise ValueError("route fee_bps is 10000")

        gross_in = _ceil_div_nonneg(_check_u128_mul(net_in, BPS_DENOM, "gross_in numerator"), denom_fee)
        required_in = gross_in
        assets.append(in_asset)

    assets.reverse()
    target_outs.reverse()

    route_asset_in = assets[0]
    if route_asset_in != asset_in:
        raise ValueError("route asset_in mismatch")
    if required_in > total_max_amount_in:
        raise ValueError("route total_max_amount_in exceeded")

    # Forward pass: execute with protocol fee capture
    current_asset = asset_in
    current_amount = required_in
    leg_results: List[RouteLegResult] = []
    fee_credits: Dict[Tuple[str, str], int] = {}
    pool_updates: Dict[str, Tuple[int, int]] = {}

    for leg_index, leg in enumerate(legs):
        target_out = target_outs[leg_index]
        pool_id = leg.hops[0].pool_id
        pool = pools[pool_id]

        if current_asset == pool.asset0:
            asset_out_leg = pool.asset1
            reserve_in = pool.reserve0
            reserve_out = pool.reserve1
        elif current_asset == pool.asset1:
            asset_out_leg = pool.asset0
            reserve_in = pool.reserve1
            reserve_out = pool.reserve0
        else:
            raise ValueError(f"route asset chain mismatch at pool {pool_id}")

        fee_total = _ceil_div_nonneg(
            _check_u128_mul(current_amount, pool.fee_bps, "fee_total numerator"),
            BPS_DENOM,
        )
        if fee_total > current_amount:
            raise ValueError("route fee_total exceeds current_amount")
        net_in = current_amount - fee_total
        if net_in <= 0:
            raise ValueError("route net_in must be positive after fees")

        protocol_fee = (_check_u128_mul(fee_total, protocol_fee_share_bps, "protocol_fee numerator")) // BPS_DENOM
        if protocol_fee > fee_total:
            raise ValueError("route protocol_fee exceeds fee_total")

        reserve_in_delta = current_amount - protocol_fee

        denom = _check_u128_add(reserve_in, net_in, "denominator")
        if denom <= 0:
            raise ValueError("route denominator must be positive")
        amount_out = (_check_u128_mul(reserve_out, net_in, "amount_out numerator")) // denom
        if amount_out < target_out:
            raise ValueError("route exact-out target not met")
        if amount_out > reserve_out:
            raise ValueError("route amount_out exceeds reserve_out")

        new_reserve_in = _check_u128_add(reserve_in, reserve_in_delta, "new_reserve_in")
        new_reserve_out = reserve_out - target_out

        if current_asset == pool.asset0:
            pool_updates[pool_id] = (new_reserve_in, new_reserve_out)
        else:
            pool_updates[pool_id] = (new_reserve_out, new_reserve_in)

        if protocol_fee > 0 and protocol_fee_recipient is not None:
            key = (protocol_fee_recipient, current_asset)
            fee_credits[key] = _check_u128_add(
                fee_credits.get(key, 0), protocol_fee, "fee_credits accumulation"
            )

        leg_results.append(
            RouteLegResult(
                pool_id=pool_id,
                asset_in=current_asset,
                asset_out=asset_out_leg,
                current_amount=current_amount,
                fee_total=fee_total,
                protocol_fee=protocol_fee,
                net_in=net_in,
                amount_out=amount_out,
                reserve_in_delta=reserve_in_delta,
                reserve_out_delta=target_out,
                new_reserve_in=new_reserve_in,
                new_reserve_out=new_reserve_out,
            )
        )

        current_asset = asset_out_leg
        current_amount = target_out

    if current_asset != asset_out:
        raise ValueError("route final asset mismatch")

    return RouteExecutionResult(
        sender_debit=required_in,
        recipient_credit=total_amount_out,
        leg_results=tuple(leg_results),
        fee_credits=fee_credits,
        pool_updates=pool_updates,
        asset_in=asset_in,
        asset_out=asset_out,
    )
