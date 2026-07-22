from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Mapping

from ..core.price_impact_preview import compute_price_impact_bps
from ..core.quote_receipts import verify_route_quote_receipt
from ..kernels.python.strategy_route_economic_sanity_guard_v1_adapter import (
    StrategyRouteEconomicSanityInputs,
    StrategyRouteEconomicSanityPolicy,
    check_strategy_route_economic_sanity,
)
from ..state.immutable_json import snapshot_json_mapping
from ..state.pools import PoolState

ROUTE_METRIC_MAX = 0xFFFFFFFF
ROUTE_INPUT_STRESS_EXTREME_BPS = 10_000
ROUTE_OUTPUT_DEPLETION_EXTREME_BPS = 9_000
ROUTE_PRICE_IMPACT_EXTREME_BPS = 5_000
ROUTE_ECONOMIC_SANITY_POLICY = StrategyRouteEconomicSanityPolicy(
    input_stress_extreme_bps=ROUTE_INPUT_STRESS_EXTREME_BPS,
    output_depletion_extreme_bps=ROUTE_OUTPUT_DEPLETION_EXTREME_BPS,
    price_impact_extreme_bps=ROUTE_PRICE_IMPACT_EXTREME_BPS,
)


@dataclass(frozen=True)
class RouteShapeFacts:
    receipt_kind: str = ""
    leg_count: int = 0
    hop_count: int = 0
    route_kind_supported: bool = False
    body_pair_valid: bool = False
    legs_present: bool = False
    all_legs_single_hop: bool = False
    all_legs_match_body_pair: bool = False
    multi_hop_present: bool = False
    legs: tuple[object, ...] = ()


@dataclass(frozen=True)
class RouteStressMetrics:
    max_input_stress_bps: int = 0
    max_output_depletion_bps: int = 0
    max_price_impact_bps: int = 0
    dominant_hop_pool_id: str = ""
    dominant_hop_asset_in: str = ""
    dominant_hop_asset_out: str = ""
    dominant_hop_amount_in: int = 0
    dominant_hop_reserve_in: int = 0
    dominant_hop_amount_out: int = 0
    dominant_hop_reserve_out: int = 0


@dataclass(frozen=True)
class RouteEconomicSanitySnapshot:
    receipt_verified: bool
    verification_error: str | None
    receipt_kind: str
    leg_count: int
    hop_count: int
    route_kind_supported: bool
    body_pair_valid: bool
    legs_present: bool
    all_legs_single_hop: bool
    all_legs_match_body_pair: bool
    multi_hop_present: bool
    route_shape_supported_for_intents: bool
    max_hop_input_vs_reserve_bps: int
    max_hop_output_vs_reserve_bps: int
    max_hop_price_impact_bps: int
    dominant_hop_pool_id: str
    dominant_hop_asset_in: str
    dominant_hop_asset_out: str
    dominant_hop_amount_in: int
    dominant_hop_reserve_in: int
    dominant_hop_amount_out: int
    dominant_hop_reserve_out: int
    extreme_input_stress_present: bool
    extreme_output_depletion_present: bool
    extreme_price_impact_present: bool
    route_economic_sanity_ok: bool
    classification_error: str | None


def _safe_ratio_bps(numerator: int, denominator: int) -> int:
    if denominator <= 0 or numerator <= 0:
        return 0
    ratio_bps = int(numerator) * 10_000 // int(denominator)
    return min(ROUTE_METRIC_MAX, int(ratio_bps))


def _pool_reserves_for_direction(
    pool: PoolState,
    *,
    asset_in: str,
    asset_out: str,
) -> tuple[int, int] | None:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _replace_pool_reserves_for_direction(
    pool: PoolState,
    *,
    asset_in: str,
    asset_out: str,
    reserve_in: int,
    reserve_out: int,
) -> PoolState:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return replace(pool, reserve0=int(reserve_in), reserve1=int(reserve_out))
    return replace(pool, reserve0=int(reserve_out), reserve1=int(reserve_in))


def _route_shape_facts(*, body: Mapping[str, Any] | None) -> RouteShapeFacts:
    if not isinstance(body, Mapping):
        return RouteShapeFacts()
    receipt_kind = str(body.get("kind", "")).strip().lower()
    route_kind_supported = receipt_kind in {"exact_in", "exact_out"}
    body_asset_in = str(body.get("asset_in", "")).strip()
    body_asset_out = str(body.get("asset_out", "")).strip()
    body_pair_valid = bool(body_asset_in and body_asset_out and body_asset_in != body_asset_out)
    legs = body.get("legs")
    if not isinstance(legs, list):
        return RouteShapeFacts(
            receipt_kind=receipt_kind,
            route_kind_supported=route_kind_supported,
            body_pair_valid=body_pair_valid,
        )

    hop_count = 0
    all_legs_single_hop = bool(legs)
    all_legs_match_body_pair = bool(legs) and body_pair_valid
    multi_hop_present = False
    for leg in legs:
        if not isinstance(leg, Mapping):
            all_legs_single_hop = False
            all_legs_match_body_pair = False
            continue
        hops = leg.get("hops")
        if not isinstance(hops, list) or not hops:
            all_legs_single_hop = False
            all_legs_match_body_pair = False
            continue
        hop_count += len(hops)
        if len(hops) != 1:
            all_legs_single_hop = False
        if len(hops) > 1:
            multi_hop_present = True
        for hop in hops:
            if not isinstance(hop, Mapping):
                all_legs_match_body_pair = False
                continue
            asset_in = str(hop.get("asset_in", "")).strip()
            asset_out = str(hop.get("asset_out", "")).strip()
            if not asset_in or not asset_out or asset_in == asset_out:
                all_legs_match_body_pair = False
                continue
            if asset_in != body_asset_in or asset_out != body_asset_out:
                all_legs_match_body_pair = False
    return RouteShapeFacts(
        receipt_kind=receipt_kind,
        leg_count=int(len(legs)),
        hop_count=int(hop_count),
        route_kind_supported=bool(route_kind_supported),
        body_pair_valid=bool(body_pair_valid),
        legs_present=bool(legs),
        all_legs_single_hop=bool(all_legs_single_hop),
        all_legs_match_body_pair=bool(all_legs_match_body_pair),
        multi_hop_present=bool(multi_hop_present),
        legs=tuple(legs),
    )


def _route_stress_metrics(
    *,
    legs: tuple[object, ...],
    pools_by_id: Mapping[str, PoolState],
) -> RouteStressMetrics:
    max_input_stress_bps = 0
    max_output_depletion_bps = 0
    max_price_impact_bps = 0
    dominant_hop_pool_id = ""
    dominant_hop_asset_in = ""
    dominant_hop_asset_out = ""
    dominant_hop_amount_in = 0
    dominant_hop_reserve_in = 0
    dominant_hop_amount_out = 0
    dominant_hop_reserve_out = 0
    working_pools = {
        str(pool_id): pool
        for pool_id, pool in pools_by_id.items()
        if isinstance(pool_id, str) and isinstance(pool, PoolState)
    }
    for leg in legs:
        if not isinstance(leg, Mapping):
            continue
        hops = leg.get("hops")
        if not isinstance(hops, list):
            continue
        for hop in hops:
            if not isinstance(hop, Mapping):
                continue
            pool_id = str(hop.get("pool_id", "")).strip()
            asset_in = str(hop.get("asset_in", "")).strip()
            asset_out = str(hop.get("asset_out", "")).strip()
            amount_in = hop.get("amount_in")
            amount_out = hop.get("amount_out")
            if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                continue
            if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
                continue
            pool = working_pools.get(pool_id)
            if pool is None:
                continue
            reserves = _pool_reserves_for_direction(pool, asset_in=asset_in, asset_out=asset_out)
            if reserves is None:
                continue
            reserve_in, reserve_out = reserves
            input_stress_bps = _safe_ratio_bps(int(amount_in), int(reserve_in))
            output_depletion_bps = _safe_ratio_bps(int(amount_out), int(reserve_out))
            price_impact_bps = 0
            if str(pool.curve_tag).strip().upper() == "CPMM":
                try:
                    price_impact_bps = compute_price_impact_bps(
                        reserve_in=int(reserve_in),
                        reserve_out=int(reserve_out),
                        amount_in=int(amount_in),
                        fee_bps=int(pool.fee_bps),
                    )
                except (TypeError, ValueError):
                    price_impact_bps = 0
            price_impact_bps = max(0, min(ROUTE_METRIC_MAX, int(price_impact_bps)))
            if input_stress_bps > max_input_stress_bps:
                max_input_stress_bps = input_stress_bps
                dominant_hop_pool_id = pool_id
                dominant_hop_asset_in = asset_in
                dominant_hop_asset_out = asset_out
                dominant_hop_amount_in = int(amount_in)
                dominant_hop_reserve_in = int(reserve_in)
                dominant_hop_amount_out = int(amount_out)
                dominant_hop_reserve_out = int(reserve_out)
            if output_depletion_bps > max_output_depletion_bps:
                max_output_depletion_bps = output_depletion_bps
            if price_impact_bps > max_price_impact_bps:
                max_price_impact_bps = price_impact_bps
            next_reserve_in = int(reserve_in) + int(amount_in)
            next_reserve_out = max(0, int(reserve_out) - int(amount_out))
            working_pools[pool_id] = _replace_pool_reserves_for_direction(
                pool,
                asset_in=asset_in,
                asset_out=asset_out,
                reserve_in=next_reserve_in,
                reserve_out=next_reserve_out,
            )
    return RouteStressMetrics(
        max_input_stress_bps=int(max_input_stress_bps),
        max_output_depletion_bps=int(max_output_depletion_bps),
        max_price_impact_bps=int(max_price_impact_bps),
        dominant_hop_pool_id=dominant_hop_pool_id,
        dominant_hop_asset_in=dominant_hop_asset_in,
        dominant_hop_asset_out=dominant_hop_asset_out,
        dominant_hop_amount_in=int(dominant_hop_amount_in),
        dominant_hop_reserve_in=int(dominant_hop_reserve_in),
        dominant_hop_amount_out=int(dominant_hop_amount_out),
        dominant_hop_reserve_out=int(dominant_hop_reserve_out),
    )


def build_route_economic_sanity_snapshot(
    *,
    quote_receipt: Mapping[str, Any] | None,
    pools_by_id: Mapping[str, PoolState] | None,
) -> RouteEconomicSanitySnapshot | None:
    if not isinstance(quote_receipt, Mapping):
        return None
    if not isinstance(pools_by_id, Mapping):
        return None

    try:
        receipt_snapshot = snapshot_json_mapping(quote_receipt, name="quote_receipt")
    except TypeError:
        return None
    verify_ok, verify_error = verify_route_quote_receipt(
        receipt_snapshot,
        pools_by_id=dict(pools_by_id),
    )
    shape = _route_shape_facts(body=receipt_snapshot.get("body"))
    metrics = _route_stress_metrics(legs=shape.legs, pools_by_id=pools_by_id)
    classification = check_strategy_route_economic_sanity(
        inputs=StrategyRouteEconomicSanityInputs(
            receipt_verified=bool(verify_ok),
            route_kind_supported=shape.route_kind_supported,
            body_pair_valid=shape.body_pair_valid,
            legs_present=shape.legs_present,
            all_legs_single_hop=shape.all_legs_single_hop,
            all_legs_match_body_pair=shape.all_legs_match_body_pair,
            multi_hop_present=shape.multi_hop_present,
            max_hop_input_vs_reserve_bps=metrics.max_input_stress_bps,
            max_hop_output_vs_reserve_bps=metrics.max_output_depletion_bps,
            max_hop_price_impact_bps=metrics.max_price_impact_bps,
        ),
        policy=ROUTE_ECONOMIC_SANITY_POLICY,
    )
    return RouteEconomicSanitySnapshot(
        receipt_verified=bool(verify_ok),
        verification_error=None if verify_ok else str(verify_error),
        receipt_kind=shape.receipt_kind,
        leg_count=int(shape.leg_count),
        hop_count=int(shape.hop_count),
        route_kind_supported=bool(shape.route_kind_supported),
        body_pair_valid=bool(shape.body_pair_valid),
        legs_present=bool(shape.legs_present),
        all_legs_single_hop=bool(shape.all_legs_single_hop),
        all_legs_match_body_pair=bool(shape.all_legs_match_body_pair),
        multi_hop_present=bool(shape.multi_hop_present),
        route_shape_supported_for_intents=bool(classification.route_shape_supported_for_intents),
        max_hop_input_vs_reserve_bps=int(metrics.max_input_stress_bps),
        max_hop_output_vs_reserve_bps=int(metrics.max_output_depletion_bps),
        max_hop_price_impact_bps=int(metrics.max_price_impact_bps),
        dominant_hop_pool_id=metrics.dominant_hop_pool_id,
        dominant_hop_asset_in=metrics.dominant_hop_asset_in,
        dominant_hop_asset_out=metrics.dominant_hop_asset_out,
        dominant_hop_amount_in=int(metrics.dominant_hop_amount_in),
        dominant_hop_reserve_in=int(metrics.dominant_hop_reserve_in),
        dominant_hop_amount_out=int(metrics.dominant_hop_amount_out),
        dominant_hop_reserve_out=int(metrics.dominant_hop_reserve_out),
        extreme_input_stress_present=bool(classification.extreme_input_stress_present),
        extreme_output_depletion_present=bool(classification.extreme_output_depletion_present),
        extreme_price_impact_present=bool(classification.extreme_price_impact_present),
        route_economic_sanity_ok=bool(classification.ok),
        classification_error=classification.error,
    )
