from __future__ import annotations

from dataclasses import dataclass

from .strategy_budget_guard_v1_adapter import _require_u32


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


@dataclass(frozen=True)
class StrategyRouteEconomicSanityInputs:
    receipt_verified: bool
    route_kind_supported: bool
    body_pair_valid: bool
    legs_present: bool
    all_legs_single_hop: bool
    all_legs_match_body_pair: bool
    multi_hop_present: bool
    max_hop_input_vs_reserve_bps: int
    max_hop_output_vs_reserve_bps: int
    max_hop_price_impact_bps: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "receipt_verified", _require_bool("receipt_verified", self.receipt_verified))
        object.__setattr__(self, "route_kind_supported", _require_bool("route_kind_supported", self.route_kind_supported))
        object.__setattr__(self, "body_pair_valid", _require_bool("body_pair_valid", self.body_pair_valid))
        object.__setattr__(self, "legs_present", _require_bool("legs_present", self.legs_present))
        object.__setattr__(self, "all_legs_single_hop", _require_bool("all_legs_single_hop", self.all_legs_single_hop))
        object.__setattr__(
            self,
            "all_legs_match_body_pair",
            _require_bool("all_legs_match_body_pair", self.all_legs_match_body_pair),
        )
        object.__setattr__(self, "multi_hop_present", _require_bool("multi_hop_present", self.multi_hop_present))
        object.__setattr__(
            self,
            "max_hop_input_vs_reserve_bps",
            _require_u32("max_hop_input_vs_reserve_bps", self.max_hop_input_vs_reserve_bps),
        )
        object.__setattr__(
            self,
            "max_hop_output_vs_reserve_bps",
            _require_u32("max_hop_output_vs_reserve_bps", self.max_hop_output_vs_reserve_bps),
        )
        object.__setattr__(
            self,
            "max_hop_price_impact_bps",
            _require_u32("max_hop_price_impact_bps", self.max_hop_price_impact_bps),
        )


@dataclass(frozen=True)
class StrategyRouteEconomicSanityPolicy:
    input_stress_extreme_bps: int
    output_depletion_extreme_bps: int
    price_impact_extreme_bps: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "input_stress_extreme_bps",
            _require_u32("input_stress_extreme_bps", self.input_stress_extreme_bps, minimum=1),
        )
        object.__setattr__(
            self,
            "output_depletion_extreme_bps",
            _require_u32("output_depletion_extreme_bps", self.output_depletion_extreme_bps, minimum=1),
        )
        object.__setattr__(
            self,
            "price_impact_extreme_bps",
            _require_u32("price_impact_extreme_bps", self.price_impact_extreme_bps, minimum=1),
        )


@dataclass(frozen=True)
class StrategyRouteEconomicSanityResult:
    ok: bool
    route_shape_supported_for_intents: bool
    extreme_input_stress_present: bool
    extreme_output_depletion_present: bool
    extreme_price_impact_present: bool
    error: str | None = None


def _route_shape_supported(*, inputs: StrategyRouteEconomicSanityInputs) -> bool:
    return (
        inputs.receipt_verified
        and inputs.route_kind_supported
        and inputs.body_pair_valid
        and inputs.legs_present
        and inputs.all_legs_single_hop
        and inputs.all_legs_match_body_pair
        and not inputs.multi_hop_present
    )


def _classification_error(
    *,
    inputs: StrategyRouteEconomicSanityInputs,
    policy: StrategyRouteEconomicSanityPolicy,
    route_shape_supported_for_intents: bool,
    extreme_input_stress_present: bool,
    extreme_output_depletion_present: bool,
    extreme_price_impact_present: bool,
) -> str | None:
    if not inputs.receipt_verified:
        return "route_receipt_unverified"
    if not inputs.route_kind_supported:
        return "route_kind_unsupported"
    if not inputs.body_pair_valid:
        return "route_body_pair_invalid"
    if not inputs.legs_present:
        return "route_legs_missing"
    if not inputs.all_legs_match_body_pair:
        return "route_mixed_asset_pairs"
    if not route_shape_supported_for_intents:
        return "route_multi_hop_unsupported"
    if extreme_input_stress_present:
        return (
            "route_extreme_input_stress:"
            f"max={inputs.max_hop_input_vs_reserve_bps},threshold={policy.input_stress_extreme_bps}"
        )
    if extreme_output_depletion_present:
        return (
            "route_extreme_output_depletion:"
            f"max={inputs.max_hop_output_vs_reserve_bps},threshold={policy.output_depletion_extreme_bps}"
        )
    if extreme_price_impact_present:
        return (
            "route_extreme_price_impact:"
            f"max={inputs.max_hop_price_impact_bps},threshold={policy.price_impact_extreme_bps}"
        )
    return None


def check_strategy_route_economic_sanity(
    *,
    inputs: StrategyRouteEconomicSanityInputs,
    policy: StrategyRouteEconomicSanityPolicy,
) -> StrategyRouteEconomicSanityResult:
    if not isinstance(inputs, StrategyRouteEconomicSanityInputs):
        raise TypeError("inputs must be a StrategyRouteEconomicSanityInputs")
    if not isinstance(policy, StrategyRouteEconomicSanityPolicy):
        raise TypeError("policy must be a StrategyRouteEconomicSanityPolicy")

    route_shape_supported_for_intents = _route_shape_supported(inputs=inputs)
    extreme_input_stress_present = inputs.max_hop_input_vs_reserve_bps >= policy.input_stress_extreme_bps
    extreme_output_depletion_present = inputs.max_hop_output_vs_reserve_bps >= policy.output_depletion_extreme_bps
    extreme_price_impact_present = inputs.max_hop_price_impact_bps >= policy.price_impact_extreme_bps
    if (
        route_shape_supported_for_intents
        and not extreme_input_stress_present
        and not extreme_output_depletion_present
        and not extreme_price_impact_present
    ):
        return StrategyRouteEconomicSanityResult(
            ok=True,
            route_shape_supported_for_intents=True,
            extreme_input_stress_present=False,
            extreme_output_depletion_present=False,
            extreme_price_impact_present=False,
        )

    return StrategyRouteEconomicSanityResult(
        ok=False,
        route_shape_supported_for_intents=route_shape_supported_for_intents,
        extreme_input_stress_present=extreme_input_stress_present,
        extreme_output_depletion_present=extreme_output_depletion_present,
        extreme_price_impact_present=extreme_price_impact_present,
        error=_classification_error(
            inputs=inputs,
            policy=policy,
            route_shape_supported_for_intents=route_shape_supported_for_intents,
            extreme_input_stress_present=extreme_input_stress_present,
            extreme_output_depletion_present=extreme_output_depletion_present,
            extreme_price_impact_present=extreme_price_impact_present,
        ),
    )
