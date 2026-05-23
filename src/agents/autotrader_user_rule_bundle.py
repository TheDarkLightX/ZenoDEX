from __future__ import annotations

import json
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Mapping

from .autotrader_client_policy_bundle import (
    AutoTraderClientPolicyBundle,
    build_autotrader_client_policy_bundle,
)
from .autotrader_client_policy_surface import (
    AutoTraderClientPolicySurface,
    build_autotrader_client_policy_surface,
)
from .autotrader_local_guard_evaluator import (
    AutoTraderLocalGuardEvaluation,
    AutoTraderLocalGuardInputs,
)
from .policy_artifacts import (
    StrategyPolicyArtifact,
    StrategySourceArtifact,
    TauPolicyBundle,
    build_strategy_source_artifact,
)
from .strategy_ir import (
    AUTOTRADER_TAU_POLICY_SPECS,
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyControls,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from ..state.canonical import canonical_json_bytes, sha256_hex

AUTOTRADER_USER_RULE_BUNDLE_SCHEMA = "zenodex/autotrader-user-rule-bundle/v1"
DEFAULT_AUTOTRADER_USER_RULE_BUNDLE_COMPILER_VERSION = "autotrader-user-rule-bundle/v1"
_USER_RULE_SOURCE_FORM = "autotrader_user_rule_bundle"


class AutoTraderUserRuleMode(Enum):
    DCA_SWAP_EXACT_IN = "dca_swap_exact_in"
    STOP_LOSS_ORDER_INTENT = "stop_loss_order_intent"
    TAKE_PROFIT_ORDER_INTENT = "take_profit_order_intent"


class AutoTraderUserRulePreset(Enum):
    CAPITAL_PRESERVATION_DCA = "capital_preservation_dca"
    CONSERVATIVE_DCA = "conservative_dca"
    BALANCED_DCA = "balanced_dca"
    PRICE_DISCIPLINE_DCA = "price_discipline_dca"
    HIGH_THROUGHPUT_DCA = "high_throughput_dca"
    PROTECTIVE_STOP_LOSS = "protective_stop_loss"
    DISCIPLINED_TAKE_PROFIT = "disciplined_take_profit"


@dataclass(frozen=True)
class _AutoTraderUserRulePresetSpec:
    mode: AutoTraderUserRuleMode
    per_window_orders: int
    lifetime_orders: int
    max_slippage_bps: int
    max_oracle_staleness_epochs: int
    min_order_spacing_epochs: int
    max_live_orders: int
    require_quote_receipts: bool = True
    kill_switch_enabled: bool = True


_PRESET_SPECS: dict[AutoTraderUserRulePreset, _AutoTraderUserRulePresetSpec] = {
    AutoTraderUserRulePreset.CAPITAL_PRESERVATION_DCA: _AutoTraderUserRulePresetSpec(
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        per_window_orders=2,
        lifetime_orders=16,
        max_slippage_bps=20,
        max_oracle_staleness_epochs=1,
        min_order_spacing_epochs=6,
        max_live_orders=1,
    ),
    AutoTraderUserRulePreset.CONSERVATIVE_DCA: _AutoTraderUserRulePresetSpec(
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        per_window_orders=4,
        lifetime_orders=24,
        max_slippage_bps=30,
        max_oracle_staleness_epochs=2,
        min_order_spacing_epochs=4,
        max_live_orders=2,
    ),
    AutoTraderUserRulePreset.BALANCED_DCA: _AutoTraderUserRulePresetSpec(
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        per_window_orders=6,
        lifetime_orders=36,
        max_slippage_bps=75,
        max_oracle_staleness_epochs=3,
        min_order_spacing_epochs=2,
        max_live_orders=3,
    ),
    AutoTraderUserRulePreset.PRICE_DISCIPLINE_DCA: _AutoTraderUserRulePresetSpec(
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        per_window_orders=5,
        lifetime_orders=30,
        max_slippage_bps=20,
        max_oracle_staleness_epochs=3,
        min_order_spacing_epochs=3,
        max_live_orders=2,
    ),
    AutoTraderUserRulePreset.HIGH_THROUGHPUT_DCA: _AutoTraderUserRulePresetSpec(
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        per_window_orders=10,
        lifetime_orders=60,
        max_slippage_bps=150,
        max_oracle_staleness_epochs=5,
        min_order_spacing_epochs=1,
        max_live_orders=5,
    ),
    AutoTraderUserRulePreset.PROTECTIVE_STOP_LOSS: _AutoTraderUserRulePresetSpec(
        mode=AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT,
        per_window_orders=1,
        lifetime_orders=12,
        max_slippage_bps=25,
        max_oracle_staleness_epochs=1,
        min_order_spacing_epochs=0,
        max_live_orders=1,
    ),
    AutoTraderUserRulePreset.DISCIPLINED_TAKE_PROFIT: _AutoTraderUserRulePresetSpec(
        mode=AutoTraderUserRuleMode.TAKE_PROFIT_ORDER_INTENT,
        per_window_orders=2,
        lifetime_orders=18,
        max_slippage_bps=40,
        max_oracle_staleness_epochs=2,
        min_order_spacing_epochs=1,
        max_live_orders=2,
    ),
}


_PRESET_HUMAN_PROFILES: dict[AutoTraderUserRulePreset, dict[str, str]] = {
    AutoTraderUserRulePreset.CAPITAL_PRESERVATION_DCA: {
        "label": "Capital Preservation DCA",
        "optimize_for": "capital_preservation",
        "summary": "Accumulate only under the tightest execution conditions with minimal concurrency and the strictest oracle freshness posture.",
        "tradeoffs": "Highest skip rate and slowest accumulation in exchange for the narrowest risk envelope.",
        "cadence_posture": "very_spaced",
        "slippage_posture": "very_tight",
        "freshness_posture": "very_strict",
        "concurrency_posture": "minimal",
    },
    AutoTraderUserRulePreset.CONSERVATIVE_DCA: {
        "label": "Conservative DCA",
        "optimize_for": "execution_safety",
        "summary": "Accumulate slowly with tighter slippage, stricter oracle freshness, and fewer concurrent live orders.",
        "tradeoffs": "Lower throughput and fewer stressed-market fills in exchange for tighter execution posture.",
        "cadence_posture": "spaced",
        "slippage_posture": "tight",
        "freshness_posture": "strict",
        "concurrency_posture": "low",
    },
    AutoTraderUserRulePreset.BALANCED_DCA: {
        "label": "Balanced DCA",
        "optimize_for": "balanced_execution",
        "summary": "Accumulate on a steadier schedule with moderate slippage and oracle-freshness limits.",
        "tradeoffs": "Accepts more opportunities than the conservative preset without opening the full risk envelope.",
        "cadence_posture": "balanced",
        "slippage_posture": "moderate",
        "freshness_posture": "balanced",
        "concurrency_posture": "medium",
    },
    AutoTraderUserRulePreset.PRICE_DISCIPLINE_DCA: {
        "label": "Price Discipline DCA",
        "optimize_for": "price_discipline",
        "summary": "Accumulate steadily while prioritizing tighter execution prices over raw fill frequency.",
        "tradeoffs": "Skips more wide-spread opportunities than balanced execution, but remains less restrictive than capital preservation.",
        "cadence_posture": "measured",
        "slippage_posture": "very_tight",
        "freshness_posture": "balanced",
        "concurrency_posture": "low",
    },
    AutoTraderUserRulePreset.HIGH_THROUGHPUT_DCA: {
        "label": "High-Throughput DCA",
        "optimize_for": "throughput",
        "summary": "Accumulate aggressively with looser slippage and freshness limits and higher live-order concurrency.",
        "tradeoffs": "Higher execution risk and less conservative market filtering in exchange for more opportunities.",
        "cadence_posture": "aggressive",
        "slippage_posture": "loose",
        "freshness_posture": "permissive",
        "concurrency_posture": "high",
    },
    AutoTraderUserRulePreset.PROTECTIVE_STOP_LOSS: {
        "label": "Protective Stop-Loss",
        "optimize_for": "downside_protection",
        "summary": "Exit under the strictest trigger-driven posture with the freshest quotes and minimal concurrency.",
        "tradeoffs": "Most likely to skip weakly supported exits in exchange for the tightest downside-protection posture.",
        "cadence_posture": "event_driven",
        "slippage_posture": "very_tight",
        "freshness_posture": "very_strict",
        "concurrency_posture": "minimal",
    },
    AutoTraderUserRulePreset.DISCIPLINED_TAKE_PROFIT: {
        "label": "Disciplined Take-Profit",
        "optimize_for": "profit_realization",
        "summary": "Realize gains with trigger-driven exits while keeping pricing and oracle posture tighter than a throughput-oriented strategy.",
        "tradeoffs": "Will skip more marginal take-profit opportunities in exchange for tighter realized execution posture.",
        "cadence_posture": "event_driven",
        "slippage_posture": "tight",
        "freshness_posture": "strict",
        "concurrency_posture": "low",
    },
}


def _surface_support_entry(
    *,
    supported: bool,
    current_executor: str,
    reject_reason: str | None,
) -> dict[str, Any]:
    return {
        "supported": supported,
        "status": "supported" if supported else "rejected",
        "current_executor": current_executor,
        "reject_reason_when_unsupported": (None if supported else reject_reason),
    }



def describe_autotrader_user_rule_surface_support(
    mode: AutoTraderUserRuleMode | str,
) -> dict[str, Any]:
    if isinstance(mode, str):
        mode_value = AutoTraderUserRuleMode(mode)
    elif isinstance(mode, AutoTraderUserRuleMode):
        mode_value = mode
    else:
        raise TypeError("mode must be an AutoTraderUserRuleMode or string")

    compile_entry = _surface_support_entry(
        supported=True,
        current_executor="autotrader_user_rule_bundle_compiler_v1",
        reject_reason=None,
    )
    shadow_supported = mode_value is AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN
    live_supported = mode_value is AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN
    shadow_entry = _surface_support_entry(
        supported=shadow_supported,
        current_executor="dca_shadow_exact_in_only",
        reject_reason="unsupported_shadow_strategy_mode",
    )
    live_entry = _surface_support_entry(
        supported=live_supported,
        current_executor="dca_swap_exact_in_only",
        reject_reason="unsupported_live_strategy_mode",
    )
    if shadow_supported and live_supported:
        overall_status = "supported"
    elif shadow_supported:
        overall_status = "shadow_only"
    else:
        overall_status = "compile_only"
    return {
        "overall_status": overall_status,
        "compile": compile_entry,
        "shadow": shadow_entry,
        "live": live_entry,
    }



def describe_autotrader_strategy_surface_support(strategy: StrategyIR) -> dict[str, Any]:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if (
        strategy.template is StrategyTemplate.DCA
        and strategy.allowed_actions == (StrategyAction.PLACE_SWAP_EXACT_IN,)
    ):
        return describe_autotrader_user_rule_surface_support(
            AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN
        )
    if (
        strategy.template is StrategyTemplate.STOP_LOSS
        and strategy.allowed_actions == (StrategyAction.PLACE_ORDER_INTENT,)
    ):
        return describe_autotrader_user_rule_surface_support(
            AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT
        )
    if (
        strategy.template is StrategyTemplate.TAKE_PROFIT
        and strategy.allowed_actions == (StrategyAction.PLACE_ORDER_INTENT,)
    ):
        return describe_autotrader_user_rule_surface_support(
            AutoTraderUserRuleMode.TAKE_PROFIT_ORDER_INTENT
        )
    return {
        "overall_status": "compile_only",
        "compile": _surface_support_entry(
            supported=True,
            current_executor="strategy_ir_compiler",
            reject_reason=None,
        ),
        "shadow": _surface_support_entry(
            supported=False,
            current_executor="dca_shadow_exact_in_only",
            reject_reason="unsupported_shadow_strategy_mode",
        ),
        "live": _surface_support_entry(
            supported=False,
            current_executor="dca_swap_exact_in_only",
            reject_reason="unsupported_live_strategy_mode",
        ),
    }



def list_autotrader_user_rule_presets(
    *,
    live_supported_only: bool = False,
    fail_closed_only: bool = False,
) -> tuple[dict[str, Any], ...]:
    if live_supported_only and fail_closed_only:
        raise ValueError("live_supported_only and fail_closed_only are mutually exclusive")
    out: list[dict[str, Any]] = []
    for preset in AutoTraderUserRulePreset:
        description = describe_autotrader_user_rule_preset(preset)
        if description is None:
            continue
        live_posture = description.get("live_execution_posture")
        supported = None
        if isinstance(live_posture, Mapping):
            raw_supported = live_posture.get("supported")
            if isinstance(raw_supported, bool):
                supported = raw_supported
        if live_supported_only and supported is not True:
            continue
        if fail_closed_only and supported is not False:
            continue
        out.append(description)
    return tuple(out)


def recommend_autotrader_user_rule_preset(
    *,
    desired_user_rule_mode: str | None = None,
    desired_optimize_for: str | None = None,
    desired_max_slippage_bps: int | None = None,
    desired_max_oracle_staleness_epochs: int | None = None,
    desired_max_live_orders: int | None = None,
    require_live_supported: bool = False,
) -> dict[str, Any]:
    if (
        desired_user_rule_mode is None
        and desired_optimize_for is None
        and desired_max_slippage_bps is None
        and desired_max_oracle_staleness_epochs is None
        and desired_max_live_orders is None
        and not require_live_supported
    ):
        raise ValueError("preset recommendation requires at least one criterion")

    ranked_candidates: list[dict[str, Any]] = []
    for preset in AutoTraderUserRulePreset:
        description = describe_autotrader_user_rule_preset(preset)
        if description is None:
            continue
        live_posture = description.get("live_execution_posture")
        live_supported = None
        if isinstance(live_posture, Mapping):
            raw_supported = live_posture.get("supported")
            if isinstance(raw_supported, bool):
                live_supported = raw_supported
        if require_live_supported and live_supported is not True:
            continue
        guard_profile = description.get("guard_profile")
        if not isinstance(guard_profile, Mapping):
            continue
        breakdown: dict[str, int] = {}
        total_penalty = 0
        if desired_user_rule_mode is not None:
            if description.get("mode") != desired_user_rule_mode:
                continue
            breakdown["user_rule_mode_penalty"] = 0
        if desired_optimize_for is not None:
            optimize_penalty = 0 if description.get("optimize_for") == desired_optimize_for else 1000
            breakdown["optimize_for_penalty"] = optimize_penalty
            total_penalty += optimize_penalty
        if desired_max_slippage_bps is not None:
            slippage_penalty = abs(int(guard_profile.get("max_slippage_bps", 0)) - desired_max_slippage_bps)
            breakdown["max_slippage_bps_penalty"] = slippage_penalty
            total_penalty += slippage_penalty
        if desired_max_oracle_staleness_epochs is not None:
            freshness_penalty = abs(
                int(guard_profile.get("max_oracle_staleness_epochs", 0))
                - desired_max_oracle_staleness_epochs
            )
            breakdown["max_oracle_staleness_epochs_penalty"] = freshness_penalty
            total_penalty += freshness_penalty
        if desired_max_live_orders is not None:
            concurrency_penalty = abs(int(guard_profile.get("max_live_orders", 0)) - desired_max_live_orders)
            breakdown["max_live_orders_penalty"] = concurrency_penalty
            total_penalty += concurrency_penalty
        ranked_candidates.append(
            {
                "preset_id": description["preset_id"],
                "label": description["label"],
                "optimize_for": description["optimize_for"],
                "total_penalty": total_penalty,
                "penalty_breakdown": breakdown,
            }
        )

    if not ranked_candidates:
        raise ValueError("no presets satisfy the requested recommendation constraints")
    ranked_candidates.sort(
        key=lambda row: (
            int(row["total_penalty"]),
            str(row["preset_id"]),
        )
    )
    recommended_preset_id = str(ranked_candidates[0]["preset_id"])
    recommended_preset = describe_autotrader_user_rule_preset(recommended_preset_id)
    if recommended_preset is None:
        raise ValueError("failed to resolve recommended preset")
    return {
        "criteria": {
            "desired_user_rule_mode": desired_user_rule_mode,
            "desired_optimize_for": desired_optimize_for,
            "desired_max_slippage_bps": desired_max_slippage_bps,
            "desired_max_oracle_staleness_epochs": desired_max_oracle_staleness_epochs,
            "desired_max_live_orders": desired_max_live_orders,
            "require_live_supported": require_live_supported,
        },
        "recommended_preset": recommended_preset,
        "ranked_candidates": ranked_candidates,
    }


def compare_autotrader_user_rule_presets(
    left_preset_id: AutoTraderUserRulePreset | str,
    right_preset_id: AutoTraderUserRulePreset | str,
) -> dict[str, Any]:
    left = describe_autotrader_user_rule_preset(left_preset_id)
    right = describe_autotrader_user_rule_preset(right_preset_id)
    if left is None or right is None:
        raise ValueError("preset comparison requires two known presets")

    def _diff_mapping(left_map: object, right_map: object) -> dict[str, dict[str, Any]]:
        if not isinstance(left_map, Mapping) or not isinstance(right_map, Mapping):
            return {}
        keys = sorted(set(left_map.keys()) | set(right_map.keys()))
        out: dict[str, dict[str, Any]] = {}
        for key in keys:
            left_value = left_map.get(key)
            right_value = right_map.get(key)
            if left_value != right_value:
                out[str(key)] = {
                    "left": left_value,
                    "right": right_value,
                }
        return out

    top_level_deltas = {
        key: {"left": left.get(key), "right": right.get(key)}
        for key in ("mode", "label", "optimize_for", "summary", "tradeoffs")
        if left.get(key) != right.get(key)
    }
    operating_profile_deltas = _diff_mapping(
        left.get("operating_profile"),
        right.get("operating_profile"),
    )
    guard_profile_deltas = _diff_mapping(
        left.get("guard_profile"),
        right.get("guard_profile"),
    )
    return {
        "left": left,
        "right": right,
        "top_level_deltas": top_level_deltas,
        "operating_profile_deltas": operating_profile_deltas,
        "guard_profile_deltas": guard_profile_deltas,
    }


def describe_autotrader_user_rule_preset(
    preset_id: AutoTraderUserRulePreset | str | None,
) -> dict[str, Any] | None:
    if preset_id is None:
        return None
    if isinstance(preset_id, str):
        preset = AutoTraderUserRulePreset(preset_id)
    elif isinstance(preset_id, AutoTraderUserRulePreset):
        preset = preset_id
    else:
        raise TypeError("preset_id must be an AutoTraderUserRulePreset, string, or None")
    spec = _PRESET_SPECS[preset]
    human = _PRESET_HUMAN_PROFILES[preset]
    authoring_requirements = {
        "required_common_parameters": [
            "asset_in",
            "asset_out",
            "fixed_order_size",
            "valid_from_epoch",
            "valid_until_epoch",
        ],
        "requires_cadence_epochs": spec.mode is AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        "requires_trigger_price": spec.mode in (
            AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT,
            AutoTraderUserRuleMode.TAKE_PROFIT_ORDER_INTENT,
        ),
    }
    surface_support_matrix = describe_autotrader_user_rule_surface_support(spec.mode)
    live_execution_posture = dict(surface_support_matrix["live"])
    return {
        "preset_id": preset.value,
        "mode": spec.mode.value,
        "label": human["label"],
        "optimize_for": human["optimize_for"],
        "summary": human["summary"],
        "tradeoffs": human["tradeoffs"],
        "authoring_requirements": authoring_requirements,
        "overall_support_status": surface_support_matrix["overall_status"],
        "surface_support_matrix": surface_support_matrix,
        "live_execution_posture": live_execution_posture,
        "operating_profile": {
            "cadence_posture": human["cadence_posture"],
            "slippage_posture": human["slippage_posture"],
            "freshness_posture": human["freshness_posture"],
            "concurrency_posture": human["concurrency_posture"],
        },
        "guard_profile": {
            "per_window_orders": int(spec.per_window_orders),
            "lifetime_orders": int(spec.lifetime_orders),
            "max_slippage_bps": int(spec.max_slippage_bps),
            "max_oracle_staleness_epochs": int(spec.max_oracle_staleness_epochs),
            "min_order_spacing_epochs": int(spec.min_order_spacing_epochs),
            "max_live_orders": int(spec.max_live_orders),
            "require_quote_receipts": bool(spec.require_quote_receipts),
            "kill_switch_enabled": bool(spec.kill_switch_enabled),
        },
    }


def _require_text(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text



def _require_int(value: object, *, name: str, minimum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if minimum is not None and out < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    return out



def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value



def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)



def _require_isoish_timestamp(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if "T" not in text:
        raise ValueError(f"{name} must be an ISO-like timestamp")
    return text


@dataclass(frozen=True)
class AutoTraderUserMarket:
    asset_in: str
    asset_out: str

    def __post_init__(self) -> None:
        asset_in = _require_text(self.asset_in, name="asset_in")
        asset_out = _require_text(self.asset_out, name="asset_out")
        if asset_in == asset_out:
            raise ValueError("asset_in and asset_out must be distinct")
        object.__setattr__(self, "asset_in", asset_in)
        object.__setattr__(self, "asset_out", asset_out)

    def to_dict(self) -> dict[str, str]:
        return {
            "asset_in": self.asset_in,
            "asset_out": self.asset_out,
        }


@dataclass(frozen=True)
class AutoTraderUserSizingRule:
    fixed_order_size: int
    cadence_epochs: int | None = None

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "fixed_order_size",
            _require_int(self.fixed_order_size, name="fixed_order_size", minimum=1),
        )
        cadence_epochs = self.cadence_epochs
        if cadence_epochs is not None:
            cadence_epochs = _require_int(cadence_epochs, name="cadence_epochs", minimum=1)
        object.__setattr__(self, "cadence_epochs", cadence_epochs)

    def to_dict(self) -> dict[str, int]:
        payload = {
            "fixed_order_size": int(self.fixed_order_size),
        }
        if self.cadence_epochs is not None:
            payload["cadence_epochs"] = int(self.cadence_epochs)
        return payload


@dataclass(frozen=True)
class AutoTraderUserTriggerRule:
    trigger_price: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "trigger_price",
            _require_int(self.trigger_price, name="trigger_price", minimum=1),
        )

    def to_dict(self) -> dict[str, int]:
        return {
            "trigger_price": int(self.trigger_price),
        }


@dataclass(frozen=True)
class AutoTraderUserBudgetRule:
    per_window_max: int
    lifetime_max: int

    def __post_init__(self) -> None:
        per_window_max = _require_int(self.per_window_max, name="per_window_max", minimum=1)
        lifetime_max = _require_int(self.lifetime_max, name="lifetime_max", minimum=1)
        if per_window_max > lifetime_max:
            raise ValueError("per_window_max must be <= lifetime_max")
        object.__setattr__(self, "per_window_max", per_window_max)
        object.__setattr__(self, "lifetime_max", lifetime_max)

    def to_dict(self) -> dict[str, int]:
        return {
            "per_window_max": int(self.per_window_max),
            "lifetime_max": int(self.lifetime_max),
        }


@dataclass(frozen=True)
class AutoTraderUserRiskRule:
    max_slippage_bps: int
    max_oracle_staleness_epochs: int
    require_quote_receipts: bool = True

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "max_slippage_bps",
            _require_int(self.max_slippage_bps, name="max_slippage_bps", minimum=0),
        )
        object.__setattr__(
            self,
            "max_oracle_staleness_epochs",
            _require_int(
                self.max_oracle_staleness_epochs,
                name="max_oracle_staleness_epochs",
                minimum=1,
            ),
        )
        if not isinstance(self.require_quote_receipts, bool):
            raise TypeError("require_quote_receipts must be a bool")

    def to_dict(self) -> dict[str, int | bool]:
        return {
            "max_slippage_bps": int(self.max_slippage_bps),
            "max_oracle_staleness_epochs": int(self.max_oracle_staleness_epochs),
            "require_quote_receipts": bool(self.require_quote_receipts),
        }


@dataclass(frozen=True)
class AutoTraderUserWindowRule:
    valid_from_epoch: int
    valid_until_epoch: int
    min_order_spacing_epochs: int = 0

    def __post_init__(self) -> None:
        valid_from_epoch = _require_int(self.valid_from_epoch, name="valid_from_epoch", minimum=0)
        valid_until_epoch = _require_int(self.valid_until_epoch, name="valid_until_epoch", minimum=0)
        min_order_spacing_epochs = _require_int(
            self.min_order_spacing_epochs,
            name="min_order_spacing_epochs",
            minimum=0,
        )
        if valid_from_epoch > valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        object.__setattr__(self, "valid_from_epoch", valid_from_epoch)
        object.__setattr__(self, "valid_until_epoch", valid_until_epoch)
        object.__setattr__(self, "min_order_spacing_epochs", min_order_spacing_epochs)

    def to_dict(self) -> dict[str, int]:
        return {
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
            "min_order_spacing_epochs": int(self.min_order_spacing_epochs),
        }


@dataclass(frozen=True)
class AutoTraderUserControlRule:
    kill_switch_enabled: bool = True
    max_live_orders: int = 3

    def __post_init__(self) -> None:
        if not isinstance(self.kill_switch_enabled, bool):
            raise TypeError("kill_switch_enabled must be a bool")
        object.__setattr__(
            self,
            "max_live_orders",
            _require_int(self.max_live_orders, name="max_live_orders", minimum=1),
        )

    def to_dict(self) -> dict[str, int | bool]:
        return {
            "kill_switch_enabled": bool(self.kill_switch_enabled),
            "max_live_orders": int(self.max_live_orders),
        }


@dataclass(frozen=True)
class AutoTraderUserRuleBundle:
    bundle_name: str
    built_at: str
    compiler_version: str
    strategy_id: str
    owner_pubkey: str
    policy_backend: PolicyBackend
    mode: AutoTraderUserRuleMode
    market: AutoTraderUserMarket
    sizing: AutoTraderUserSizingRule
    budget: AutoTraderUserBudgetRule
    risk: AutoTraderUserRiskRule
    window: AutoTraderUserWindowRule
    trigger: AutoTraderUserTriggerRule | None = None
    preset_id: AutoTraderUserRulePreset | None = None
    controls: AutoTraderUserControlRule = field(default_factory=AutoTraderUserControlRule)

    def __post_init__(self) -> None:
        object.__setattr__(self, "bundle_name", _require_text(self.bundle_name, name="bundle_name"))
        object.__setattr__(self, "built_at", _require_isoish_timestamp(self.built_at, name="built_at"))
        object.__setattr__(
            self,
            "compiler_version",
            _require_text(self.compiler_version, name="compiler_version"),
        )
        object.__setattr__(self, "strategy_id", _require_text(self.strategy_id, name="strategy_id"))
        object.__setattr__(self, "owner_pubkey", _require_text(self.owner_pubkey, name="owner_pubkey"))
        if not isinstance(self.policy_backend, PolicyBackend):
            raise TypeError("policy_backend must be a PolicyBackend")
        if not isinstance(self.mode, AutoTraderUserRuleMode):
            raise TypeError("mode must be an AutoTraderUserRuleMode")
        if self.preset_id is not None and not isinstance(self.preset_id, AutoTraderUserRulePreset):
            raise TypeError("preset_id must be an AutoTraderUserRulePreset when present")
        if not isinstance(self.market, AutoTraderUserMarket):
            raise TypeError("market must be an AutoTraderUserMarket")
        if not isinstance(self.sizing, AutoTraderUserSizingRule):
            raise TypeError("sizing must be an AutoTraderUserSizingRule")
        if not isinstance(self.budget, AutoTraderUserBudgetRule):
            raise TypeError("budget must be an AutoTraderUserBudgetRule")
        if not isinstance(self.risk, AutoTraderUserRiskRule):
            raise TypeError("risk must be an AutoTraderUserRiskRule")
        if not isinstance(self.window, AutoTraderUserWindowRule):
            raise TypeError("window must be an AutoTraderUserWindowRule")
        if self.trigger is not None and not isinstance(self.trigger, AutoTraderUserTriggerRule):
            raise TypeError("trigger must be an AutoTraderUserTriggerRule when present")
        if not isinstance(self.controls, AutoTraderUserControlRule):
            raise TypeError("controls must be an AutoTraderUserControlRule")
        if self.mode is AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN:
            if self.sizing.cadence_epochs is None:
                raise ValueError("dca_swap_exact_in requires cadence_epochs")
            if self.trigger is not None:
                raise ValueError("dca_swap_exact_in does not accept trigger rules")
        elif self.mode in (
            AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT,
            AutoTraderUserRuleMode.TAKE_PROFIT_ORDER_INTENT,
        ):
            if self.sizing.cadence_epochs is not None:
                raise ValueError(f"{self.mode.value} does not accept cadence_epochs")
            if self.trigger is None:
                raise ValueError(f"{self.mode.value} requires trigger rules")
        if self.preset_id is not None:
            preset_description = describe_autotrader_user_rule_preset(self.preset_id)
            if preset_description is None:
                raise ValueError("preset_id must resolve to a known user-rule preset")
            preset_mode = preset_description.get("mode")
            if preset_mode != self.mode.value:
                raise ValueError("preset_id mode must match bundle mode")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": AUTOTRADER_USER_RULE_BUNDLE_SCHEMA,
            "bundle_name": self.bundle_name,
            "built_at": self.built_at,
            "compiler_version": self.compiler_version,
            "strategy_id": self.strategy_id,
            "owner_pubkey": self.owner_pubkey,
            "policy_backend": self.policy_backend.value,
            "mode": self.mode.value,
            "preset_id": None if self.preset_id is None else self.preset_id.value,
            "market": self.market.to_dict(),
            "strategy_rules": self.sizing.to_dict(),
            "trigger_rules": None if self.trigger is None else self.trigger.to_dict(),
            "budget_rules": self.budget.to_dict(),
            "risk_rules": self.risk.to_dict(),
            "window_rules": self.window.to_dict(),
            "controls": self.controls.to_dict(),
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["user_rule_bundle_hash"] = self.user_rule_bundle_hash_hex()
        return payload

    def to_json_bytes(self) -> bytes:
        return canonical_json_bytes(self.to_unsigned_dict())

    def user_rule_bundle_hash_hex(self) -> str:
        return sha256_hex(self.to_json_bytes())



def build_autotrader_user_rule_bundle_from_preset(
    *,
    bundle_name: str,
    built_at: str,
    strategy_id: str,
    owner_pubkey: str,
    policy_backend: PolicyBackend,
    preset_id: AutoTraderUserRulePreset,
    market: AutoTraderUserMarket,
    fixed_order_size: int,
    valid_from_epoch: int,
    valid_until_epoch: int,
    cadence_epochs: int | None = None,
    trigger_price: int | None = None,
) -> AutoTraderUserRuleBundle:
    if not isinstance(policy_backend, PolicyBackend):
        raise TypeError("policy_backend must be a PolicyBackend")
    if not isinstance(preset_id, AutoTraderUserRulePreset):
        raise TypeError("preset_id must be an AutoTraderUserRulePreset")
    if not isinstance(market, AutoTraderUserMarket):
        raise TypeError("market must be an AutoTraderUserMarket")
    spec = _PRESET_SPECS[preset_id]
    fixed_order_size_value = _require_int(fixed_order_size, name="fixed_order_size", minimum=1)
    cadence_value: int | None = None
    trigger_rule: AutoTraderUserTriggerRule | None = None
    if spec.mode is AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN:
        if cadence_epochs is None:
            raise ValueError(f"{preset_id.value} requires cadence_epochs")
        if trigger_price is not None:
            raise ValueError(f"{preset_id.value} does not accept trigger_price")
        cadence_value = _require_int(cadence_epochs, name="cadence_epochs", minimum=1)
    else:
        if cadence_epochs is not None:
            raise ValueError(f"{preset_id.value} does not accept cadence_epochs")
        if trigger_price is None:
            raise ValueError(f"{preset_id.value} requires trigger_price")
        trigger_rule = AutoTraderUserTriggerRule(
            trigger_price=_require_int(trigger_price, name="trigger_price", minimum=1)
        )
    sizing = AutoTraderUserSizingRule(
        fixed_order_size=fixed_order_size_value,
        cadence_epochs=cadence_value,
    )
    return AutoTraderUserRuleBundle(
        bundle_name=bundle_name,
        built_at=built_at,
        compiler_version=DEFAULT_AUTOTRADER_USER_RULE_BUNDLE_COMPILER_VERSION,
        strategy_id=strategy_id,
        owner_pubkey=owner_pubkey,
        policy_backend=policy_backend,
        mode=spec.mode,
        preset_id=preset_id,
        market=market,
        sizing=sizing,
        budget=AutoTraderUserBudgetRule(
            per_window_max=sizing.fixed_order_size * spec.per_window_orders,
            lifetime_max=sizing.fixed_order_size * spec.lifetime_orders,
        ),
        risk=AutoTraderUserRiskRule(
            max_slippage_bps=spec.max_slippage_bps,
            max_oracle_staleness_epochs=spec.max_oracle_staleness_epochs,
            require_quote_receipts=spec.require_quote_receipts,
        ),
        window=AutoTraderUserWindowRule(
            valid_from_epoch=valid_from_epoch,
            valid_until_epoch=valid_until_epoch,
            min_order_spacing_epochs=spec.min_order_spacing_epochs,
        ),
        trigger=trigger_rule,
        controls=AutoTraderUserControlRule(
            kill_switch_enabled=spec.kill_switch_enabled,
            max_live_orders=spec.max_live_orders,
        ),
    )


def build_autotrader_user_rule_bundle_from_mode(
    *,
    bundle_name: str,
    built_at: str,
    strategy_id: str,
    owner_pubkey: str,
    policy_backend: PolicyBackend,
    mode: AutoTraderUserRuleMode,
    market: AutoTraderUserMarket,
    fixed_order_size: int,
    per_window_max: int,
    lifetime_max: int,
    max_slippage_bps: int,
    max_oracle_staleness_epochs: int,
    valid_from_epoch: int,
    valid_until_epoch: int,
    min_order_spacing_epochs: int = 0,
    require_quote_receipts: bool = True,
    kill_switch_enabled: bool = True,
    max_live_orders: int = 3,
    cadence_epochs: int | None = None,
    trigger_price: int | None = None,
) -> AutoTraderUserRuleBundle:
    if not isinstance(policy_backend, PolicyBackend):
        raise TypeError("policy_backend must be a PolicyBackend")
    if not isinstance(mode, AutoTraderUserRuleMode):
        raise TypeError("mode must be an AutoTraderUserRuleMode")
    if not isinstance(market, AutoTraderUserMarket):
        raise TypeError("market must be an AutoTraderUserMarket")
    sizing = AutoTraderUserSizingRule(
        fixed_order_size=_require_int(fixed_order_size, name="fixed_order_size", minimum=1),
        cadence_epochs=None
        if cadence_epochs is None
        else _require_int(cadence_epochs, name="cadence_epochs", minimum=1),
    )
    trigger = (
        None
        if trigger_price is None
        else AutoTraderUserTriggerRule(
            trigger_price=_require_int(trigger_price, name="trigger_price", minimum=1),
        )
    )
    return AutoTraderUserRuleBundle(
        bundle_name=bundle_name,
        built_at=built_at,
        compiler_version=DEFAULT_AUTOTRADER_USER_RULE_BUNDLE_COMPILER_VERSION,
        strategy_id=strategy_id,
        owner_pubkey=owner_pubkey,
        policy_backend=policy_backend,
        mode=mode,
        market=market,
        sizing=sizing,
        budget=AutoTraderUserBudgetRule(
            per_window_max=_require_int(per_window_max, name="per_window_max", minimum=1),
            lifetime_max=_require_int(lifetime_max, name="lifetime_max", minimum=1),
        ),
        risk=AutoTraderUserRiskRule(
            max_slippage_bps=_require_int(max_slippage_bps, name="max_slippage_bps", minimum=0),
            max_oracle_staleness_epochs=_require_int(
                max_oracle_staleness_epochs,
                name="max_oracle_staleness_epochs",
                minimum=1,
            ),
            require_quote_receipts=_require_bool(require_quote_receipts, name="require_quote_receipts"),
        ),
        window=AutoTraderUserWindowRule(
            valid_from_epoch=_require_int(valid_from_epoch, name="valid_from_epoch", minimum=0),
            valid_until_epoch=_require_int(valid_until_epoch, name="valid_until_epoch", minimum=0),
            min_order_spacing_epochs=_require_int(
                min_order_spacing_epochs,
                name="min_order_spacing_epochs",
                minimum=0,
            ),
        ),
        trigger=trigger,
        controls=AutoTraderUserControlRule(
            kill_switch_enabled=_require_bool(kill_switch_enabled, name="kill_switch_enabled"),
            max_live_orders=_require_int(max_live_orders, name="max_live_orders", minimum=1),
        ),
    )


def compile_autotrader_user_rule_bundle(bundle: AutoTraderUserRuleBundle) -> StrategyIR:
    if not isinstance(bundle, AutoTraderUserRuleBundle):
        raise TypeError("bundle must be an AutoTraderUserRuleBundle")
    tau_policy_specs: tuple[str, ...] = ()
    if bundle.policy_backend is PolicyBackend.TAU:
        tau_policy_specs = AUTOTRADER_TAU_POLICY_SPECS
    if bundle.mode is AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN:
        template = StrategyTemplate.DCA
        allowed_actions = (StrategyAction.PLACE_SWAP_EXACT_IN,)
        cadence_epochs = bundle.sizing.cadence_epochs
        if cadence_epochs is None:
            raise ValueError("dca_swap_exact_in requires cadence_epochs")
        template_params: dict[str, str | int | bool] = {
            "fixed_order_size": bundle.sizing.fixed_order_size,
            "cadence_epochs": cadence_epochs,
            "asset_in": bundle.market.asset_in,
            "asset_out": bundle.market.asset_out,
        }
    elif bundle.mode is AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT:
        template = StrategyTemplate.STOP_LOSS
        allowed_actions = (StrategyAction.PLACE_ORDER_INTENT,)
        if bundle.trigger is None:
            raise ValueError("stop_loss_order_intent requires trigger rules")
        template_params = {
            "trigger_price": bundle.trigger.trigger_price,
            "fixed_order_size": bundle.sizing.fixed_order_size,
            "asset_in": bundle.market.asset_in,
            "asset_out": bundle.market.asset_out,
        }
    elif bundle.mode is AutoTraderUserRuleMode.TAKE_PROFIT_ORDER_INTENT:
        template = StrategyTemplate.TAKE_PROFIT
        allowed_actions = (StrategyAction.PLACE_ORDER_INTENT,)
        if bundle.trigger is None:
            raise ValueError("take_profit_order_intent requires trigger rules")
        template_params = {
            "trigger_price": bundle.trigger.trigger_price,
            "fixed_order_size": bundle.sizing.fixed_order_size,
            "asset_in": bundle.market.asset_in,
            "asset_out": bundle.market.asset_out,
        }
    else:
        raise ValueError(f"unsupported user rule mode: {bundle.mode.value}")
    return StrategyIR(
        strategy_id=bundle.strategy_id,
        owner_pubkey=bundle.owner_pubkey,
        policy_backend=bundle.policy_backend,
        template=template,
        asset_universe=(bundle.market.asset_in, bundle.market.asset_out),
        allowed_actions=allowed_actions,
        notional_caps=NotionalCaps(
            per_order_max=bundle.sizing.fixed_order_size,
            per_window_max=bundle.budget.per_window_max,
            lifetime_max=bundle.budget.lifetime_max,
        ),
        risk_limits=RiskLimits(
            max_slippage_bps=bundle.risk.max_slippage_bps,
            max_oracle_staleness_epochs=bundle.risk.max_oracle_staleness_epochs,
            require_quote_receipts=bundle.risk.require_quote_receipts,
        ),
        strategy_window=StrategyWindow(
            valid_from_epoch=bundle.window.valid_from_epoch,
            valid_until_epoch=bundle.window.valid_until_epoch,
            min_order_spacing_epochs=bundle.window.min_order_spacing_epochs,
        ),
        controls=StrategyControls(
            kill_switch_enabled=bundle.controls.kill_switch_enabled,
            max_live_orders=bundle.controls.max_live_orders,
        ),
        template_params=template_params,
        tau_policy_specs=tau_policy_specs,
    )



def build_autotrader_user_rule_source_artifact(bundle: AutoTraderUserRuleBundle) -> StrategySourceArtifact:
    strategy = compile_autotrader_user_rule_bundle(bundle)
    return build_strategy_source_artifact(
        strategy=strategy,
        source_form=_USER_RULE_SOURCE_FORM,
        source_text=bundle.to_json_bytes().decode("utf-8"),
    )



def build_autotrader_client_policy_surface_from_user_rule_bundle(
    bundle: AutoTraderUserRuleBundle,
    *,
    tau_policy_bundle: TauPolicyBundle | None = None,
    policy_artifact: StrategyPolicyArtifact | None = None,
) -> AutoTraderClientPolicySurface:
    strategy = compile_autotrader_user_rule_bundle(bundle)
    source_artifact = build_autotrader_user_rule_source_artifact(bundle)
    return build_autotrader_client_policy_surface(
        strategy=strategy,
        source_artifact=source_artifact,
        source_preset_id=None if bundle.preset_id is None else bundle.preset_id.value,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )



def build_autotrader_client_policy_bundle_from_user_rule_bundle(
    bundle: AutoTraderUserRuleBundle,
    *,
    local_guard_evaluation: AutoTraderLocalGuardEvaluation | None = None,
    local_guard_inputs: AutoTraderLocalGuardInputs | None = None,
    tau_policy_bundle: TauPolicyBundle | None = None,
    policy_artifact: StrategyPolicyArtifact | None = None,
) -> AutoTraderClientPolicyBundle:
    surface = build_autotrader_client_policy_surface_from_user_rule_bundle(
        bundle,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )
    return build_autotrader_client_policy_bundle(
        bundle_name=bundle.bundle_name,
        built_at=bundle.built_at,
        client_policy_surface=surface,
        local_guard_evaluation=local_guard_evaluation,
        local_guard_inputs=local_guard_inputs,
    )



def autotrader_user_rule_bundle_from_dict(data: Mapping[str, Any]) -> AutoTraderUserRuleBundle:
    doc = _require_mapping(data, name="user rule bundle")
    schema = doc.get("schema")
    if schema is not None and schema != AUTOTRADER_USER_RULE_BUNDLE_SCHEMA:
        raise ValueError("unsupported autotrader user rule bundle schema")
    market = _require_mapping(doc.get("market"), name="market")
    strategy_rules = _require_mapping(doc.get("strategy_rules"), name="strategy_rules")
    trigger_rules_raw = doc.get("trigger_rules")
    budget_rules = _require_mapping(doc.get("budget_rules"), name="budget_rules")
    risk_rules = _require_mapping(doc.get("risk_rules"), name="risk_rules")
    window_rules = _require_mapping(doc.get("window_rules"), name="window_rules")
    controls = _require_mapping(doc.get("controls"), name="controls")
    bundle = AutoTraderUserRuleBundle(
        bundle_name=_require_text(doc.get("bundle_name"), name="bundle_name"),
        built_at=_require_text(doc.get("built_at"), name="built_at"),
        compiler_version=_require_text(
            doc.get("compiler_version", DEFAULT_AUTOTRADER_USER_RULE_BUNDLE_COMPILER_VERSION),
            name="compiler_version",
        ),
        strategy_id=_require_text(doc.get("strategy_id"), name="strategy_id"),
        owner_pubkey=_require_text(doc.get("owner_pubkey"), name="owner_pubkey"),
        policy_backend=PolicyBackend(_require_text(doc.get("policy_backend"), name="policy_backend")),
        mode=AutoTraderUserRuleMode(_require_text(doc.get("mode"), name="mode")),
        preset_id=(
            None
            if doc.get("preset_id") is None
            else AutoTraderUserRulePreset(_require_text(doc.get("preset_id"), name="preset_id"))
        ),
        market=AutoTraderUserMarket(
            asset_in=_require_text(market.get("asset_in"), name="market.asset_in"),
            asset_out=_require_text(market.get("asset_out"), name="market.asset_out"),
        ),
        sizing=AutoTraderUserSizingRule(
            fixed_order_size=_require_int(
                strategy_rules.get("fixed_order_size"),
                name="strategy_rules.fixed_order_size",
                minimum=1,
            ),
            cadence_epochs=(
                None
                if strategy_rules.get("cadence_epochs") is None
                else _require_int(
                    strategy_rules.get("cadence_epochs"),
                    name="strategy_rules.cadence_epochs",
                    minimum=1,
                )
            ),
        ),
        budget=AutoTraderUserBudgetRule(
            per_window_max=_require_int(
                budget_rules.get("per_window_max"),
                name="budget_rules.per_window_max",
                minimum=1,
            ),
            lifetime_max=_require_int(
                budget_rules.get("lifetime_max"),
                name="budget_rules.lifetime_max",
                minimum=1,
            ),
        ),
        risk=AutoTraderUserRiskRule(
            max_slippage_bps=_require_int(
                risk_rules.get("max_slippage_bps"),
                name="risk_rules.max_slippage_bps",
                minimum=0,
            ),
            max_oracle_staleness_epochs=_require_int(
                risk_rules.get("max_oracle_staleness_epochs"),
                name="risk_rules.max_oracle_staleness_epochs",
                minimum=1,
            ),
            require_quote_receipts=_require_bool(
                risk_rules.get("require_quote_receipts", True),
                name="risk_rules.require_quote_receipts",
            ),
        ),
        window=AutoTraderUserWindowRule(
            valid_from_epoch=_require_int(
                window_rules.get("valid_from_epoch"),
                name="window_rules.valid_from_epoch",
                minimum=0,
            ),
            valid_until_epoch=_require_int(
                window_rules.get("valid_until_epoch"),
                name="window_rules.valid_until_epoch",
                minimum=0,
            ),
            min_order_spacing_epochs=_require_int(
                window_rules.get("min_order_spacing_epochs", 0),
                name="window_rules.min_order_spacing_epochs",
                minimum=0,
            ),
        ),
        trigger=(
            None
            if trigger_rules_raw is None
            else AutoTraderUserTriggerRule(
                trigger_price=_require_int(
                    _require_mapping(trigger_rules_raw, name="trigger_rules").get("trigger_price"),
                    name="trigger_rules.trigger_price",
                    minimum=1,
                )
            )
        ),
        controls=AutoTraderUserControlRule(
            kill_switch_enabled=_require_bool(
                controls.get("kill_switch_enabled", True),
                name="controls.kill_switch_enabled",
            ),
            max_live_orders=_require_int(
                controls.get("max_live_orders", 3),
                name="controls.max_live_orders",
                minimum=1,
            ),
        ),
    )
    bundle_hash = doc.get("user_rule_bundle_hash")
    if bundle_hash is not None and bundle_hash != bundle.user_rule_bundle_hash_hex():
        raise ValueError("user rule bundle hash mismatch")
    return bundle



def load_autotrader_user_rule_bundle_file(path: str | Path) -> AutoTraderUserRuleBundle:
    obj = json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("autotrader user rule bundle file must be a JSON object")
    return autotrader_user_rule_bundle_from_dict(obj)


__all__ = [
    "AUTOTRADER_USER_RULE_BUNDLE_SCHEMA",
    "DEFAULT_AUTOTRADER_USER_RULE_BUNDLE_COMPILER_VERSION",
    "AutoTraderUserBudgetRule",
    "AutoTraderUserControlRule",
    "AutoTraderUserMarket",
    "AutoTraderUserRiskRule",
    "AutoTraderUserRuleBundle",
    "AutoTraderUserRuleMode",
    "AutoTraderUserRulePreset",
    "AutoTraderUserSizingRule",
    "AutoTraderUserTriggerRule",
    "AutoTraderUserWindowRule",
    "autotrader_user_rule_bundle_from_dict",
    "build_autotrader_client_policy_bundle_from_user_rule_bundle",
    "build_autotrader_client_policy_surface_from_user_rule_bundle",
    "build_autotrader_user_rule_bundle_from_mode",
    "build_autotrader_user_rule_bundle_from_preset",
    "build_autotrader_user_rule_source_artifact",
    "compare_autotrader_user_rule_presets",
    "compile_autotrader_user_rule_bundle",
    "recommend_autotrader_user_rule_preset",
    "describe_autotrader_strategy_surface_support",
    "describe_autotrader_user_rule_preset",
    "describe_autotrader_user_rule_surface_support",
    "list_autotrader_user_rule_presets",
    "load_autotrader_user_rule_bundle_file",
]
