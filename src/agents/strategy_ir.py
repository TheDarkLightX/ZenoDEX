from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Mapping

_SAFE_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.:-]{1,128}$")
_TEMPLATE_PARAM_KEY_RE = re.compile(r"^[a-z][a-z0-9_]{0,63}$")
_JSON_SCALAR_TYPES = (str, int, bool)


class PolicyBackend(Enum):
    LOCAL = "local"
    TAU = "tau"


class StrategyTemplate(Enum):
    DCA = "dca"
    LIMIT_LADDER = "limit_ladder"
    STOP_LOSS = "stop_loss"
    TAKE_PROFIT = "take_profit"


class StrategyAction(Enum):
    PLACE_SWAP_EXACT_IN = "place_swap_exact_in"
    PLACE_SWAP_EXACT_OUT = "place_swap_exact_out"
    PLACE_ORDER_INTENT = "place_order_intent"


TEMPLATE_ALLOWED_ACTIONS: dict[StrategyTemplate, tuple[StrategyAction, ...]] = {
    StrategyTemplate.DCA: (StrategyAction.PLACE_SWAP_EXACT_IN,),
    StrategyTemplate.LIMIT_LADDER: (StrategyAction.PLACE_ORDER_INTENT,),
    StrategyTemplate.STOP_LOSS: (StrategyAction.PLACE_ORDER_INTENT,),
    StrategyTemplate.TAKE_PROFIT: (StrategyAction.PLACE_ORDER_INTENT,),
}

TEMPLATE_REQUIRED_PARAMS: dict[StrategyTemplate, tuple[str, ...]] = {
    StrategyTemplate.DCA: ("fixed_order_size", "cadence_epochs", "asset_in", "asset_out"),
    StrategyTemplate.LIMIT_LADDER: ("ladder_levels", "per_level_size", "asset_in", "asset_out"),
    StrategyTemplate.STOP_LOSS: ("trigger_price", "fixed_order_size", "asset_in", "asset_out"),
    StrategyTemplate.TAKE_PROFIT: ("trigger_price", "fixed_order_size", "asset_in", "asset_out"),
}


AUTOTRADER_TAU_POLICY_SPECS: tuple[str, ...] = (
    "autotrader_signal_provenance_guard_v1",
    "autotrader_external_signal_source_registry_guard_v1",
    "autotrader_route_economic_sanity_guard_v1",
    "autotrader_oracle_freshness_guard_v1",
    "autotrader_execution_guard_v1",
    "autotrader_budget_guard_v1",
    "autotrader_session_state_guard_v1",
    "autotrader_session_capability_binding_guard_v1",
    "autotrader_wallet_capability_guard_v1",
    "autotrader_nonce_guard_v1",
)
_LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V1: tuple[str, ...] = (
    "autotrader_budget_guard_v1",
    "autotrader_execution_guard_v1",
    "autotrader_oracle_freshness_guard_v1",
)
_LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V2: tuple[str, ...] = (
    "autotrader_signal_provenance_guard_v1",
    "autotrader_oracle_freshness_guard_v1",
    "autotrader_execution_guard_v1",
    "autotrader_budget_guard_v1",
    "autotrader_session_state_guard_v1",
    "autotrader_session_capability_binding_guard_v1",
    "autotrader_wallet_capability_guard_v1",
    "autotrader_nonce_guard_v1",
)
_LEGACY_TAU_POLICY_SPEC_MAP: dict[str, tuple[str, ...]] = {
    "autotrader_budget_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_execution_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_external_signal_source_registry_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_oracle_freshness_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_route_economic_sanity_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_session_state_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_signal_provenance_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_wallet_capability_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
    "autotrader_nonce_guard_v1": AUTOTRADER_TAU_POLICY_SPECS,
}
_LEGACY_TAU_POLICY_BUNDLE_MAP: dict[tuple[str, ...], tuple[str, ...]] = {
    _LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V1: AUTOTRADER_TAU_POLICY_SPECS,
    _LEGACY_AUTOTRADER_TAU_POLICY_SPECS_V2: AUTOTRADER_TAU_POLICY_SPECS,
}


def _require_safe_token(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        if allow_empty:
            return ""
        raise ValueError(f"{name} must be non-empty")
    if not _SAFE_TOKEN_RE.fullmatch(text):
        raise ValueError(f"{name} contains unsupported characters: {value!r}")
    return text


def _require_int(value: object, *, name: str, minimum: int | None = None, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if minimum is not None and out < minimum:
        raise ValueError(f"{name} must be >= {minimum}: {out}")
    if maximum is not None and out > maximum:
        raise ValueError(f"{name} must be <= {maximum}: {out}")
    return out


def _normalize_scalar(value: object, *, name: str) -> str | int | bool:
    if isinstance(value, bool):
        return bool(value)
    if isinstance(value, int):
        return int(value)
    if isinstance(value, str):
        return _require_safe_token(value, name=name)
    raise TypeError(f"{name} must be a string, int, or bool")


def _normalize_string_tuple(
    values: tuple[str, ...] | list[str] | tuple[StrategyAction, ...] | list[StrategyAction],
    *,
    name: str,
) -> tuple[str, ...]:
    out: list[str] = []
    seen: set[str] = set()
    for idx, raw in enumerate(values):
        if isinstance(raw, StrategyAction):
            value = raw.value
        else:
            value = _require_safe_token(raw, name=f"{name}[{idx}]")
        if value in seen:
            continue
        seen.add(value)
        out.append(value)
    if not out:
        raise ValueError(f"{name} must be non-empty")
    return tuple(out)


def _normalize_tau_policy_specs(
    values: tuple[str, ...] | list[str],
    *,
    name: str,
) -> tuple[str, ...]:
    normalized = _normalize_string_tuple(values, name=name)
    legacy_bundle = _LEGACY_TAU_POLICY_BUNDLE_MAP.get(normalized)
    if legacy_bundle is not None:
        return legacy_bundle
    if normalized != AUTOTRADER_TAU_POLICY_SPECS:
        expected = ", ".join(AUTOTRADER_TAU_POLICY_SPECS)
        got = ", ".join(normalized)
        raise ValueError(f"{name} must equal the supported autotrader bundle: {expected}; got {got}")
    return normalized


def _resolve_tau_policy_specs(
    *,
    policy_backend: PolicyBackend,
    tau_policy_specs: tuple[str, ...] | list[str],
    tau_policy_spec: str | None,
) -> tuple[str, ...]:
    if tau_policy_spec is not None:
        tau_policy_spec = _require_safe_token(tau_policy_spec, name="tau_policy_spec")
    if tau_policy_specs:
        resolved = _normalize_tau_policy_specs(tau_policy_specs, name="tau_policy_specs")
    elif tau_policy_spec is not None:
        resolved = _LEGACY_TAU_POLICY_SPEC_MAP.get(tau_policy_spec, ())
        if not resolved:
            raise ValueError(
                "tau_policy_spec is unsupported; expected a canonical tau_policy_specs bundle"
            )
    else:
        resolved = ()
    if policy_backend is PolicyBackend.TAU and not resolved:
        raise ValueError("tau_policy_specs is required when policy_backend=tau")
    if policy_backend is PolicyBackend.LOCAL and resolved:
        raise ValueError("tau_policy_specs is only allowed when policy_backend=tau")
    return tuple(resolved)


@dataclass(frozen=True)
class NotionalCaps:
    per_order_max: int
    per_window_max: int
    lifetime_max: int

    def __post_init__(self) -> None:
        per_order_max = _require_int(self.per_order_max, name="per_order_max", minimum=1, maximum=0xFFFFFFFF)
        per_window_max = _require_int(self.per_window_max, name="per_window_max", minimum=1, maximum=0xFFFFFFFF)
        lifetime_max = _require_int(self.lifetime_max, name="lifetime_max", minimum=1, maximum=0xFFFFFFFF)
        if per_order_max > per_window_max:
            raise ValueError("per_order_max must be <= per_window_max")
        if per_window_max > lifetime_max:
            raise ValueError("per_window_max must be <= lifetime_max")
        object.__setattr__(self, "per_order_max", per_order_max)
        object.__setattr__(self, "per_window_max", per_window_max)
        object.__setattr__(self, "lifetime_max", lifetime_max)

    def to_dict(self) -> dict[str, int]:
        return {
            "per_order_max": int(self.per_order_max),
            "per_window_max": int(self.per_window_max),
            "lifetime_max": int(self.lifetime_max),
        }


@dataclass(frozen=True)
class RiskLimits:
    max_slippage_bps: int
    max_oracle_staleness_epochs: int
    require_quote_receipts: bool = True

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "max_slippage_bps",
            _require_int(self.max_slippage_bps, name="max_slippage_bps", minimum=0, maximum=10_000),
        )
        object.__setattr__(
            self,
            "max_oracle_staleness_epochs",
            _require_int(
                self.max_oracle_staleness_epochs,
                name="max_oracle_staleness_epochs",
                minimum=1,
                maximum=1_000_000,
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
class StrategyWindow:
    valid_from_epoch: int
    valid_until_epoch: int
    min_order_spacing_epochs: int = 0
    budget_window_epochs: int = 0

    def __post_init__(self) -> None:
        valid_from_epoch = _require_int(self.valid_from_epoch, name="valid_from_epoch", minimum=0, maximum=1_000_000)
        valid_until_epoch = _require_int(self.valid_until_epoch, name="valid_until_epoch", minimum=0, maximum=1_000_000)
        min_order_spacing_epochs = _require_int(
            self.min_order_spacing_epochs,
            name="min_order_spacing_epochs",
            minimum=0,
            maximum=1_000_000,
        )
        budget_window_epochs = _require_int(
            self.budget_window_epochs,
            name="budget_window_epochs",
            minimum=0,
            maximum=1_000_000,
        )
        if valid_from_epoch > valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        object.__setattr__(self, "valid_from_epoch", valid_from_epoch)
        object.__setattr__(self, "valid_until_epoch", valid_until_epoch)
        object.__setattr__(self, "min_order_spacing_epochs", min_order_spacing_epochs)
        object.__setattr__(self, "budget_window_epochs", budget_window_epochs)

    def to_dict(self) -> dict[str, int]:
        return {
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
            "min_order_spacing_epochs": int(self.min_order_spacing_epochs),
            "budget_window_epochs": int(self.budget_window_epochs),
        }


@dataclass(frozen=True)
class StrategyControls:
    kill_switch_enabled: bool = True
    max_live_orders: int = 1
    max_intents_per_order: int = 16

    def __post_init__(self) -> None:
        if not isinstance(self.kill_switch_enabled, bool):
            raise TypeError("kill_switch_enabled must be a bool")
        object.__setattr__(
            self,
            "max_live_orders",
            _require_int(self.max_live_orders, name="max_live_orders", minimum=1, maximum=1_024),
        )
        object.__setattr__(
            self,
            "max_intents_per_order",
            _require_int(
                self.max_intents_per_order,
                name="max_intents_per_order",
                minimum=1,
                maximum=1_024,
            ),
        )

    def to_dict(self) -> dict[str, int | bool]:
        return {
            "kill_switch_enabled": bool(self.kill_switch_enabled),
            "max_live_orders": int(self.max_live_orders),
            "max_intents_per_order": int(self.max_intents_per_order),
        }


def strategy_budget_window_duration_epochs(strategy_window: StrategyWindow) -> int:
    if not isinstance(strategy_window, StrategyWindow):
        raise TypeError("strategy_window must be a StrategyWindow")
    if strategy_window.budget_window_epochs > 0:
        return int(strategy_window.budget_window_epochs)
    return int(strategy_window.valid_until_epoch - strategy_window.valid_from_epoch + 1)


def strategy_budget_window_id(strategy_window: StrategyWindow, current_epoch: int) -> int:
    if not isinstance(strategy_window, StrategyWindow):
        raise TypeError("strategy_window must be a StrategyWindow")
    current_epoch = _require_int(
        current_epoch,
        name="current_epoch",
        minimum=0,
        maximum=1_000_000,
    )
    duration = strategy_budget_window_duration_epochs(strategy_window)
    if current_epoch <= strategy_window.valid_from_epoch:
        return int(strategy_window.valid_from_epoch)
    offset = current_epoch - strategy_window.valid_from_epoch
    return int(strategy_window.valid_from_epoch + (offset // duration) * duration)


@dataclass(frozen=True)
class StrategyIR:
    strategy_id: str
    owner_pubkey: str
    policy_backend: PolicyBackend
    template: StrategyTemplate
    asset_universe: tuple[str, ...]
    allowed_actions: tuple[StrategyAction, ...]
    notional_caps: NotionalCaps
    risk_limits: RiskLimits
    strategy_window: StrategyWindow
    controls: StrategyControls = field(default_factory=StrategyControls)
    template_params: Mapping[str, str | int | bool] = field(default_factory=dict)
    tau_policy_specs: tuple[str, ...] = field(default_factory=tuple)
    tau_policy_spec: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "strategy_id", _require_safe_token(self.strategy_id, name="strategy_id"))
        object.__setattr__(self, "owner_pubkey", _require_safe_token(self.owner_pubkey, name="owner_pubkey"))

        if not isinstance(self.policy_backend, PolicyBackend):
            raise TypeError("policy_backend must be a PolicyBackend")
        if not isinstance(self.template, StrategyTemplate):
            raise TypeError("template must be a StrategyTemplate")
        if not isinstance(self.notional_caps, NotionalCaps):
            raise TypeError("notional_caps must be a NotionalCaps")
        if not isinstance(self.risk_limits, RiskLimits):
            raise TypeError("risk_limits must be a RiskLimits")
        if not isinstance(self.strategy_window, StrategyWindow):
            raise TypeError("strategy_window must be a StrategyWindow")
        if not isinstance(self.controls, StrategyControls):
            raise TypeError("controls must be a StrategyControls")

        asset_universe = _normalize_string_tuple(self.asset_universe, name="asset_universe")
        if len(asset_universe) < 2:
            raise ValueError("asset_universe must contain at least two assets")
        object.__setattr__(self, "asset_universe", asset_universe)

        allowed_actions_raw = _normalize_string_tuple(self.allowed_actions, name="allowed_actions")
        allowed_actions = tuple(StrategyAction(value) for value in allowed_actions_raw)
        object.__setattr__(self, "allowed_actions", allowed_actions)

        normalized_template_params: dict[str, str | int | bool] = {}
        for key, value in dict(self.template_params).items():
            if not isinstance(key, str) or not _TEMPLATE_PARAM_KEY_RE.fullmatch(key):
                raise ValueError(f"invalid template_params key: {key!r}")
            normalized_template_params[key] = _normalize_scalar(value, name=f"template_params.{key}")
        object.__setattr__(self, "template_params", normalized_template_params)

        tau_policy_specs = _resolve_tau_policy_specs(
            policy_backend=self.policy_backend,
            tau_policy_specs=tuple(self.tau_policy_specs),
            tau_policy_spec=self.tau_policy_spec,
        )
        object.__setattr__(self, "tau_policy_specs", tau_policy_specs)
        object.__setattr__(self, "tau_policy_spec", None)

    def to_dict(self) -> dict[str, Any]:
        return {
            "strategy_id": self.strategy_id,
            "owner_pubkey": self.owner_pubkey,
            "policy_backend": self.policy_backend.value,
            "template": self.template.value,
            "asset_universe": list(self.asset_universe),
            "allowed_actions": [action.value for action in self.allowed_actions],
            "notional_caps": self.notional_caps.to_dict(),
            "risk_limits": self.risk_limits.to_dict(),
            "strategy_window": self.strategy_window.to_dict(),
            "controls": self.controls.to_dict(),
            "template_params": dict(self.template_params),
            "tau_policy_specs": list(self.tau_policy_specs),
        }

    def to_json_bytes(self) -> bytes:
        return json.dumps(
            self.to_dict(),
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")

    def strategy_hash_hex(self) -> str:
        return "0x" + hashlib.sha256(self.to_json_bytes()).hexdigest()


def strategy_ir_from_dict(data: Mapping[str, Any]) -> StrategyIR:
    if not isinstance(data, Mapping):
        raise TypeError("strategy policy data must be a mapping")

    def _enum_member(enum_type: type[Enum], value: object, *, name: str) -> Enum:
        if not isinstance(value, str):
            raise TypeError(f"{name} must be a string")
        try:
            return enum_type(value)
        except ValueError as exc:
            allowed = ", ".join(member.value for member in enum_type)
            raise ValueError(f"{name} must be one of: {allowed}") from exc

    def _policy_backend_member(value: object) -> PolicyBackend:
        return PolicyBackend(_enum_member(PolicyBackend, value, name="policy_backend").value)

    def _template_member(value: object) -> StrategyTemplate:
        return StrategyTemplate(_enum_member(StrategyTemplate, value, name="template").value)

    def _action_member(value: object) -> StrategyAction:
        return StrategyAction(_enum_member(StrategyAction, value, name="allowed_actions").value)

    notional_caps_raw = data.get("notional_caps")
    risk_limits_raw = data.get("risk_limits")
    strategy_window_raw = data.get("strategy_window")
    controls_raw = data.get("controls", {})
    asset_universe_raw = data.get("asset_universe", ())
    allowed_actions_raw = data.get("allowed_actions", ())
    if not isinstance(notional_caps_raw, Mapping):
        raise ValueError("notional_caps must be an object")
    if not isinstance(risk_limits_raw, Mapping):
        raise ValueError("risk_limits must be an object")
    if not isinstance(strategy_window_raw, Mapping):
        raise ValueError("strategy_window must be an object")
    if not isinstance(controls_raw, Mapping):
        raise ValueError("controls must be an object")
    if not isinstance(asset_universe_raw, (list, tuple)):
        raise ValueError("asset_universe must be a list")
    if not isinstance(allowed_actions_raw, (list, tuple)):
        raise ValueError("allowed_actions must be a list")

    return StrategyIR(
        strategy_id=data.get("strategy_id", ""),
        owner_pubkey=data.get("owner_pubkey", ""),
        policy_backend=_policy_backend_member(data.get("policy_backend", "local")),
        template=_template_member(data.get("template", "")),
        asset_universe=tuple(asset_universe_raw),
        allowed_actions=tuple(_action_member(value) for value in allowed_actions_raw),
        notional_caps=NotionalCaps(
            per_order_max=_require_int(notional_caps_raw.get("per_order_max"), name="notional_caps.per_order_max"),
            per_window_max=_require_int(
                notional_caps_raw.get("per_window_max"),
                name="notional_caps.per_window_max",
            ),
            lifetime_max=_require_int(notional_caps_raw.get("lifetime_max"), name="notional_caps.lifetime_max"),
        ),
        risk_limits=RiskLimits(
            max_slippage_bps=_require_int(risk_limits_raw.get("max_slippage_bps"), name="risk_limits.max_slippage_bps"),
            max_oracle_staleness_epochs=_require_int(
                risk_limits_raw.get("max_oracle_staleness_epochs"),
                name="risk_limits.max_oracle_staleness_epochs",
            ),
            require_quote_receipts=bool(risk_limits_raw.get("require_quote_receipts", True)),
        ),
        strategy_window=StrategyWindow(
            valid_from_epoch=_require_int(
                strategy_window_raw.get("valid_from_epoch"),
                name="strategy_window.valid_from_epoch",
            ),
            valid_until_epoch=_require_int(
                strategy_window_raw.get("valid_until_epoch"),
                name="strategy_window.valid_until_epoch",
            ),
            min_order_spacing_epochs=_require_int(
                strategy_window_raw.get("min_order_spacing_epochs", 0),
                name="strategy_window.min_order_spacing_epochs",
            ),
            budget_window_epochs=_require_int(
                strategy_window_raw.get("budget_window_epochs", 0),
                name="strategy_window.budget_window_epochs",
            ),
        ),
        controls=StrategyControls(
            kill_switch_enabled=bool(controls_raw.get("kill_switch_enabled", True)),
            max_live_orders=_require_int(controls_raw.get("max_live_orders", 1), name="controls.max_live_orders"),
            max_intents_per_order=_require_int(
                controls_raw.get("max_intents_per_order", 16),
                name="controls.max_intents_per_order",
            ),
        ),
        template_params=dict(data.get("template_params", {})),
        tau_policy_specs=tuple(data.get("tau_policy_specs", ()) or ()),
        tau_policy_spec=data.get("tau_policy_spec"),
    )
