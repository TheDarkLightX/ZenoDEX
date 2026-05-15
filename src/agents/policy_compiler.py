from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..kernels.python.strategy_compile_contract_v1_adapter import check_strategy_compile_contract
from .strategy_ir import (
    TEMPLATE_ALLOWED_ACTIONS,
    TEMPLATE_REQUIRED_PARAMS,
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyControls,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)


@dataclass(frozen=True)
class PolicyCompilationResult:
    strategy: StrategyIR
    explain: tuple[str, ...]


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    return value


def _coerce_backend(value: Any) -> PolicyBackend:
    if value is None:
        return PolicyBackend.LOCAL
    if not isinstance(value, str):
        raise TypeError("policy_backend must be a string")
    return PolicyBackend(value.strip().lower())


def _coerce_template(value: Any) -> StrategyTemplate:
    if not isinstance(value, str):
        raise TypeError("template must be a string")
    normalized = value.strip().lower().replace("-", "_").replace(" ", "_")
    aliases = {
        "limit": StrategyTemplate.LIMIT_LADDER,
        "limit_order": StrategyTemplate.LIMIT_LADDER,
        "stop": StrategyTemplate.STOP_LOSS,
        "stop_order": StrategyTemplate.STOP_LOSS,
        "take_profit_order": StrategyTemplate.TAKE_PROFIT,
    }
    if normalized in aliases:
        return aliases[normalized]
    return StrategyTemplate(normalized)


def _coerce_actions(value: Any, *, template: StrategyTemplate) -> tuple[StrategyAction, ...]:
    if value is None:
        return TEMPLATE_ALLOWED_ACTIONS[template]
    if not isinstance(value, list):
        raise ValueError("allowed_actions must be a list")
    actions: list[StrategyAction] = []
    seen: set[StrategyAction] = set()
    aliases = {
        "swap_exact_in": StrategyAction.PLACE_SWAP_EXACT_IN,
        "swap_exact_out": StrategyAction.PLACE_SWAP_EXACT_OUT,
        "order_intent": StrategyAction.PLACE_ORDER_INTENT,
    }
    for raw in value:
        if not isinstance(raw, str):
            raise TypeError("allowed_actions entries must be strings")
        normalized = raw.strip().lower().replace("-", "_").replace(" ", "_")
        action = aliases.get(normalized)
        if action is None:
            action = StrategyAction(normalized)
        if action in seen:
            continue
        seen.add(action)
        actions.append(action)
    if not actions:
        raise ValueError("allowed_actions must be non-empty")
    return tuple(actions)


def _coerce_template_params(value: Any) -> dict[str, str | int | bool]:
    if value is None:
        return {}
    if not isinstance(value, Mapping):
        raise ValueError("template_params must be an object")
    return dict(value)


def compile_policy_candidate(candidate: Mapping[str, Any], *, owner_pubkey: str | None = None) -> PolicyCompilationResult:
    if not isinstance(candidate, Mapping):
        raise TypeError("candidate must be a mapping")

    template = _coerce_template(candidate.get("template"))
    notional_caps_raw = _require_mapping(candidate.get("notional_caps", {}), name="notional_caps")
    risk_limits_raw = _require_mapping(candidate.get("risk_limits", {}), name="risk_limits")
    strategy_window_raw = _require_mapping(candidate.get("strategy_window", {}), name="strategy_window")
    controls_raw = _require_mapping(candidate.get("controls", {}), name="controls")
    template_params = _coerce_template_params(candidate.get("template_params"))

    missing_params = [key for key in TEMPLATE_REQUIRED_PARAMS[template] if key not in template_params]
    if missing_params:
        raise ValueError(f"template_params missing required keys for {template.value}: {', '.join(missing_params)}")

    asset_universe_raw = candidate.get("asset_universe")
    if not isinstance(asset_universe_raw, list):
        raise ValueError("asset_universe must be a list")

    strategy = StrategyIR(
        strategy_id=str(candidate.get("strategy_id") or candidate.get("id") or "").strip(),
        owner_pubkey=str(owner_pubkey or candidate.get("owner_pubkey") or "").strip(),
        policy_backend=_coerce_backend(candidate.get("policy_backend")),
        template=template,
        asset_universe=tuple(str(x) for x in asset_universe_raw),
        allowed_actions=_coerce_actions(candidate.get("allowed_actions"), template=template),
        notional_caps=NotionalCaps(
            per_order_max=int(notional_caps_raw.get("per_order_max", 0)),
            per_window_max=int(notional_caps_raw.get("per_window_max", 0)),
            lifetime_max=int(notional_caps_raw.get("lifetime_max", 0)),
        ),
        risk_limits=RiskLimits(
            max_slippage_bps=int(risk_limits_raw.get("max_slippage_bps", 0)),
            max_oracle_staleness_epochs=int(risk_limits_raw.get("max_oracle_staleness_epochs", 0)),
            require_quote_receipts=bool(risk_limits_raw.get("require_quote_receipts", True)),
        ),
        strategy_window=StrategyWindow(
            valid_from_epoch=int(strategy_window_raw.get("valid_from_epoch", 0)),
            valid_until_epoch=int(strategy_window_raw.get("valid_until_epoch", 0)),
            min_order_spacing_epochs=int(strategy_window_raw.get("min_order_spacing_epochs", 0)),
            budget_window_epochs=int(strategy_window_raw.get("budget_window_epochs", 0)),
        ),
        controls=StrategyControls(
            kill_switch_enabled=bool(controls_raw.get("kill_switch_enabled", True)),
            max_live_orders=int(controls_raw.get("max_live_orders", 1)),
            max_intents_per_order=int(controls_raw.get("max_intents_per_order", 16)),
        ),
        template_params=template_params,
        tau_policy_specs=tuple(candidate.get("tau_policy_specs", ()) or ()),
        tau_policy_spec=candidate.get("tau_policy_spec"),
    )
    contract = check_strategy_compile_contract(strategy)
    if not contract.ok:
        raise ValueError(f"strategy compile contract rejected: {contract.error}")

    explain = (
        f"template={strategy.template.value}",
        f"backend={strategy.policy_backend.value}",
        f"actions={','.join(action.value for action in strategy.allowed_actions)}",
        f"strategy_hash={strategy.strategy_hash_hex()}",
    )
    return PolicyCompilationResult(strategy=strategy, explain=explain)
