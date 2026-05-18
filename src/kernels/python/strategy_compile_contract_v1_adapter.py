from __future__ import annotations

from dataclasses import dataclass

from ...agents.strategy_ir import (
    AUTOTRADER_TAU_POLICY_SPECS,
    TEMPLATE_ALLOWED_ACTIONS,
    TEMPLATE_REQUIRED_PARAMS,
    PolicyBackend,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
)


def strategy_template_code(value: StrategyTemplate) -> int:
    if not isinstance(value, StrategyTemplate):
        raise TypeError("value must be a StrategyTemplate")
    mapping = {
        StrategyTemplate.DCA: 1,
        StrategyTemplate.LIMIT_LADDER: 2,
        StrategyTemplate.STOP_LOSS: 3,
        StrategyTemplate.TAKE_PROFIT: 4,
    }
    return mapping[value]


def policy_backend_code(value: PolicyBackend) -> int:
    if not isinstance(value, PolicyBackend):
        raise TypeError("value must be a PolicyBackend")
    return 1 if value is PolicyBackend.TAU else 0


@dataclass(frozen=True)
class StrategyCompileContractResult:
    ok: bool
    backend_ok: bool
    template_ok: bool
    strategy_id_ok: bool
    owner_binding_ok: bool
    asset_scope_ok: bool
    required_params_ok: bool
    action_scope_ok: bool
    notional_chain_ok: bool
    slippage_ok: bool
    oracle_window_ok: bool
    strategy_window_ok: bool
    controls_ok: bool
    tau_bundle_ok: bool
    error: str | None = None


def _resolve_compile_error(result: StrategyCompileContractResult) -> str | None:
    checks = (
        ("backend_unsupported", result.backend_ok),
        ("template_unsupported", result.template_ok),
        ("strategy_id_missing", result.strategy_id_ok),
        ("owner_pubkey_missing", result.owner_binding_ok),
        ("asset_scope_invalid", result.asset_scope_ok),
        ("required_template_params_missing", result.required_params_ok),
        ("allowed_actions_invalid", result.action_scope_ok),
        ("notional_caps_invalid", result.notional_chain_ok),
        ("slippage_limit_invalid", result.slippage_ok),
        ("oracle_window_invalid", result.oracle_window_ok),
        ("strategy_window_invalid", result.strategy_window_ok),
        ("controls_invalid", result.controls_ok),
        ("tau_policy_bundle_invalid", result.tau_bundle_ok),
    )
    for error, ok in checks:
        if not ok:
            return error
    return None


def check_strategy_compile_contract(strategy: StrategyIR) -> StrategyCompileContractResult:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")

    backend_ok = policy_backend_code(strategy.policy_backend) in (0, 1)
    template_ok = strategy_template_code(strategy.template) in (1, 2, 3, 4)
    strategy_id_ok = bool(strategy.strategy_id)
    owner_binding_ok = bool(strategy.owner_pubkey)
    asset_in = str(strategy.template_params.get("asset_in", "")).strip()
    asset_out = str(strategy.template_params.get("asset_out", "")).strip()
    asset_scope_ok = (
        len(strategy.asset_universe) >= 2
        and bool(asset_in)
        and bool(asset_out)
        and asset_in in strategy.asset_universe
        and asset_out in strategy.asset_universe
        and asset_in != asset_out
    )
    required_params_ok = all(
        key in strategy.template_params for key in TEMPLATE_REQUIRED_PARAMS[strategy.template]
    )
    required_actions = tuple(TEMPLATE_ALLOWED_ACTIONS[strategy.template])
    action_scope_ok = (
        bool(strategy.allowed_actions)
        and all(isinstance(action, StrategyAction) for action in strategy.allowed_actions)
        and all(action in strategy.allowed_actions for action in required_actions)
    )
    notional_chain_ok = (
        strategy.notional_caps.per_order_max <= strategy.notional_caps.per_window_max
        and strategy.notional_caps.per_window_max <= strategy.notional_caps.lifetime_max
    )
    slippage_ok = 0 <= strategy.risk_limits.max_slippage_bps <= 10_000
    oracle_window_ok = strategy.risk_limits.max_oracle_staleness_epochs >= 1
    strategy_window_ok = (
        strategy.strategy_window.valid_from_epoch <= strategy.strategy_window.valid_until_epoch
        and strategy.strategy_window.min_order_spacing_epochs >= 0
        and strategy.strategy_window.budget_window_epochs >= 0
    )
    controls_ok = (
        strategy.controls.max_live_orders >= 1
        and strategy.controls.max_intents_per_order >= 1
    )
    tau_bundle_ok = (
        strategy.policy_backend is PolicyBackend.LOCAL
        or strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS
    )
    ok = all(
        (
            backend_ok,
            template_ok,
            strategy_id_ok,
            owner_binding_ok,
            asset_scope_ok,
            required_params_ok,
            action_scope_ok,
            notional_chain_ok,
            slippage_ok,
            oracle_window_ok,
            strategy_window_ok,
            controls_ok,
            tau_bundle_ok,
        )
    )
    result = StrategyCompileContractResult(
        ok=ok,
        backend_ok=backend_ok,
        template_ok=template_ok,
        strategy_id_ok=strategy_id_ok,
        owner_binding_ok=owner_binding_ok,
        asset_scope_ok=asset_scope_ok,
        required_params_ok=required_params_ok,
        action_scope_ok=action_scope_ok,
        notional_chain_ok=notional_chain_ok,
        slippage_ok=slippage_ok,
        oracle_window_ok=oracle_window_ok,
        strategy_window_ok=strategy_window_ok,
        controls_ok=controls_ok,
        tau_bundle_ok=tau_bundle_ok,
    )
    error = _resolve_compile_error(result)
    return StrategyCompileContractResult(
        ok=result.ok,
        backend_ok=result.backend_ok,
        template_ok=result.template_ok,
        strategy_id_ok=result.strategy_id_ok,
        owner_binding_ok=result.owner_binding_ok,
        asset_scope_ok=result.asset_scope_ok,
        required_params_ok=result.required_params_ok,
        action_scope_ok=result.action_scope_ok,
        notional_chain_ok=result.notional_chain_ok,
        slippage_ok=result.slippage_ok,
        oracle_window_ok=result.oracle_window_ok,
        strategy_window_ok=result.strategy_window_ok,
        controls_ok=result.controls_ok,
        tau_bundle_ok=result.tau_bundle_ok,
        error=error,
    )
