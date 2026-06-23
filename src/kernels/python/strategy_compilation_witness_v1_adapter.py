from __future__ import annotations

from dataclasses import dataclass

from ...agents.policy_artifacts import StrategySourceArtifact
from ...agents.strategy_ir import StrategyIR


@dataclass(frozen=True)
class StrategyCompilationWitnessResult:
    ok: bool
    source_form_ok: bool
    strategy_hash_match: bool
    owner_match: bool
    backend_match: bool
    template_match: bool
    asset_universe_match: bool
    allowed_actions_match: bool
    notional_caps_match: bool
    risk_limits_match: bool
    strategy_window_match: bool
    controls_match: bool
    template_params_match: bool
    tau_policy_specs_match: bool
    compile_contract_ok: bool
    error: str | None = None


def check_strategy_compilation_witness(
    *,
    source_artifact: StrategySourceArtifact,
    strategy: StrategyIR,
    compile_contract_ok: bool,
) -> StrategyCompilationWitnessResult:
    if not isinstance(source_artifact, StrategySourceArtifact):
        raise TypeError("source_artifact must be a StrategySourceArtifact")
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(compile_contract_ok, bool):
        raise TypeError("compile_contract_ok must be a bool")

    source_form_ok = bool(source_artifact.source_form)
    source_strategy = source_artifact.strategy
    strategy_hash_match = source_strategy.strategy_hash_hex() == strategy.strategy_hash_hex()
    owner_match = source_strategy.owner_pubkey == strategy.owner_pubkey
    backend_match = source_strategy.policy_backend is strategy.policy_backend
    template_match = source_strategy.template is strategy.template
    asset_universe_match = tuple(source_strategy.asset_universe) == tuple(strategy.asset_universe)
    allowed_actions_match = tuple(source_strategy.allowed_actions) == tuple(strategy.allowed_actions)
    notional_caps_match = source_strategy.notional_caps == strategy.notional_caps
    risk_limits_match = source_strategy.risk_limits == strategy.risk_limits
    strategy_window_match = source_strategy.strategy_window == strategy.strategy_window
    controls_match = source_strategy.controls == strategy.controls
    template_params_match = dict(source_strategy.template_params) == dict(strategy.template_params)
    tau_policy_specs_match = tuple(source_strategy.tau_policy_specs) == tuple(strategy.tau_policy_specs)

    ok = all(
        (
            source_form_ok,
            strategy_hash_match,
            owner_match,
            backend_match,
            template_match,
            asset_universe_match,
            allowed_actions_match,
            notional_caps_match,
            risk_limits_match,
            strategy_window_match,
            controls_match,
            template_params_match,
            tau_policy_specs_match,
            compile_contract_ok,
        )
    )
    checks = (
        ("source_form_invalid", source_form_ok),
        ("strategy_hash_mismatch", strategy_hash_match),
        ("owner_mismatch", owner_match),
        ("backend_mismatch", backend_match),
        ("template_mismatch", template_match),
        ("asset_universe_mismatch", asset_universe_match),
        ("allowed_actions_mismatch", allowed_actions_match),
        ("notional_caps_mismatch", notional_caps_match),
        ("risk_limits_mismatch", risk_limits_match),
        ("strategy_window_mismatch", strategy_window_match),
        ("controls_mismatch", controls_match),
        ("template_params_mismatch", template_params_match),
        ("tau_policy_specs_mismatch", tau_policy_specs_match),
        ("compile_contract_invalid", compile_contract_ok),
    )
    error = next((name for name, passed in checks if not passed), None)
    return StrategyCompilationWitnessResult(
        ok=ok,
        source_form_ok=source_form_ok,
        strategy_hash_match=strategy_hash_match,
        owner_match=owner_match,
        backend_match=backend_match,
        template_match=template_match,
        asset_universe_match=asset_universe_match,
        allowed_actions_match=allowed_actions_match,
        notional_caps_match=notional_caps_match,
        risk_limits_match=risk_limits_match,
        strategy_window_match=strategy_window_match,
        controls_match=controls_match,
        template_params_match=template_params_match,
        tau_policy_specs_match=tau_policy_specs_match,
        compile_contract_ok=compile_contract_ok,
        error=error,
    )
