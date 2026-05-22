from __future__ import annotations

from pathlib import Path

from src.agents.zenograph_microtheories import load_microtheory_specs, resolve_active_microtheories


def test_load_microtheory_specs_orders_by_priority_then_id() -> None:
    specs = load_microtheory_specs(Path("config/zenograph/microtheories_v1.yaml"))
    assert specs[0].microtheory_id == "OnChainFacts"
    assert specs[-1].microtheory_id == "TaxPolicy"


def test_resolve_active_microtheories_uses_activation_flags() -> None:
    specs = load_microtheory_specs(Path("config/zenograph/microtheories_v1.yaml"))
    active = resolve_active_microtheories(
        specs,
        {
            "strategy_templates_present": True,
            "user_policy_present": True,
            "execution_path_active": True,
            "external_signals_present": False,
            "taxable_account_present": False,
        },
    )
    assert active == (
        "OnChainFacts",
        "ExecutionMicrostructure",
        "UserPolicy",
        "StrategyLibrary",
    )
