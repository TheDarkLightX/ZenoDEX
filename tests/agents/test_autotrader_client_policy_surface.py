from __future__ import annotations

import pytest

from src.agents.autotrader_client_policy_surface import (
    AUTOTRADER_CLIENT_POLICY_SURFACE_SCHEMA,
    autotrader_client_policy_surface_from_dict,
    build_autotrader_client_policy_surface,
)
from src.agents.policy_artifacts import (
    build_strategy_policy_artifact,
    build_strategy_source_artifact,
    build_tau_policy_bundle,
)
from src.agents.strategy_ir import (
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.agents.tau_policy_adapter import build_compile_contract_tau_policy_receipt



def _strategy() -> StrategyIR:
    return StrategyIR(
        strategy_id="client.surface.1",
        owner_pubkey="owner.pubkey.surface",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=75, max_oracle_staleness_epochs=3, require_quote_receipts=True),
        strategy_window=StrategyWindow(valid_from_epoch=10, valid_until_epoch=100, min_order_spacing_epochs=2),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
    )


def test_build_autotrader_client_policy_surface_splits_strategy_and_guards() -> None:
    strategy = _strategy()
    surface = build_autotrader_client_policy_surface(strategy=strategy)
    payload = surface.to_dict()

    assert payload["schema"] == AUTOTRADER_CLIENT_POLICY_SURFACE_SCHEMA
    assert payload["strategy_logic"]["template"] == "dca"
    assert payload["strategy_logic"]["allowed_actions"] == ["place_swap_exact_in"]
    assert payload["hard_local_guards"]["risk_limits"]["max_slippage_bps"] == 75
    assert payload["hard_local_guards"]["controls"]["kill_switch_enabled"] is True
    assert payload["posture"]["client_side_default"] is True
    assert payload["posture"]["quote_receipts_required"] is True
    assert payload["assurance_artifacts"]["source_form"] == "compiled_strategy_ir"
    assert payload["posture"]["assurance_bundle_present"] is False
    assert payload["posture"]["signed_policy_present"] is False


def test_build_autotrader_client_policy_surface_records_artifact_hashes() -> None:
    strategy = _strategy()
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    tau_policy_bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
        source_artifact=source_artifact,
    )
    policy_artifact = build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=tau_policy_bundle,
        source_artifact=source_artifact,
    )

    surface = build_autotrader_client_policy_surface(
        strategy=strategy,
        source_artifact=source_artifact,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )
    payload = surface.to_dict()

    assert payload["assurance_artifacts"]["source_form"] == "kv"
    assert payload["assurance_artifacts"]["source_preset_id"] is None
    assert payload["assurance_artifacts"]["source_artifact_hash"] == source_artifact.source_artifact_hash_hex()
    assert payload["assurance_artifacts"]["tau_policy_bundle_hash"] == tau_policy_bundle.tau_policy_bundle_hash_hex()
    assert payload["assurance_artifacts"]["policy_artifact_hash"] == policy_artifact.policy_artifact_hash_hex()
    assert payload["posture"]["assurance_bundle_present"] is True
    assert payload["posture"]["signed_policy_present"] is True

    roundtrip = autotrader_client_policy_surface_from_dict(payload)
    assert roundtrip.to_dict() == payload


def test_build_autotrader_client_policy_surface_records_user_rule_preset_id() -> None:
    strategy = _strategy()
    source_artifact = build_strategy_source_artifact(
        strategy=strategy,
        source_form="autotrader_user_rule_bundle",
    )

    surface = build_autotrader_client_policy_surface(
        strategy=strategy,
        source_artifact=source_artifact,
        source_preset_id="conservative_dca",
    )

    payload = surface.to_dict()
    assert payload["assurance_artifacts"]["source_form"] == "autotrader_user_rule_bundle"
    assert payload["assurance_artifacts"]["source_preset_id"] == "conservative_dca"

    roundtrip = autotrader_client_policy_surface_from_dict(payload)
    assert roundtrip.to_dict() == payload


def test_build_autotrader_client_policy_surface_rejects_mismatched_artifacts() -> None:
    strategy = _strategy()
    other_strategy = StrategyIR(
        strategy_id="client.surface.2",
        owner_pubkey="owner.pubkey.surface",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=75, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=10, valid_until_epoch=100),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
    )
    other_source = build_strategy_source_artifact(strategy=other_strategy, source_form="kv")

    with pytest.raises(ValueError, match="source artifact strategy hash mismatch"):
        build_autotrader_client_policy_surface(strategy=strategy, source_artifact=other_source)


def test_build_autotrader_client_policy_surface_rejects_preset_without_user_rule_source() -> None:
    with pytest.raises(ValueError, match="source_preset_id requires autotrader_user_rule_bundle source artifact"):
        build_autotrader_client_policy_surface(
            strategy=_strategy(),
            source_preset_id="conservative_dca",
        )
