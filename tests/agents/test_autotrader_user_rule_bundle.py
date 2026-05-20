from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.agents.autotrader_client_policy_bundle import (
    load_autotrader_client_policy_bundle_file,
    sign_autotrader_client_policy_bundle,
    verify_autotrader_client_policy_bundle_signature,
)
from src.agents.autotrader_local_guard_evaluator import AutoTraderLocalGuardInputs
from src.agents.autotrader_user_rule_bundle import (
    AUTOTRADER_USER_RULE_BUNDLE_SCHEMA,
    AutoTraderUserBudgetRule,
    AutoTraderUserControlRule,
    AutoTraderUserMarket,
    AutoTraderUserRiskRule,
    AutoTraderUserRuleBundle,
    AutoTraderUserRuleMode,
    AutoTraderUserRulePreset,
    AutoTraderUserSizingRule,
    AutoTraderUserTriggerRule,
    AutoTraderUserWindowRule,
    autotrader_user_rule_bundle_from_dict,
    build_autotrader_client_policy_bundle_from_user_rule_bundle,
    build_autotrader_client_policy_surface_from_user_rule_bundle,
    compare_autotrader_user_rule_presets,
    build_autotrader_user_rule_bundle_from_mode,
    build_autotrader_user_rule_bundle_from_preset,
    build_autotrader_user_rule_source_artifact,
    compile_autotrader_user_rule_bundle,
    describe_autotrader_user_rule_preset,
    list_autotrader_user_rule_presets,
    recommend_autotrader_user_rule_preset,
    load_autotrader_user_rule_bundle_file,
)
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS, PolicyBackend, StrategyAction, StrategyTemplate
from src.integration.autotrader_signals import QuoteReceiptSignalPacket, SignalSourceKind, SignalTrustTier
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey


def _owner_pubkey(privkey: int = 21) -> str:
    return "0x" + bls_pubkey_hex_from_privkey(privkey)



def _packet(**overrides: object) -> QuoteReceiptSignalPacket:
    data = {
        "current_epoch": 12,
        "quote_epoch": 12,
        "asset_in": "zUSD",
        "asset_out": "BTC",
        "amount_in": 100,
        "amount_out": 181,
        "receipt_hash": "receipt.hash.user.bundle.1",
        "source_id": "route_quote_receipt",
        "source_kind": SignalSourceKind.ROUTE_QUOTE_RECEIPT,
        "trust_tier": SignalTrustTier.VERIFIED,
        "quote_receipt_present": True,
        "quote_receipt_verified": True,
        "quote_epoch_present": True,
        "source_available": True,
        "auth_ok": True,
        "binding_ok": True,
    }
    data.update(overrides)
    return QuoteReceiptSignalPacket(**data)



def _bundle(*, owner_privkey: int = 21, policy_backend: PolicyBackend = PolicyBackend.TAU) -> AutoTraderUserRuleBundle:
    return AutoTraderUserRuleBundle(
        bundle_name="user.rules.bundle.1",
        built_at="2026-04-09T18:00:00Z",
        compiler_version="autotrader-user-rule-bundle/v1",
        strategy_id="user.rule.strategy.1",
        owner_pubkey=_owner_pubkey(owner_privkey),
        policy_backend=policy_backend,
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        sizing=AutoTraderUserSizingRule(fixed_order_size=100, cadence_epochs=4),
        budget=AutoTraderUserBudgetRule(per_window_max=500, lifetime_max=1000),
        risk=AutoTraderUserRiskRule(max_slippage_bps=75, max_oracle_staleness_epochs=3),
        window=AutoTraderUserWindowRule(valid_from_epoch=10, valid_until_epoch=100, min_order_spacing_epochs=2),
        controls=AutoTraderUserControlRule(kill_switch_enabled=True, max_live_orders=3),
    )



def test_autotrader_user_rule_bundle_roundtrips_and_hashes(tmp_path: Path) -> None:
    bundle = _bundle()
    payload = bundle.to_dict()
    assert payload["schema"] == AUTOTRADER_USER_RULE_BUNDLE_SCHEMA

    roundtrip = autotrader_user_rule_bundle_from_dict(payload)
    assert roundtrip.to_dict() == payload

    path = tmp_path / "user_rule_bundle.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    loaded = load_autotrader_user_rule_bundle_file(path)
    assert loaded.to_dict() == payload


def test_recommend_autotrader_user_rule_preset_prefers_matching_constraints() -> None:
    recommendation = recommend_autotrader_user_rule_preset(
        desired_optimize_for="price_discipline",
        desired_max_slippage_bps=20,
        desired_max_oracle_staleness_epochs=3,
        desired_max_live_orders=2,
    )

    assert recommendation["recommended_preset"]["preset_id"] == "price_discipline_dca"
    assert recommendation["ranked_candidates"][0]["total_penalty"] == 0


def test_recommend_autotrader_user_rule_preset_can_select_trigger_mode() -> None:
    recommendation = recommend_autotrader_user_rule_preset(
        desired_user_rule_mode="stop_loss_order_intent",
        desired_optimize_for="downside_protection",
        desired_max_slippage_bps=25,
        desired_max_oracle_staleness_epochs=1,
        desired_max_live_orders=1,
    )

    assert recommendation["recommended_preset"]["preset_id"] == "protective_stop_loss"
    assert recommendation["recommended_preset"]["mode"] == "stop_loss_order_intent"
    assert recommendation["ranked_candidates"][0]["penalty_breakdown"]["user_rule_mode_penalty"] == 0


def test_recommend_autotrader_user_rule_preset_can_require_live_supported() -> None:
    recommendation = recommend_autotrader_user_rule_preset(
        desired_optimize_for="throughput",
        require_live_supported=True,
    )

    assert recommendation["recommended_preset"]["preset_id"] == "high_throughput_dca"
    assert recommendation["criteria"]["require_live_supported"] is True


def test_recommend_autotrader_user_rule_preset_rejects_unsatisfied_live_support_constraint() -> None:
    with pytest.raises(ValueError, match="no presets satisfy"):
        recommend_autotrader_user_rule_preset(
            desired_user_rule_mode="stop_loss_order_intent",
            require_live_supported=True,
        )


def test_compare_autotrader_user_rule_presets_reports_guard_deltas() -> None:
    comparison = compare_autotrader_user_rule_presets(
        AutoTraderUserRulePreset.CAPITAL_PRESERVATION_DCA,
        AutoTraderUserRulePreset.HIGH_THROUGHPUT_DCA,
    )

    assert comparison["left"]["preset_id"] == "capital_preservation_dca"
    assert comparison["right"]["preset_id"] == "high_throughput_dca"
    assert comparison["guard_profile_deltas"]["max_slippage_bps"] == {"left": 20, "right": 150}
    assert comparison["operating_profile_deltas"]["concurrency_posture"] == {"left": "minimal", "right": "high"}



def test_list_autotrader_user_rule_presets_returns_expected_order() -> None:
    presets = list_autotrader_user_rule_presets()
    preset_ids = [preset["preset_id"] for preset in presets]

    assert preset_ids == [
        "capital_preservation_dca",
        "conservative_dca",
        "balanced_dca",
        "price_discipline_dca",
        "high_throughput_dca",
        "protective_stop_loss",
        "disciplined_take_profit",
    ]


def test_list_autotrader_user_rule_presets_supports_live_filters() -> None:
    live_supported = list_autotrader_user_rule_presets(live_supported_only=True)
    fail_closed = list_autotrader_user_rule_presets(fail_closed_only=True)

    assert [preset["preset_id"] for preset in live_supported] == [
        "capital_preservation_dca",
        "conservative_dca",
        "balanced_dca",
        "price_discipline_dca",
        "high_throughput_dca",
    ]
    assert [preset["preset_id"] for preset in fail_closed] == [
        "protective_stop_loss",
        "disciplined_take_profit",
    ]



def test_describe_autotrader_user_rule_preset_supports_new_presets() -> None:
    capital = describe_autotrader_user_rule_preset(AutoTraderUserRulePreset.CAPITAL_PRESERVATION_DCA)
    price = describe_autotrader_user_rule_preset("price_discipline_dca")
    stop_loss = describe_autotrader_user_rule_preset("protective_stop_loss")

    assert capital is not None
    assert capital["label"] == "Capital Preservation DCA"
    assert capital["mode"] == "dca_swap_exact_in"
    assert capital["optimize_for"] == "capital_preservation"
    assert capital["guard_profile"]["max_live_orders"] == 1

    assert price is not None
    assert price["label"] == "Price Discipline DCA"
    assert price["guard_profile"]["max_slippage_bps"] == 20

    assert stop_loss is not None
    assert stop_loss["label"] == "Protective Stop-Loss"
    assert stop_loss["mode"] == "stop_loss_order_intent"
    assert stop_loss["optimize_for"] == "downside_protection"
    assert stop_loss["authoring_requirements"]["requires_trigger_price"] is True
    assert stop_loss["authoring_requirements"]["requires_cadence_epochs"] is False
    assert stop_loss["live_execution_posture"]["supported"] is False
    assert stop_loss["live_execution_posture"]["reject_reason_when_unsupported"] == "unsupported_live_strategy_mode"



def test_build_autotrader_user_rule_bundle_from_capital_preservation_preset_uses_expected_bounds() -> None:
    bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name="user.rules.bundle.preset.capital",
        built_at="2026-04-09T18:09:00Z",
        strategy_id="user.rule.strategy.preset.capital",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        preset_id=AutoTraderUserRulePreset.CAPITAL_PRESERVATION_DCA,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        fixed_order_size=100,
        cadence_epochs=4,
        valid_from_epoch=10,
        valid_until_epoch=100,
    )

    assert bundle.preset_id is AutoTraderUserRulePreset.CAPITAL_PRESERVATION_DCA
    assert bundle.budget.per_window_max == 200
    assert bundle.budget.lifetime_max == 1600
    assert bundle.risk.max_slippage_bps == 20
    assert bundle.risk.max_oracle_staleness_epochs == 1
    assert bundle.window.min_order_spacing_epochs == 6
    assert bundle.controls.max_live_orders == 1



def test_build_autotrader_user_rule_bundle_from_preset_uses_expected_bounds() -> None:
    bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name="user.rules.bundle.preset.1",
        built_at="2026-04-09T18:10:00Z",
        strategy_id="user.rule.strategy.preset.1",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.TAU,
        preset_id=AutoTraderUserRulePreset.CONSERVATIVE_DCA,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        fixed_order_size=100,
        cadence_epochs=4,
        valid_from_epoch=10,
        valid_until_epoch=100,
    )

    assert bundle.preset_id is AutoTraderUserRulePreset.CONSERVATIVE_DCA
    assert bundle.budget.per_window_max == 400
    assert bundle.budget.lifetime_max == 2400
    assert bundle.risk.max_slippage_bps == 30
    assert bundle.risk.max_oracle_staleness_epochs == 2
    assert bundle.window.min_order_spacing_epochs == 4
    assert bundle.controls.max_live_orders == 2


def test_build_autotrader_user_rule_bundle_from_protective_stop_loss_preset_uses_trigger_bounds() -> None:
    bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name="user.rules.bundle.preset.stop.loss",
        built_at="2026-04-09T18:10:30Z",
        strategy_id="user.rule.strategy.preset.stop.loss",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        preset_id=AutoTraderUserRulePreset.PROTECTIVE_STOP_LOSS,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        fixed_order_size=100,
        trigger_price=90000,
        valid_from_epoch=10,
        valid_until_epoch=100,
    )

    assert bundle.preset_id is AutoTraderUserRulePreset.PROTECTIVE_STOP_LOSS
    assert bundle.mode is AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT
    assert bundle.trigger is not None
    assert bundle.trigger.trigger_price == 90000
    assert bundle.sizing.cadence_epochs is None
    assert bundle.budget.per_window_max == 100
    assert bundle.budget.lifetime_max == 1200
    assert bundle.risk.max_slippage_bps == 25
    assert bundle.risk.max_oracle_staleness_epochs == 1
    assert bundle.controls.max_live_orders == 1


def test_price_discipline_bundle_roundtrip_preserves_preset_id() -> None:
    bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name="user.rules.bundle.preset.price",
        built_at="2026-04-09T18:16:00Z",
        strategy_id="user.rule.strategy.preset.price",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        preset_id=AutoTraderUserRulePreset.PRICE_DISCIPLINE_DCA,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        fixed_order_size=125,
        cadence_epochs=3,
        valid_from_epoch=5,
        valid_until_epoch=80,
    )

    roundtrip = autotrader_user_rule_bundle_from_dict(bundle.to_dict())
    assert roundtrip.to_dict() == bundle.to_dict()
    assert roundtrip.preset_id is AutoTraderUserRulePreset.PRICE_DISCIPLINE_DCA



def test_build_autotrader_user_rule_bundle_from_mode_builds_stop_loss_strategy() -> None:
    bundle = build_autotrader_user_rule_bundle_from_mode(
        bundle_name="user.rules.bundle.stop_loss",
        built_at="2026-04-09T18:18:00Z",
        strategy_id="user.rule.strategy.stop_loss",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        mode=AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        fixed_order_size=125,
        per_window_max=375,
        lifetime_max=1500,
        max_slippage_bps=40,
        max_oracle_staleness_epochs=2,
        valid_from_epoch=5,
        valid_until_epoch=80,
        trigger_price=90000,
    )

    strategy = compile_autotrader_user_rule_bundle(bundle)

    assert strategy.template is StrategyTemplate.STOP_LOSS
    assert strategy.allowed_actions == (StrategyAction.PLACE_ORDER_INTENT,)
    assert strategy.template_params == {
        "trigger_price": 90000,
        "fixed_order_size": 125,
        "asset_in": "zUSD",
        "asset_out": "BTC",
    }


def test_take_profit_user_rule_bundle_roundtrip_preserves_trigger_rules() -> None:
    bundle = AutoTraderUserRuleBundle(
        bundle_name="user.rules.bundle.take_profit",
        built_at="2026-04-09T18:19:00Z",
        compiler_version="autotrader-user-rule-bundle/v1",
        strategy_id="user.rule.strategy.take_profit",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        mode=AutoTraderUserRuleMode.TAKE_PROFIT_ORDER_INTENT,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        sizing=AutoTraderUserSizingRule(fixed_order_size=75),
        budget=AutoTraderUserBudgetRule(per_window_max=225, lifetime_max=900),
        risk=AutoTraderUserRiskRule(max_slippage_bps=25, max_oracle_staleness_epochs=2),
        window=AutoTraderUserWindowRule(valid_from_epoch=3, valid_until_epoch=60),
        trigger=AutoTraderUserTriggerRule(trigger_price=120000),
        controls=AutoTraderUserControlRule(kill_switch_enabled=True, max_live_orders=2),
    )

    roundtrip = autotrader_user_rule_bundle_from_dict(bundle.to_dict())
    assert roundtrip.to_dict() == bundle.to_dict()
    assert roundtrip.trigger is not None
    assert roundtrip.trigger.trigger_price == 120000


def test_user_rule_bundle_roundtrip_preserves_preset_id() -> None:
    bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name="user.rules.bundle.preset.2",
        built_at="2026-04-09T18:15:00Z",
        strategy_id="user.rule.strategy.preset.2",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        preset_id=AutoTraderUserRulePreset.BALANCED_DCA,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        fixed_order_size=125,
        cadence_epochs=3,
        valid_from_epoch=5,
        valid_until_epoch=80,
    )

    roundtrip = autotrader_user_rule_bundle_from_dict(bundle.to_dict())
    assert roundtrip.to_dict() == bundle.to_dict()
    assert roundtrip.preset_id is AutoTraderUserRulePreset.BALANCED_DCA


def test_compile_autotrader_user_rule_bundle_builds_dca_strategy() -> None:
    bundle = _bundle(policy_backend=PolicyBackend.TAU)
    strategy = compile_autotrader_user_rule_bundle(bundle)

    assert strategy.template is StrategyTemplate.DCA
    assert strategy.template_params == {
        "fixed_order_size": 100,
        "cadence_epochs": 4,
        "asset_in": "zUSD",
        "asset_out": "BTC",
    }
    assert strategy.notional_caps.per_order_max == 100
    assert strategy.notional_caps.per_window_max == 500
    assert strategy.notional_caps.lifetime_max == 1000
    assert strategy.tau_policy_specs == AUTOTRADER_TAU_POLICY_SPECS



def test_build_client_policy_surface_from_user_rule_bundle_pins_source_hash() -> None:
    bundle = _bundle(policy_backend=PolicyBackend.LOCAL)
    surface = build_autotrader_client_policy_surface_from_user_rule_bundle(bundle)
    source_artifact = build_autotrader_user_rule_source_artifact(bundle)

    assert surface.strategy.strategy_id == bundle.strategy_id
    assert surface.source_form == "autotrader_user_rule_bundle"
    assert surface.source_artifact_hash == source_artifact.source_artifact_hash_hex()
    assert surface.tau_policy_bundle_hash is None
    assert surface.policy_artifact_hash is None
    assert surface.to_dict()["strategy_logic"]["template"] == "dca"
    assert surface.to_dict()["assurance_artifacts"]["source_form"] == "autotrader_user_rule_bundle"
    assert surface.to_dict()["assurance_artifacts"]["source_preset_id"] is None


def test_build_client_policy_surface_from_preset_user_rule_bundle_pins_preset_id() -> None:
    bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name="user.rules.bundle.preset.surface",
        built_at="2026-04-09T18:20:00Z",
        strategy_id="user.rule.strategy.preset.surface",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        preset_id=AutoTraderUserRulePreset.HIGH_THROUGHPUT_DCA,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        fixed_order_size=200,
        cadence_epochs=1,
        valid_from_epoch=1,
        valid_until_epoch=120,
    )

    surface = build_autotrader_client_policy_surface_from_user_rule_bundle(bundle)
    assert surface.source_preset_id == "high_throughput_dca"
    assert surface.to_dict()["assurance_artifacts"]["source_preset_id"] == "high_throughput_dca"


def test_build_client_policy_bundle_from_user_rule_bundle_roundtrips_signed_bundle(tmp_path: Path) -> None:
    bundle = _bundle()
    client_bundle = build_autotrader_client_policy_bundle_from_user_rule_bundle(
        bundle,
        local_guard_inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=1,
            lifetime_spent=200,
            spent_in_window=100,
            budget_window_id=12,
            kill_switch_active=False,
            last_action_epoch=8,
            slippage_bps=50,
            signal_packet=_packet(),
        ),
    )
    signed = sign_autotrader_client_policy_bundle(client_bundle, privkey=21)
    assert verify_autotrader_client_policy_bundle_signature(signed) is True
    assert signed.client_policy_surface.source_artifact_hash == build_autotrader_user_rule_source_artifact(bundle).source_artifact_hash_hex()

    path = tmp_path / "client_policy_bundle.json"
    path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")
    loaded = load_autotrader_client_policy_bundle_file(path)
    assert loaded.to_dict() == signed.to_dict()
    assert loaded.local_guard_evaluation is not None
    assert loaded.local_guard_evaluation.ok is True



def test_user_rule_bundle_from_dict_rejects_non_bool_control_flag() -> None:
    payload = _bundle().to_dict()
    payload["controls"]["kill_switch_enabled"] = "false"

    with pytest.raises(TypeError, match="controls.kill_switch_enabled must be a bool"):
        autotrader_user_rule_bundle_from_dict(payload)


def test_compile_autotrader_user_rule_bundle_rejects_budget_below_fixed_order_size() -> None:
    bundle = AutoTraderUserRuleBundle(
        bundle_name="user.rules.bundle.bad",
        built_at="2026-04-09T18:05:00Z",
        compiler_version="autotrader-user-rule-bundle/v1",
        strategy_id="user.rule.strategy.bad",
        owner_pubkey=_owner_pubkey(),
        policy_backend=PolicyBackend.LOCAL,
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        market=AutoTraderUserMarket(asset_in="zUSD", asset_out="BTC"),
        sizing=AutoTraderUserSizingRule(fixed_order_size=200, cadence_epochs=4),
        budget=AutoTraderUserBudgetRule(per_window_max=100, lifetime_max=1000),
        risk=AutoTraderUserRiskRule(max_slippage_bps=75, max_oracle_staleness_epochs=3),
        window=AutoTraderUserWindowRule(valid_from_epoch=10, valid_until_epoch=100),
    )

    with pytest.raises(ValueError, match="per_order_max must be <= per_window_max"):
        compile_autotrader_user_rule_bundle(bundle)
