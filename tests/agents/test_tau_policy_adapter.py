from __future__ import annotations

import pytest

from src.agents.policy_artifacts import build_strategy_source_artifact
from src.agents.route_economic_sanity import RouteEconomicSanitySnapshot
from src.agents.strategy_ir import (
    AUTOTRADER_TAU_POLICY_SPECS,
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.agents.tau_policy_adapter import (
    TAU_POLICY_RECEIPT_SCHEMA,
    build_budget_guard_tau_policy_receipt,
    build_compilation_witness_tau_policy_receipt,
    build_compile_contract_tau_policy_receipt,
    build_execution_guard_tau_policy_receipt,
    build_external_signal_source_registry_guard_tau_policy_receipt,
    build_nonce_guard_tau_policy_receipt,
    build_oracle_freshness_guard_tau_policy_receipt,
    build_route_economic_sanity_guard_tau_policy_receipt,
    build_session_capability_binding_guard_tau_policy_receipt,
    build_session_state_guard_tau_policy_receipt,
    build_signal_provenance_guard_tau_policy_receipt,
    build_wallet_capability_guard_tau_policy_receipt,
)
from src.integration.autotrader_signal_registry import (
    ExternalSignalSourceRegistry,
    ExternalSignalSourceRegistryEntry,
)
from src.integration.autotrader_signals import (
    AutoTraderSessionState,
    AutoTraderWalletCapability,
    ExternalSignalObservation,
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
)
from src.integration.tau_witness import (
    AUTOTRADER_BUDGET_GUARD_V1,
    AUTOTRADER_COMPILATION_WITNESS_V1,
    AUTOTRADER_COMPILE_CONTRACT_V1,
    AUTOTRADER_EXECUTION_GUARD_V1,
    AUTOTRADER_NONCE_GUARD_V1,
    AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1,
    AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1,
    AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1,
    AUTOTRADER_SESSION_STATE_GUARD_V1,
    AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1,
    AUTOTRADER_WALLET_CAPABILITY_GUARD_V1,
)
from src.kernels.python.strategy_budget_guard_v1_adapter import StrategyBudgetState


def _tau_strategy() -> StrategyIR:
    return StrategyIR(
        strategy_id="tau.strat.1",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.TAU,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=100, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
        tau_policy_specs=AUTOTRADER_TAU_POLICY_SPECS,
    )


def _signal_packet(*, verified: bool = True) -> QuoteReceiptSignalPacket:
    return QuoteReceiptSignalPacket(
        current_epoch=10,
        quote_epoch=9,
        asset_in="zUSD",
        asset_out="BTC",
        amount_in=100,
        amount_out=95,
        receipt_hash="receipt.hash.1",
        source_kind=SignalSourceKind.ROUTE_QUOTE_RECEIPT,
        trust_tier=SignalTrustTier.VERIFIED,
        quote_receipt_present=True,
        quote_receipt_verified=verified,
        quote_epoch_present=True,
        source_available=True,
        auth_ok=verified,
        binding_ok=verified,
        verify_error=None if verified else "hash mismatch",
    )


def _wallet_capability(**overrides: object) -> AutoTraderWalletCapability:
    data = {
        "session_id": "session.1",
        "owner_pubkey": "owner.pubkey.1",
        "chain_id": "tau-net-alpha",
        "valid_from_epoch": 1,
        "valid_until_epoch": 100,
        "notional_remaining": 500,
        "allowed_assets": ("BTC", "zUSD"),
        "allowed_actions": (StrategyAction.PLACE_SWAP_EXACT_IN,),
        "enabled": True,
    }
    data.update(overrides)
    return AutoTraderWalletCapability(**data)


def _session_state(**overrides: object) -> AutoTraderSessionState:
    data = {
        "session_id": "session.1",
        "owner_pubkey": "owner.pubkey.1",
        "chain_id": "tau-net-alpha",
        "enabled": True,
        "revoked_at_epoch": None,
    }
    data.update(overrides)
    return AutoTraderSessionState(**data)


def _route_snapshot(**overrides: object) -> RouteEconomicSanitySnapshot:
    data = {
        "receipt_verified": True,
        "verification_error": None,
        "receipt_kind": "exact_in",
        "leg_count": 1,
        "hop_count": 1,
        "route_kind_supported": True,
        "body_pair_valid": True,
        "legs_present": True,
        "all_legs_single_hop": True,
        "all_legs_match_body_pair": True,
        "multi_hop_present": False,
        "route_shape_supported_for_intents": True,
        "max_hop_input_vs_reserve_bps": 2500,
        "max_hop_output_vs_reserve_bps": 2000,
        "max_hop_price_impact_bps": 800,
        "dominant_hop_pool_id": "p_ab",
        "dominant_hop_asset_in": "zUSD",
        "dominant_hop_asset_out": "BTC",
        "dominant_hop_amount_in": 100,
        "dominant_hop_reserve_in": 1000,
        "dominant_hop_amount_out": 95,
        "dominant_hop_reserve_out": 2000,
        "extreme_input_stress_present": False,
        "extreme_output_depletion_present": False,
        "extreme_price_impact_present": False,
        "route_economic_sanity_ok": True,
        "classification_error": None,
    }
    data.update(overrides)
    return RouteEconomicSanitySnapshot(**data)


def test_build_budget_guard_tau_policy_receipt_accept_path() -> None:
    receipt = build_budget_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        state=StrategyBudgetState(window_id=1, spent_in_window=100, kill_switch_on=False),
        order_amount=50,
    )
    assert receipt.spec_id == AUTOTRADER_BUDGET_GUARD_V1.spec_id
    assert receipt.expected_ok is True
    assert receipt.steps[0]["i5"] == 150
    assert receipt.to_dict()["schema"] == TAU_POLICY_RECEIPT_SCHEMA


def test_build_compile_contract_tau_policy_receipt_accept_and_reject_paths() -> None:
    receipt = build_compile_contract_tau_policy_receipt(strategy=_tau_strategy())
    assert receipt.spec_id == AUTOTRADER_COMPILE_CONTRACT_V1.spec_id
    assert receipt.expected_ok is True
    assert receipt.steps[0]["i1"] == 1
    assert receipt.steps[0]["i13"] == 1
    assert receipt.to_dict()["schema"] == TAU_POLICY_RECEIPT_SCHEMA

    reject_strategy = _tau_strategy()
    object.__setattr__(reject_strategy, "tau_policy_specs", ("autotrader_budget_guard_v1",))
    reject = build_compile_contract_tau_policy_receipt(strategy=reject_strategy)
    assert reject.expected_ok is False
    assert reject.steps[0]["i13"] == 0


def test_build_compile_contract_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_compile_contract_tau_policy_receipt(strategy="bad")


def test_build_compilation_witness_tau_policy_receipt_accept_and_reject_paths() -> None:
    strategy = _tau_strategy()
    source_artifact = build_strategy_source_artifact(
        strategy=strategy,
        source_form="sentence",
        source_text="dca 100 zUSD into BTC every 4 epochs",
    )
    compile_receipt = build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict()

    receipt = build_compilation_witness_tau_policy_receipt(
        strategy=strategy,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=compile_receipt,
    )
    assert receipt.spec_id == AUTOTRADER_COMPILATION_WITNESS_V1.spec_id
    assert receipt.expected_ok is True
    assert receipt.steps[0]["i1"] == 1
    assert receipt.steps[0]["i14"] == 1
    assert receipt.to_dict()["schema"] == TAU_POLICY_RECEIPT_SCHEMA

    tampered = _tau_strategy()
    object.__setattr__(
        tampered,
        "template_params",
        {
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "BTC",
            "asset_out": "zUSD",
        },
    )
    reject = build_compilation_witness_tau_policy_receipt(
        strategy=tampered,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=compile_receipt,
    )
    assert reject.expected_ok is False
    assert reject.steps[0]["i2"] == 0
    assert reject.steps[0]["i12"] == 0


def test_build_compilation_witness_tau_policy_receipt_rejects_bad_types() -> None:
    strategy = _tau_strategy()
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    compile_receipt = build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict()

    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_compilation_witness_tau_policy_receipt(
            strategy="bad",
            source_artifact=source_artifact,
            compile_contract_tau_receipt=compile_receipt,
        )
    with pytest.raises(TypeError, match="source_artifact must be a StrategySourceArtifact"):
        build_compilation_witness_tau_policy_receipt(
            strategy=strategy,
            source_artifact="bad",
            compile_contract_tau_receipt=compile_receipt,
        )
    with pytest.raises(TypeError, match="compile_contract_tau_receipt must be an object"):
        build_compilation_witness_tau_policy_receipt(
            strategy=strategy,
            source_artifact=source_artifact,
            compile_contract_tau_receipt="bad",
        )


def test_build_budget_guard_tau_policy_receipt_local_backend_without_tau_spec() -> None:
    strategy = StrategyIR(
        strategy_id="local.strat.1",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=100, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
    )
    receipt = build_budget_guard_tau_policy_receipt(
        strategy=strategy,
        state=StrategyBudgetState(window_id=1, spent_in_window=0, kill_switch_on=True),
        order_amount=10,
    )
    assert receipt.expected_ok is False
    assert receipt.steps[0]["i6"] == 1


def test_build_budget_guard_tau_policy_receipt_reject_path_still_emits_step() -> None:
    receipt = build_budget_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        state=StrategyBudgetState(window_id=1, spent_in_window=480, kill_switch_on=False),
        order_amount=40,
    )
    assert receipt.expected_ok is False
    assert receipt.steps[0]["i5"] == 520


def test_build_budget_guard_tau_policy_receipt_rejects_bad_types_and_overflow() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_budget_guard_tau_policy_receipt(
            strategy="bad",
            state=StrategyBudgetState(window_id=1, spent_in_window=0, kill_switch_on=False),
            order_amount=1,
        )
    with pytest.raises(TypeError, match="state must be a StrategyBudgetState"):
        build_budget_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            state="bad",
            order_amount=1,
        )
    with pytest.raises(ValueError, match="tau budget witness overflow"):
        build_budget_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            state=StrategyBudgetState(window_id=1, spent_in_window=4_294_967_295, kill_switch_on=False),
            order_amount=1,
        )


def test_build_budget_guard_tau_policy_receipt_rejects_tampered_tau_bundle() -> None:
    strategy = _tau_strategy()
    object.__setattr__(strategy, "tau_policy_specs", ("other_spec",))
    with pytest.raises(ValueError, match="tau strategy must bind"):
        build_budget_guard_tau_policy_receipt(
            strategy=strategy,
            state=StrategyBudgetState(window_id=1, spent_in_window=0, kill_switch_on=False),
            order_amount=1,
        )


def test_build_execution_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    receipt = build_execution_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        current_epoch=10,
        last_action_epoch=5,
        projected_live_orders=1,
    )
    assert receipt.spec_id == AUTOTRADER_EXECUTION_GUARD_V1.spec_id
    assert receipt.expected_ok is True
    assert receipt.steps[0]["i8"] == 1

    reject_receipt = build_execution_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        current_epoch=10,
        last_action_epoch=5,
        projected_live_orders=2,
    )
    assert reject_receipt.expected_ok is False
    assert reject_receipt.steps[0]["i9"] == 1


def test_build_execution_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_execution_guard_tau_policy_receipt(
            strategy="bad",
            current_epoch=10,
            last_action_epoch=5,
            projected_live_orders=1,
        )


def test_build_oracle_freshness_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    receipt = build_oracle_freshness_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        current_epoch=10,
        quote_epoch=8,
    )
    assert receipt.spec_id == AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.spec_id
    assert receipt.expected_ok is True
    assert receipt.steps[0]["i2"] == 8

    reject_receipt = build_oracle_freshness_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        current_epoch=10,
        quote_epoch=6,
    )
    assert reject_receipt.expected_ok is False
    assert reject_receipt.steps[0]["i3"] == 3


def test_build_oracle_freshness_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_oracle_freshness_guard_tau_policy_receipt(
            strategy="bad",
            current_epoch=10,
            quote_epoch=8,
        )


def test_build_route_economic_sanity_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    accept = build_route_economic_sanity_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        snapshot=_route_snapshot(),
    )
    assert accept.spec_id == AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.spec_id
    assert accept.expected_ok is True
    assert accept.steps[0]["i8"] == 2500
    assert accept.to_dict()["schema"] == TAU_POLICY_RECEIPT_SCHEMA

    reject = build_route_economic_sanity_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        snapshot=_route_snapshot(
            max_hop_input_vs_reserve_bps=10_000,
            extreme_input_stress_present=True,
            route_economic_sanity_ok=False,
            classification_error="route_extreme_input_stress:max=10000,threshold=10000",
        ),
    )
    assert reject.expected_ok is False
    assert reject.steps[0]["i8"] == 10_000
    assert reject.steps[0]["i11"] == 10_000


def test_build_route_economic_sanity_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_route_economic_sanity_guard_tau_policy_receipt(
            strategy="bad",
            snapshot=_route_snapshot(),
        )
    with pytest.raises(TypeError, match="snapshot must be a RouteEconomicSanitySnapshot"):
        build_route_economic_sanity_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            snapshot="bad",
        )


def test_build_signal_provenance_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    accept = build_signal_provenance_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        packet=_signal_packet(),
    )
    assert accept.spec_id == AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.spec_id
    assert accept.expected_ok is True
    assert accept.steps[0]["i1"] == 1
    assert accept.to_dict()["schema"] == TAU_POLICY_RECEIPT_SCHEMA

    reject = build_signal_provenance_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        packet=_signal_packet(verified=False),
    )
    assert reject.expected_ok is False
    assert reject.steps[0]["i4"] == 0
    assert reject.steps[0]["i7"] == 0


def test_build_signal_provenance_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_signal_provenance_guard_tau_policy_receipt(strategy="bad", packet=_signal_packet())
    with pytest.raises(TypeError, match="packet must be a QuoteReceiptSignalPacket"):
        build_signal_provenance_guard_tau_policy_receipt(strategy=_tau_strategy(), packet="bad")


def test_build_external_signal_source_registry_guard_tau_policy_receipt_accept_and_missing_paths() -> None:
    signal = ExternalSignalObservation(
        signal_id="sig.oracle.1",
        source_id="oracle.alpha",
        source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
        trust_tier=SignalTrustTier.VERIFIED,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=False,
    )
    registry = ExternalSignalSourceRegistry(
        entries=(
            ExternalSignalSourceRegistryEntry(
                source_id="oracle.alpha",
                source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
                allowed_trust_tiers=(SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED),
                require_auth=True,
                require_freshness=True,
            ),
        )
    )
    accept = build_external_signal_source_registry_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        signal=signal,
        registry=registry,
    )
    assert accept.spec_id == "autotrader_external_signal_source_registry_guard_v1"
    assert accept.expected_ok is True
    assert accept.steps[0]["i1"] == 1
    assert accept.steps[0]["i15"] == 1

    missing = build_external_signal_source_registry_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        signal=signal,
        registry=None,
    )
    assert missing.expected_ok is False
    assert missing.steps[0]["i1"] == 0
    assert missing.steps[0]["i8"] == 0


def test_build_external_signal_source_registry_guard_tau_policy_receipt_rejects_bad_types() -> None:
    signal = ExternalSignalObservation(
        signal_id="sig.oracle.1",
        source_id="oracle.alpha",
        source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
        trust_tier=SignalTrustTier.VERIFIED,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=False,
    )
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_external_signal_source_registry_guard_tau_policy_receipt(
            strategy="bad",
            signal=signal,
            registry=None,
        )
    with pytest.raises(TypeError, match="signal must be an ExternalSignalObservation"):
        build_external_signal_source_registry_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            signal="bad",
            registry=None,
        )
    with pytest.raises(TypeError, match="registry must be an ExternalSignalSourceRegistry or None"):
        build_external_signal_source_registry_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            signal=signal,
            registry="bad",
        )


def test_build_wallet_capability_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    accept = build_wallet_capability_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        capability=_wallet_capability(),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=10,
        asset_in="zUSD",
        asset_out="BTC",
        order_amount=100,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert accept.spec_id == AUTOTRADER_WALLET_CAPABILITY_GUARD_V1.spec_id
    assert accept.expected_ok is True
    assert accept.steps[0]["i10"] == 100

    reject = build_wallet_capability_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        capability=_wallet_capability(enabled=False, notional_remaining=50),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=10,
        asset_in="zUSD",
        asset_out="BTC",
        order_amount=100,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert reject.expected_ok is False
    assert reject.steps[0]["i1"] == 0
    assert reject.steps[0]["i11"] == 50


def test_build_wallet_capability_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_wallet_capability_guard_tau_policy_receipt(
            strategy="bad",
            capability=_wallet_capability(),
            signer_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            current_epoch=10,
            asset_in="zUSD",
            asset_out="BTC",
            order_amount=100,
            action=StrategyAction.PLACE_SWAP_EXACT_IN,
        )
    with pytest.raises(TypeError, match="capability must be an AutoTraderWalletCapability"):
        build_wallet_capability_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            capability="bad",
            signer_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            current_epoch=10,
            asset_in="zUSD",
            asset_out="BTC",
            order_amount=100,
            action=StrategyAction.PLACE_SWAP_EXACT_IN,
        )
    with pytest.raises(TypeError, match="action must be a StrategyAction"):
        build_wallet_capability_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            capability=_wallet_capability(),
            signer_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            current_epoch=10,
            asset_in="zUSD",
            asset_out="BTC",
            order_amount=100,
            action="bad",
        )


def test_build_session_capability_binding_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    accept = build_session_capability_binding_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        capability=_wallet_capability(),
        chain_id="tau-net-alpha",
    )
    assert accept.spec_id == AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1.spec_id
    assert accept.expected_ok is True
    assert accept.steps[0]["i9"] == 100

    reject = build_session_capability_binding_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        capability=_wallet_capability(valid_from_epoch=0),
        chain_id="tau-net-alpha",
    )
    assert reject.expected_ok is False
    assert reject.steps[0]["i6"] == 0


def test_build_session_capability_binding_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_session_capability_binding_guard_tau_policy_receipt(
            strategy="bad",
            capability=_wallet_capability(),
            chain_id="tau-net-alpha",
        )


def test_build_session_state_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    accept = build_session_state_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        session_state=_session_state(),
        capability=_wallet_capability(),
        chain_id="tau-net-alpha",
        current_epoch=10,
    )
    assert accept.spec_id == AUTOTRADER_SESSION_STATE_GUARD_V1.spec_id
    assert accept.expected_ok is True
    assert accept.steps[0]["i6"] == 10

    reject = build_session_state_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        session_state=_session_state(revoked_at_epoch=10),
        capability=_wallet_capability(),
        chain_id="tau-net-alpha",
        current_epoch=10,
    )
    assert reject.expected_ok is False
    assert reject.steps[0]["i5"] == 1
    assert reject.steps[0]["i7"] == 10


def test_build_session_state_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_session_state_guard_tau_policy_receipt(
            strategy="bad",
            session_state=_session_state(),
            capability=_wallet_capability(),
            chain_id="tau-net-alpha",
            current_epoch=10,
        )
    with pytest.raises(TypeError, match="session_state must be an AutoTraderSessionState"):
        build_session_state_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            session_state="bad",
            capability=_wallet_capability(),
            chain_id="tau-net-alpha",
            current_epoch=10,
        )
    with pytest.raises(TypeError, match="capability must be an AutoTraderWalletCapability"):
        build_session_state_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            session_state=_session_state(),
            capability="bad",
            chain_id="tau-net-alpha",
            current_epoch=10,
        )
    with pytest.raises(TypeError, match="capability must be an AutoTraderWalletCapability"):
        build_session_capability_binding_guard_tau_policy_receipt(
            strategy=_tau_strategy(),
            capability="bad",
            chain_id="tau-net-alpha",
        )


def test_build_nonce_guard_tau_policy_receipt_accept_and_reject_paths() -> None:
    accept = build_nonce_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        intent_nonce=9,
        last_used_nonce=8,
        expected_nonce=9,
    )
    assert accept.spec_id == AUTOTRADER_NONCE_GUARD_V1.spec_id
    assert accept.expected_ok is True
    assert accept.steps[0]["i3"] == 9

    reject = build_nonce_guard_tau_policy_receipt(
        strategy=_tau_strategy(),
        intent_nonce=11,
        last_used_nonce=8,
        expected_nonce=9,
    )
    assert reject.expected_ok is False
    assert reject.steps[0]["i1"] == 11


def test_build_nonce_guard_tau_policy_receipt_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_nonce_guard_tau_policy_receipt(
            strategy="bad",
            intent_nonce=9,
            last_used_nonce=8,
            expected_nonce=9,
        )
