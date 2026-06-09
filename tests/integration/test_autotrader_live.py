from __future__ import annotations

import sys
from dataclasses import replace
from types import SimpleNamespace

import pytest

import src.integration.autotrader_live as autotrader_live
from src.agents.autotrader_client_policy_bundle import (
    AutoTraderClientPolicyBundle,
    build_autotrader_client_policy_bundle,
    sign_autotrader_client_policy_bundle,
)
from src.agents.autotrader_client_policy_surface import build_autotrader_client_policy_surface
from src.agents.autotrader_user_rule_bundle import (
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
    build_autotrader_client_policy_bundle_from_user_rule_bundle,
    build_autotrader_user_rule_bundle_from_mode,
    build_autotrader_user_rule_bundle_from_preset,
    build_autotrader_user_rule_source_artifact,
    compile_autotrader_user_rule_bundle,
)
from src.agents.policy_artifacts import build_strategy_source_artifact
from src.agents.intent_signer import (
    _create_canonical_message,
    create_swap_intent,
    verify_intent_signature,
)
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS, StrategyIR
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_controller import (
    AutoTraderControllerState,
    AutoTraderDecisionTag,
    AutoTraderGuardState,
    AutoTraderTauConfig,
)
from src.integration.autotrader_decision import DecisionCandidateKind
from src.integration.autotrader_live import prepare_autotrader_live_quote_receipt
from src.integration.autotrader_signal_registry import (
    ExternalSignalSourceRegistry,
    ExternalSignalSourceRegistryEntry,
)
from src.integration.autotrader_signals import (
    AutoTraderSessionState,
    AutoTraderWalletCapability,
    ExternalSignalObservation,
    SignalSourceKind,
    SignalTrustTier,
)
from src.integration.dex_engine import _verify_intent_signature_bytes
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.state.intents import SignedIntent
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _single_hop_receipt(*, amount_in: int = 100, quote_epoch: int = 5) -> tuple[dict[str, PoolState], dict[str, object]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=amount_in)
    assert quote is not None
    assert len(quote.legs) == 1
    assert len(quote.legs[0].hops) == 1
    receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=quote,
        pools_by_id=pools,
        quote_epoch=quote_epoch,
    )
    return pools, receipt


def _split_receipt(*, amount_in: int = 600, quote_epoch: int = 5) -> tuple[dict[str, PoolState], dict[str, object]]:
    pools = {
        "p1": _pool("p1", "A", "B", 1_000, 1_000, 0),
        "p2": _pool("p2", "A", "B", 1_000, 1_000, 0),
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=amount_in)
    assert quote is not None
    assert len(quote.legs) >= 2
    receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=quote,
        pools_by_id=pools,
        quote_epoch=quote_epoch,
    )
    return pools, receipt


def _compiled_strategy(
    *,
    owner_pubkey: str,
    backend: str = "local",
    fixed_order_size: int = 100,
    max_live_orders: int = 3,
    allowed_actions: tuple[autotrader_live.StrategyAction, ...] | None = None,
) -> StrategyIR:
    return compile_policy_candidate(
        {
            "strategy_id": f"dca.{backend}.live",
            "owner_pubkey": owner_pubkey,
            "policy_backend": backend,
            "template": "dca",
            "asset_universe": ["A", "B"],
            "allowed_actions": [
                action.value
                for action in (
                    allowed_actions
                    if allowed_actions is not None
                    else (autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,)
                )
            ],
            "notional_caps": {
                "per_order_max": fixed_order_size,
                "per_window_max": 1_000,
                "lifetime_max": 10_000,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "min_order_spacing_epochs": 0,
            },
            "controls": {
                "kill_switch_enabled": True,
                "max_live_orders": max_live_orders,
            },
            "template_params": {
                "fixed_order_size": fixed_order_size,
                "cadence_epochs": 4,
                "asset_in": "A",
                "asset_out": "B",
            },
            "tau_policy_specs": list(AUTOTRADER_TAU_POLICY_SPECS) if backend == "tau" else [],
        }
    ).strategy


def _user_rule_bundle(*, owner_pubkey: str, backend: str = "local") -> AutoTraderUserRuleBundle:
    return AutoTraderUserRuleBundle(
        bundle_name=f"{backend}.user.rules.bundle",
        built_at="2026-04-09T19:00:00Z",
        compiler_version="autotrader-user-rule-bundle/v1",
        strategy_id=f"{backend}.user.rules.strategy",
        owner_pubkey=owner_pubkey,
        policy_backend=autotrader_live.PolicyBackend(backend),
        mode=AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN,
        market=AutoTraderUserMarket(asset_in="A", asset_out="B"),
        sizing=AutoTraderUserSizingRule(fixed_order_size=100, cadence_epochs=4),
        budget=AutoTraderUserBudgetRule(per_window_max=500, lifetime_max=1_000),
        risk=AutoTraderUserRiskRule(max_slippage_bps=50, max_oracle_staleness_epochs=3),
        window=AutoTraderUserWindowRule(valid_from_epoch=1, valid_until_epoch=100),
        controls=AutoTraderUserControlRule(kill_switch_enabled=True, max_live_orders=3),
    )


def _client_policy_bundle(strategy: StrategyIR, *, privkey: int) -> AutoTraderClientPolicyBundle:
    surface = build_autotrader_client_policy_surface(strategy=strategy)
    bundle = build_autotrader_client_policy_bundle(
        bundle_name=f"{strategy.strategy_id}.bundle",
        built_at="2026-04-09T16:00:00Z",
        client_policy_surface=surface,
    )
    return sign_autotrader_client_policy_bundle(bundle, privkey=privkey)


def _pinned_client_policy_bundle(
    strategy: StrategyIR,
    *,
    privkey: int,
    source_artifact_hash: str | None = None,
    tau_policy_bundle_hash: str | None = None,
    policy_artifact_hash: str | None = None,
) -> AutoTraderClientPolicyBundle:
    source_artifact = build_strategy_source_artifact(
        strategy=strategy,
        source_form="compiled_strategy_ir",
    )
    tau_policy_bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=autotrader_live.build_compile_contract_tau_policy_receipt(
            strategy=strategy
        ).to_dict(),
    )
    policy_artifact = autotrader_live.sign_strategy_policy_artifact(
        autotrader_live.build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=tau_policy_bundle,
            source_artifact=source_artifact,
        ),
        privkey=privkey,
    )
    surface = build_autotrader_client_policy_surface(
        strategy=strategy,
        source_artifact=source_artifact,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )
    if any(
        value is not None
        for value in (source_artifact_hash, tau_policy_bundle_hash, policy_artifact_hash)
    ):
        surface = replace(
            surface,
            source_artifact_hash=(
                source_artifact_hash
                if source_artifact_hash is not None
                else surface.source_artifact_hash
            ),
            tau_policy_bundle_hash=(
                tau_policy_bundle_hash
                if tau_policy_bundle_hash is not None
                else surface.tau_policy_bundle_hash
            ),
            policy_artifact_hash=(
                policy_artifact_hash
                if policy_artifact_hash is not None
                else surface.policy_artifact_hash
            ),
        )
    bundle = build_autotrader_client_policy_bundle(
        bundle_name=f"{strategy.strategy_id}.bundle",
        built_at="2026-04-09T16:00:00Z",
        client_policy_surface=surface,
    )
    return sign_autotrader_client_policy_bundle(bundle, privkey=privkey)


def test_prepare_autotrader_live_submit_builds_signed_ops_and_tau_tx_payload() -> None:
    privkey = 7
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        tx_sequence_number=9,
        tx_expiration_time=999,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.local_guard_evaluation is not None
    assert report.local_guard_evaluation.ok is True
    assert report.local_guard_evaluation.blocking_families == ()
    assert report.live_admission_ok is True
    assert report.live_admission_error is None
    assert report.system_compose_ok is True
    assert report.system_compose_error is None
    assert report.submit_bundle_ok is True
    assert report.submit_bundle_error is None
    assert report.emit_finalize_ok is True
    assert report.emit_finalize_error is None
    assert report.krr_advice is not None
    assert report.krr_explanation is not None
    assert report.user_rule_summary is not None
    assert report.actionability_explanation is not None
    assert report.user_rule_summary["source_form"] == "compiled_strategy_ir"
    assert report.user_rule_summary["overall_support_status"] == "supported"
    assert report.user_rule_summary["surface_support_matrix"]["compile"]["supported"] is True
    assert report.user_rule_summary["surface_support_matrix"]["shadow"]["supported"] is True
    assert report.user_rule_summary["surface_support_matrix"]["live"]["supported"] is True
    assert report.user_rule_summary["intent"]["asset_pair"] == "A/B"
    assert report.user_rule_summary["sizing"]["fixed_order_size"] == 100
    assert report.user_rule_summary["budget"]["per_window_max"] == 1000
    assert report.krr_explanation["authoring_posture"]["source_form"] == "compiled_strategy_ir"
    assert report.krr_explanation["trust_posture"]["primary_trust_tier"] == "verified"
    assert report.krr_explanation["trust_posture"]["primary_weighted_trust_score"] == 0.95
    assert report.krr_explanation["trust_posture"]["weighted_trusted_signal_score"] == 0.95
    assert report.krr_explanation["confidence_posture"]["discounted"] is False
    assert report.actionability_explanation["actionability"]["actionable"] is True
    assert report.actionability_explanation["actionability"]["blocking_layer"] is None
    assert report.actionability_explanation["authoring"]["overall_support_status"] == "supported"
    assert report.actionability_explanation["authoring"]["surface_support_matrix"]["live"]["supported"] is True
    assert report.actionability_explanation["intent"]["asset_pair"] == "A/B"
    assert report.actionability_explanation["trust_posture"]["primary_trust_tier"] == "verified"
    assert report.actionability_summary is not None
    assert report.actionability_summary["headline"] == "Actionable: submit because ok."
    assert report.actionability_summary["trust_summary"] == "Trust posture: primary tier verified from 1 trusted signal without registry support. Weighted support: primary=0.95, trusted=0.95."
    assert "live::nonce_guard" in report.krr_advice["preferred_checks"]
    assert report.last_used_nonce_after == 1
    assert report.bounded_multiaction_candidate_set is not None
    assert report.bounded_multiaction_candidate_set_contract == {
        "ok": True,
        "error": None,
        "frontier_unambiguous": True,
    }
    assert report.bounded_multiaction_decision_certificate is not None
    assert report.bounded_multiaction_decision_witness is not None
    assert report.bounded_multiaction_decision_contract == {
        "ok": True,
        "error": None,
        "frontier_unambiguous": True,
    }
    assert report.bounded_multiaction_decision_witness_contract == {
        "ok": True,
        "error": None,
        "frontier_unambiguous": True,
    }
    assert report.bounded_multiaction_tau_argmax_contract == {
        "ok": None,
        "error": "tau_disabled",
        "tau_enabled": False,
        "tau_used": False,
        "frontier_unambiguous": True,
    }
    assert len(report.signed_intents) == 1
    assert report.operations["2"][0]["signature"].startswith("0x")
    assert report.tau_tx_payload is not None
    assert report.tau_tx_payload["sequence_number"] == 9
    assert report.tau_tx_payload["expiration_time"] == 999
    assert report.tx_envelope_tau_receipt is None

    env = report.signed_intents[0]
    ok, err = _verify_intent_signature_bytes(
        sender_pubkey_hex=env.intent.sender_pubkey,
        signature_hex=str(env.signature),
        signing_payload_bytes=_create_canonical_message(env.intent),
        chain_id="tau-local",
    )
    assert ok, err
    assert verify_intent_signature(
        SignedIntent(intent=env.intent, signature=str(env.signature)),
        chain_id="tau-local",
    ) is True


def test_prepare_autotrader_live_actionability_summary_surfaces_weighted_external_trust() -> None:
    privkey = 8
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
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

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        tx_sequence_number=10,
        tx_expiration_time=1000,
        external_signals=(signal,),
        signal_source_registry=registry,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.actionability_summary is not None
    trust_summary = report.actionability_summary["trust_summary"]
    assert isinstance(trust_summary, str)
    assert "with registry support" in trust_summary
    assert "Weighted support:" in trust_summary
    assert "external=" in trust_summary


def test_prepare_autotrader_live_marks_multiaction_sidecar_ambiguous_for_multi_action_strategy() -> None:
    privkey = 23
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(
        owner_pubkey=owner_pubkey,
        allowed_actions=(
            autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,
            autotrader_live.StrategyAction.PLACE_ORDER_INTENT,
        ),
    )
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.bounded_multiaction_candidate_set is None
    assert report.bounded_multiaction_candidate_set_contract == {
        "ok": None,
        "error": "multi_action_frontier_ambiguous",
        "frontier_unambiguous": False,
    }
    assert report.bounded_multiaction_decision_certificate is None
    assert report.bounded_multiaction_decision_witness is None
    assert report.bounded_multiaction_decision_contract == {
        "ok": None,
        "error": "multi_action_frontier_ambiguous",
        "frontier_unambiguous": False,
    }
    assert report.bounded_multiaction_decision_witness_contract == {
        "ok": None,
        "error": "multi_action_frontier_ambiguous",
        "frontier_unambiguous": False,
    }
    assert report.bounded_multiaction_tau_argmax_contract == {
        "ok": None,
        "error": "multi_action_frontier_ambiguous",
        "tau_enabled": False,
        "tau_used": False,
        "frontier_unambiguous": False,
    }


def test_prepare_autotrader_live_submit_with_tau_nonce_checks_on_split_receipt(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 8
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau", fixed_order_size=600, max_live_orders=5)
    pools, receipt = _split_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        lambda **kwargs: None,
    )
    monkeypatch.setattr(autotrader_live, "_verify_boolean_tau_receipt", lambda **kwargs: None)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=11,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.live_admission_ok is True
    assert report.system_compose_ok is True
    assert report.system_compose_error is None
    assert report.submit_bundle_ok is True
    assert report.emit_finalize_ok is True
    assert report.wallet_capability is not None
    assert report.session_state is not None
    assert report.session_state_tau_receipt is not None
    assert report.session_capability_tau_receipt is not None
    assert report.wallet_capability_tau_receipt is not None
    assert report.tx_envelope_tau_receipt is None
    assert len(report.signed_intents) >= 2
    assert [r.expected_nonce for r in report.nonce_tau_receipts] == list(range(12, 12 + len(report.signed_intents)))
    assert report.last_used_nonce_after == 11 + len(report.signed_intents)


def test_prepare_autotrader_live_accepts_supplied_policy_bundle_and_artifact() -> None:
    privkey = 80
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    compile_receipt = autotrader_live.build_compile_contract_tau_policy_receipt(strategy=strategy)
    bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=compile_receipt.to_dict(),
    )
    artifact = autotrader_live.sign_strategy_policy_artifact(
        autotrader_live.build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle),
        privkey=privkey,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_policy_bundle=bundle,
        policy_artifact=artifact,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.tau_policy_bundle == bundle
    assert report.policy_artifact == artifact


def test_prepare_autotrader_live_krr_advice_reflects_user_rule_bundle_authoring() -> None:
    privkey = 31
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    user_bundle = _user_rule_bundle(owner_pubkey=owner_pubkey)
    strategy = compile_autotrader_user_rule_bundle(user_bundle)
    source_artifact = build_autotrader_user_rule_source_artifact(user_bundle)
    tau_policy_bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=autotrader_live.build_compile_contract_tau_policy_receipt(
            strategy=strategy
        ).to_dict(),
    )
    policy_artifact = autotrader_live.sign_strategy_policy_artifact(
        autotrader_live.build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=tau_policy_bundle,
            source_artifact=source_artifact,
        ),
        privkey=privkey,
    )
    client_policy_bundle = build_autotrader_client_policy_bundle_from_user_rule_bundle(
        user_bundle,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )
    client_policy_bundle = sign_autotrader_client_policy_bundle(client_policy_bundle, privkey=privkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        client_policy_bundle=client_policy_bundle,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.client_policy_bundle_ok is True
    assert report.krr_advice is not None
    assert report.krr_explanation is not None
    assert report.user_rule_summary is not None
    assert report.actionability_explanation is not None
    assert report.user_rule_summary["source_form"] == "autotrader_user_rule_bundle"
    assert report.user_rule_summary["authoring_mode"] == "dca_swap_exact_in"
    assert report.user_rule_summary["sizing"]["cadence_epochs"] == 4
    assert report.actionability_explanation["authoring"]["source_form"] == "autotrader_user_rule_bundle"
    assert report.actionability_explanation["authoring"]["authoring_mode"] == "dca_swap_exact_in"
    assert report.krr_explanation["authoring_posture"]["source_form"] == "autotrader_user_rule_bundle"
    assert report.krr_explanation["authoring_posture"]["authored_via_user_bundle"] is True
    assert report.krr_explanation["authoring_posture"]["asset_pair"] == "A/B"
    assert report.krr_advice["authoring_summary"]["source_form"] == "autotrader_user_rule_bundle"
    assert report.krr_advice["authoring_summary"]["authored_via_user_bundle"] is True
    assert report.krr_advice["authoring_summary"]["authoring_mode"] == "dca_swap_exact_in"
    assert "authored_via_user_bundle=1" in report.krr_advice["semantic_signature"]
    assert "authoring_mode=dca_swap_exact_in" in report.krr_advice["semantic_signature"]


def test_prepare_autotrader_live_rejects_unsupported_stop_loss_user_rule_mode() -> None:
    privkey = 131
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    user_bundle = build_autotrader_user_rule_bundle_from_mode(
        bundle_name="stop_loss.user.rules.bundle",
        built_at="2026-04-09T19:05:00Z",
        strategy_id="stop_loss.user.rules.strategy",
        owner_pubkey=owner_pubkey,
        policy_backend=autotrader_live.PolicyBackend.LOCAL,
        mode=AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT,
        market=AutoTraderUserMarket(asset_in="A", asset_out="B"),
        fixed_order_size=100,
        per_window_max=300,
        lifetime_max=1200,
        max_slippage_bps=50,
        max_oracle_staleness_epochs=3,
        valid_from_epoch=1,
        valid_until_epoch=100,
        trigger_price=90000,
    )
    strategy = compile_autotrader_user_rule_bundle(user_bundle)
    source_artifact = build_autotrader_user_rule_source_artifact(user_bundle)
    tau_policy_bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=autotrader_live.build_compile_contract_tau_policy_receipt(
            strategy=strategy
        ).to_dict(),
    )
    policy_artifact = autotrader_live.sign_strategy_policy_artifact(
        autotrader_live.build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=tau_policy_bundle,
            source_artifact=source_artifact,
        ),
        privkey=privkey,
    )
    client_policy_bundle = sign_autotrader_client_policy_bundle(
        build_autotrader_client_policy_bundle_from_user_rule_bundle(
            user_bundle,
            tau_policy_bundle=tau_policy_bundle,
            policy_artifact=policy_artifact,
        ),
        privkey=privkey,
    )
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        client_policy_bundle=client_policy_bundle,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.live_admission_ok is False
    assert report.live_admission_error == "unsupported_live_strategy_mode"
    assert report.user_rule_summary is not None
    assert report.user_rule_summary["overall_support_status"] == "compile_only"
    assert report.user_rule_summary["surface_support_matrix"]["compile"]["supported"] is True
    assert report.user_rule_summary["surface_support_matrix"]["shadow"]["supported"] is False
    assert report.user_rule_summary["surface_support_matrix"]["live"]["supported"] is False
    assert report.user_rule_summary["intent"]["template"] == "stop_loss"
    assert report.user_rule_summary["trigger"]["trigger_price"] == 90000
    assert report.actionability_explanation is not None
    assert report.actionability_explanation["authoring"]["overall_support_status"] == "compile_only"
    assert report.actionability_explanation["authoring"]["surface_support_matrix"]["live"]["status"] == "rejected"
    assert report.actionability_explanation["actionability"]["blocking_layer"] == "live_admission"


def test_prepare_autotrader_live_preserves_user_rule_preset_authoring() -> None:
    privkey = 32
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    user_bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name="preset.user.rules.bundle",
        built_at="2026-04-09T19:10:00Z",
        strategy_id="preset.user.rules.strategy",
        owner_pubkey=owner_pubkey,
        policy_backend=autotrader_live.PolicyBackend.LOCAL,
        preset_id=AutoTraderUserRulePreset.CONSERVATIVE_DCA,
        market=AutoTraderUserMarket(asset_in="A", asset_out="B"),
        fixed_order_size=100,
        cadence_epochs=4,
        valid_from_epoch=1,
        valid_until_epoch=100,
    )
    strategy = compile_autotrader_user_rule_bundle(user_bundle)
    source_artifact = build_autotrader_user_rule_source_artifact(user_bundle)
    tau_policy_bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=autotrader_live.build_compile_contract_tau_policy_receipt(
            strategy=strategy
        ).to_dict(),
    )
    policy_artifact = autotrader_live.sign_strategy_policy_artifact(
        autotrader_live.build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=tau_policy_bundle,
            source_artifact=source_artifact,
        ),
        privkey=privkey,
    )
    client_policy_bundle = build_autotrader_client_policy_bundle_from_user_rule_bundle(
        user_bundle,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )
    client_policy_bundle = sign_autotrader_client_policy_bundle(client_policy_bundle, privkey=privkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        client_policy_bundle=client_policy_bundle,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=policy_artifact,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.user_rule_summary is not None
    assert report.actionability_explanation is not None
    assert report.krr_explanation is not None
    assert report.krr_advice is not None
    assert report.user_rule_summary["preset_id"] == "conservative_dca"
    assert report.user_rule_summary["preset_profile"]["label"] == "Conservative DCA"
    assert report.user_rule_summary["preset_profile"]["optimize_for"] == "execution_safety"
    assert report.actionability_explanation["authoring"]["preset_id"] == "conservative_dca"
    assert report.actionability_explanation["authoring"]["preset_profile"]["label"] == "Conservative DCA"
    assert report.actionability_summary is not None
    assert report.actionability_summary["preset_summary"].startswith("Conservative DCA: Accumulate slowly")
    assert report.krr_explanation["authoring_posture"]["source_preset_id"] == "conservative_dca"
    assert report.krr_explanation["authoring_posture"]["preset_profile"]["summary"].startswith("Accumulate slowly")
    assert report.krr_advice["authoring_summary"]["source_preset_id"] == "conservative_dca"
    assert "source_preset_id=conservative_dca" in report.krr_advice["semantic_signature"]


def test_prepare_autotrader_live_accepts_supplied_client_policy_bundle() -> None:
    privkey = 805
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    client_policy_bundle = _client_policy_bundle(strategy, privkey=privkey)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        client_policy_bundle=client_policy_bundle,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.client_policy_bundle == client_policy_bundle
    assert report.client_policy_bundle_ok is True
    assert report.client_policy_bundle_signature_ok is True


def test_prepare_autotrader_live_rejects_invalid_client_policy_bundle_signature() -> None:
    privkey = 806
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    client_policy_bundle = _client_policy_bundle(strategy, privkey=privkey)
    tampered_bundle = replace(client_policy_bundle, signature="0x00")

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        client_policy_bundle=tampered_bundle,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "client_policy_bundle_signature_invalid"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "client_policy_bundle_signature_invalid"
    assert report.client_policy_bundle == tampered_bundle
    assert report.client_policy_bundle_ok is False
    assert report.client_policy_bundle_error == "client_policy_bundle_signature_invalid"
    assert report.client_policy_bundle_signature_ok is False


def test_prepare_autotrader_live_rejects_missing_client_policy_bundle_signature() -> None:
    privkey = 8061
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    client_policy_bundle = replace(
        _client_policy_bundle(strategy, privkey=privkey),
        signature=None,
        signer_pubkey=None,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        client_policy_bundle=client_policy_bundle,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "client_policy_bundle_signature_missing"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "client_policy_bundle_signature_missing"
    assert report.client_policy_bundle == client_policy_bundle
    assert report.client_policy_bundle_ok is False
    assert report.client_policy_bundle_error == "client_policy_bundle_signature_missing"
    assert report.client_policy_bundle_signature_ok is False


def test_prepare_autotrader_live_rejects_client_policy_bundle_strategy_mismatch() -> None:
    privkey = 807
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    mismatched_strategy = _compiled_strategy(owner_pubkey=owner_pubkey, fixed_order_size=101)
    pools, receipt = _single_hop_receipt()
    client_policy_bundle = _client_policy_bundle(mismatched_strategy, privkey=privkey)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        client_policy_bundle=client_policy_bundle,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "client_policy_bundle_strategy_hash_mismatch"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "client_policy_bundle_strategy_hash_mismatch"
    assert report.client_policy_bundle == client_policy_bundle
    assert report.client_policy_bundle_ok is False
    assert report.client_policy_bundle_error == "client_policy_bundle_strategy_hash_mismatch"
    assert report.client_policy_bundle_signature_ok is None


@pytest.mark.parametrize(
    ("bundle_kwargs", "expected_reason"),
    (
        ({"source_artifact_hash": "0xdeadbeef"}, "client_policy_bundle_source_artifact_hash_mismatch"),
        ({"tau_policy_bundle_hash": "0xdeadbeef"}, "client_policy_bundle_tau_policy_bundle_hash_mismatch"),
        ({"policy_artifact_hash": "0xdeadbeef"}, "client_policy_bundle_policy_artifact_hash_mismatch"),
    ),
)
def test_prepare_autotrader_live_rejects_client_policy_bundle_artifact_hash_mismatches(
    bundle_kwargs: dict[str, str],
    expected_reason: str,
) -> None:
    privkey = 808
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    client_policy_bundle = _pinned_client_policy_bundle(
        strategy,
        privkey=privkey,
        **bundle_kwargs,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        client_policy_bundle=client_policy_bundle,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == expected_reason
    assert report.live_admission_ok is False
    assert report.live_admission_error == expected_reason
    assert report.client_policy_bundle == client_policy_bundle
    assert report.client_policy_bundle_ok is False
    assert report.client_policy_bundle_error == expected_reason
    assert report.client_policy_bundle_signature_ok is True


def test_prepare_autotrader_live_rejects_invalid_policy_artifact() -> None:
    privkey = 81
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=autotrader_live.build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    unsigned_artifact = autotrader_live.build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_policy_bundle=bundle,
        policy_artifact=unsigned_artifact,
    )

    assert report.decision.reason == "policy_artifact_rejected:signature_missing"
    assert report.policy_artifact_ok is False


def test_prepare_autotrader_live_rejects_on_candidate_set_contract_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live,
        "check_strategy_candidate_set_contract",
        lambda candidate_set: SimpleNamespace(ok=False, error="candidate_shape_invalid"),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.reason == "candidate_set_rejected:candidate_shape_invalid"
    assert report.live_admission_ok is False


def test_prepare_autotrader_live_rejects_when_decision_prefers_noop(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 83
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live,
        "build_strategy_decision_certificate",
        lambda **kwargs: autotrader_live.StrategyDecisionCertificate(
            policy_artifact_hash=kwargs["candidate_set"].policy_artifact_hash,
            tau_policy_bundle_hash=kwargs["candidate_set"].tau_policy_bundle_hash,
            observation_hash=kwargs["candidate_set"].observation_hash,
            candidate_set_hash=kwargs["candidate_set"].candidate_set_hash_hex(),
            decision_model_version="autotrader-binary-v1",
            winner_index=0,
            winner_kind=DecisionCandidateKind.NO_OP,
            winner_key=0,
            argmax_steps=(
                {"winner_index": 0, "winner_key": 0, "cand_index": 0, "cand_key": 0, "binding_ok": 1},
                {"winner_index": 0, "winner_key": 0, "cand_index": 1, "cand_key": 1, "binding_ok": 1},
            ),
            kill_switch_active=False,
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.live_admission_error == "decision_certificate_rejected:winner_index mismatch"
    assert report.live_admission_ok is False


def test_prepare_autotrader_live_rejects_when_decision_prefers_emit(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 830
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live,
        "build_strategy_decision_certificate",
        lambda **kwargs: autotrader_live.StrategyDecisionCertificate(
            policy_artifact_hash=kwargs["candidate_set"].policy_artifact_hash,
            tau_policy_bundle_hash=kwargs["candidate_set"].tau_policy_bundle_hash,
            observation_hash=kwargs["candidate_set"].observation_hash,
            candidate_set_hash=kwargs["candidate_set"].candidate_set_hash_hex(),
            decision_model_version="autotrader-binary-v1",
            winner_index=1,
            winner_kind=DecisionCandidateKind.EMIT_COMPILED_INTENT,
            winner_key=1,
            argmax_steps=(
                {"winner_index": 1, "winner_key": 1, "cand_index": 0, "cand_key": 0, "binding_ok": 1},
                {"winner_index": 1, "winner_key": 1, "cand_index": 1, "cand_key": 1, "binding_ok": 1},
            ),
            kill_switch_active=False,
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(last_action_epoch=5),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.tag is not AutoTraderDecisionTag.SUBMIT
    assert report.live_admission_error == "decision_certificate_rejected:winner_index mismatch"
    assert report.live_admission_ok is False


def test_prepare_autotrader_live_rejects_when_decision_certificate_binding_breaks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 831
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live,
        "build_strategy_decision_certificate",
        lambda **kwargs: autotrader_live.StrategyDecisionCertificate(
            policy_artifact_hash="artifact.hash",
            tau_policy_bundle_hash="bundle.hash",
            observation_hash="obs.hash",
            candidate_set_hash="wrong.hash",
            decision_model_version="autotrader-binary-v1",
            winner_index=1,
            winner_kind=DecisionCandidateKind.EMIT_COMPILED_INTENT,
            winner_key=1,
            argmax_steps=(
                {"winner_index": 1, "winner_key": 1, "cand_index": 0, "cand_key": 0, "binding_ok": 1},
                {"winner_index": 1, "winner_key": 1, "cand_index": 1, "cand_key": 1, "binding_ok": 1},
            ),
            kill_switch_active=False,
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.live_admission_error == "decision_certificate_rejected:policy_artifact_hash mismatch"
    assert report.live_admission_ok is False


def test_prepare_autotrader_live_rejects_on_nonce_validation_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 84
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live,
        "validate_and_apply_intent_nonce_batch",
        lambda **kwargs: (False, "nonce_gap", None),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.reason == "live_nonce_validation_failed:nonce_gap"
    assert report.live_admission_ok is False


def test_prepare_autotrader_live_rejects_on_system_compose_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 85
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live,
        "check_strategy_system_compose",
        lambda **kwargs: SimpleNamespace(ok=False, error="compose_bad"),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.reason == "system_compose_rejected:compose_bad"
    assert report.live_admission_ok is False


def test_prepare_autotrader_live_rejects_wallet_capability_violation() -> None:
    privkey = 81
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    wallet_capability = AutoTraderWalletCapability(
        session_id="session.low",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        valid_from_epoch=1,
        valid_until_epoch=100,
        notional_remaining=50,
        allowed_assets=("A", "B"),
        allowed_actions=(autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,),
        enabled=True,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        wallet_capability=wallet_capability,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "wallet_capability_notional_exceeded:100>50"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "wallet_capability_notional_exceeded:100>50"
    assert report.system_compose_ok is None
    assert report.system_compose_error is None
    assert report.wallet_capability is not None
    assert report.wallet_capability.notional_remaining == 50


def test_prepare_autotrader_live_rejects_session_capability_binding_violation() -> None:
    privkey = 181
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    wallet_capability = AutoTraderWalletCapability(
        session_id="session.wide",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        valid_from_epoch=1,
        valid_until_epoch=100,
        notional_remaining=500,
        allowed_assets=("A", "B", "C"),
        allowed_actions=(autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,),
        enabled=True,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        wallet_capability=wallet_capability,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "session_capability_asset_scope_exceeds_strategy"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "session_capability_asset_scope_exceeds_strategy"
    assert report.session_capability_tau_receipt is None
    assert report.wallet_capability_tau_receipt is None


def test_prepare_autotrader_live_rejects_revoked_session_state() -> None:
    privkey = 281
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    session_state = AutoTraderSessionState(
        session_id="session.revoked",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        enabled=True,
        revoked_at_epoch=5,
    )
    wallet_capability = AutoTraderWalletCapability(
        session_id="session.revoked",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        valid_from_epoch=1,
        valid_until_epoch=100,
        notional_remaining=500,
        allowed_assets=("A", "B"),
        allowed_actions=(autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,),
        enabled=True,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        wallet_capability=wallet_capability,
        session_state=session_state,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "session_state_revoked:5>=5"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "session_state_revoked:5>=5"
    assert report.session_state is not None
    assert report.session_state.session_id == "session.revoked"
    assert report.session_state_tau_receipt is None
    assert report.signed_intents == ()


def test_prepare_autotrader_live_rejects_signer_mismatch() -> None:
    strategy = _compiled_strategy(owner_pubkey="0x" + bls_pubkey_hex_from_privkey(9))
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=10,
        last_used_nonce=0,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "signer_pubkey_mismatch"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "signer_pubkey_mismatch"
    assert report.system_compose_ok is False
    assert report.system_compose_error == "signer_binding_rejected"
    assert report.krr_advice is None
    assert report.signed_intents == ()
    assert report.operations == {}


def test_prepare_autotrader_live_degrades_when_krr_advice_raises(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 10
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    def _boom(**_: object) -> dict[str, object] | None:
        raise RuntimeError("krr unavailable")

    monkeypatch.setattr(autotrader_live, "advise_autotrader_krr", _boom)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.krr_advice is None
    assert report.krr_advice_error == "RuntimeError:krr unavailable"
    assert report.krr_explanation is None


def test_prepare_autotrader_live_returns_skip_without_signing() -> None:
    privkey = 11
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt(quote_epoch=1)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=3,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SKIP
    assert report.local_guard_evaluation is not None
    assert report.local_guard_evaluation.ok is False
    assert report.local_guard_evaluation.blocking_families == ("oracle_freshness",)
    assert report.local_guard_evaluation.first_blocking_reason == "quote_receipt_stale:age=4,max=3"
    assert report.actionability_explanation is not None
    assert report.actionability_explanation["actionability"]["actionable"] is False
    assert report.actionability_explanation["actionability"]["blocking_layer"] == "local_guards"
    assert report.actionability_explanation["actionability"]["blocking_reasons"][0] == "quote_receipt_stale:age=4,max=3"
    assert report.actionability_explanation["guard_posture"]["blocking_families"] == ["oracle_freshness"]
    assert report.actionability_summary is not None
    assert report.actionability_summary["headline"] == "Blocked by local guards: quote_receipt_stale:age=4,max=3."
    assert report.actionability_summary["blocking_summary"] == "Blocked by local guards: quote_receipt_stale:age=4,max=3."
    assert report.live_admission_ok is False
    assert report.live_admission_error == report.decision.reason
    assert report.system_compose_ok is True
    assert report.system_compose_error is None
    assert report.last_used_nonce_after == 3
    assert report.signed_intents == ()
    assert report.nonce_tau_receipts == ()


def test_prepare_autotrader_live_rejects_missing_template_asset_params() -> None:
    privkey = 111
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    object.__setattr__(strategy, "template_params", {"fixed_order_size": 100, "asset_in": "A"})
    pools, receipt = _single_hop_receipt()

    with pytest.raises(ValueError, match="strategy template params must define asset_in and asset_out"):
        prepare_autotrader_live_quote_receipt(
            strategy=strategy,
            controller_state=AutoTraderControllerState(),
            receipt=receipt,
            pools_by_id=pools,
            current_epoch=5,
            intent_deadline=99,
            signer_privkey=privkey,
            last_used_nonce=0,
        )


def test_prepare_autotrader_live_rejects_invalid_nonce_batch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 12
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    bad_intent = create_swap_intent(
        pool_id="p_ab",
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=50,
        deadline=99,
        sender_pubkey=owner_pubkey,
    )
    decision = autotrader_live.AutoTraderDecision(
        tag=AutoTraderDecisionTag.SUBMIT,
        reason="policy_guard_passed",
        explain=("ok",),
        state=AutoTraderControllerState(),
        intents=(bad_intent,),
    )
    monkeypatch.setattr(autotrader_live, "evaluate_autotrader_quote_receipt", lambda **kwargs: decision)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt={"body": {}},
        pools_by_id={},
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason.startswith("observation_packet_build_failed:TypeError:")
    assert report.live_admission_ok is False
    assert report.live_admission_error is not None
    assert report.live_admission_error.startswith("observation_packet_build_failed:TypeError:")
    assert report.system_compose_ok is False
    assert report.system_compose_error == "observation_packet_rejected"


def test_prepare_autotrader_live_rejects_unavailable_tau_nonce_tool(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 13
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (False, None, "missing tau"),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tau_tool_unavailable:missing tau"
    assert report.live_admission_ok is False
    assert report.system_compose_ok is None
    assert report.system_compose_error is None
    assert len(report.nonce_tau_receipts) == 1


def test_prepare_autotrader_live_rejects_unavailable_tau_wallet_tool(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 113
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (False, None, "missing tau wallet guard"),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tau_tool_unavailable:missing tau wallet guard"
    assert report.wallet_capability is not None
    assert report.system_compose_ok is None
    assert report.system_compose_error is None
    assert report.last_used_nonce_after == 0


def test_prepare_autotrader_live_rejects_tau_nonce_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 14
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live,
        "_verify_nonce_tau_receipt",
        lambda **kwargs: "nonce_tau_mismatch:intent_id=bad,local=1,tau=0",
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "nonce_tau_mismatch:intent_id=bad,local=1,tau=0"
    assert report.live_admission_ok is False
    assert report.system_compose_ok is False
    assert report.system_compose_error == "nonce_rejected"


def test_prepare_autotrader_live_system_compose_rejects_post_compile_invalid_strategy() -> None:
    privkey = 44
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    object.__setattr__(strategy, "strategy_id", "")
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tau_policy_bundle_rejected:compile_contract_tau_receipt_invalid"
    assert report.live_admission_ok is None
    assert report.live_admission_error is None
    assert report.system_compose_ok is None
    assert report.system_compose_error is None
    assert report.tau_policy_bundle_ok is False
    assert report.tau_policy_bundle_error == "compile_contract_tau_receipt_invalid"


def test_prepare_autotrader_live_rejects_unpaired_tx_arguments() -> None:
    strategy = _compiled_strategy(owner_pubkey="0x" + bls_pubkey_hex_from_privkey(15))
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=15,
        last_used_nonce=0,
        tx_sequence_number=1,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "live_admission_bundle_rejected:tx_envelope_rejected"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "tx_envelope_rejected"
    assert report.system_compose_ok is False
    assert report.system_compose_error == "tx_envelope_rejected"
    assert report.tx_envelope_tau_receipt is None


def test_prepare_autotrader_live_rejects_submit_bundle_tx_payload_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    strategy = _compiled_strategy(owner_pubkey="0x" + bls_pubkey_hex_from_privkey(115))
    pools, receipt = _single_hop_receipt()
    original_builder = autotrader_live.build_signed_tau_transaction

    def _bad_tau_tx(**kwargs: object) -> dict[str, object]:
        payload = original_builder(**kwargs)
        payload["operations"] = {"2": "bad"}
        return payload

    monkeypatch.setattr(autotrader_live, "build_signed_tau_transaction", _bad_tau_tx)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=115,
        last_used_nonce=0,
        tx_sequence_number=7,
        tx_expiration_time=700,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "submit_bundle_rejected:submit_bundle_tx_payload_rejected"
    assert report.live_admission_ok is False
    assert report.submit_bundle_ok is False
    assert report.submit_bundle_error == "submit_bundle_tx_payload_rejected"
    assert report.emit_finalize_ok is None


def test_prepare_autotrader_live_rejects_submit_bundle_tau_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 189
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(autotrader_live, "_verify_tx_envelope_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(
        autotrader_live,
        "_verify_boolean_tau_receipt",
        lambda **kwargs: (
            "submit_bundle_tau_mismatch:local=1,tau=0"
            if kwargs["error_prefix"] == "submit_bundle_tau"
            else None
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tx_sequence_number=9,
        tx_expiration_time=999,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "submit_bundle_tau_mismatch:local=1,tau=0"
    assert report.submit_bundle_ok is False
    assert report.submit_bundle_error == "submit_bundle_tau_rejected"
    assert report.submit_bundle_tau_receipt is not None
    assert report.emit_finalize_ok is None


def test_prepare_autotrader_live_rejects_emit_finalize_tau_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 190
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(autotrader_live, "_verify_tx_envelope_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(
        autotrader_live,
        "_verify_boolean_tau_receipt",
        lambda **kwargs: (
            "emit_finalize_tau_mismatch:local=1,tau=0"
            if kwargs["error_prefix"] == "emit_finalize_tau"
            else None
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tx_sequence_number=9,
        tx_expiration_time=999,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "emit_finalize_tau_mismatch:local=1,tau=0"
    assert report.emit_finalize_ok is False
    assert report.emit_finalize_error == "emit_finalize_tau_rejected"
    assert report.emit_finalize_tau_receipt is not None
    assert report.submit_bundle_ok is True


def test_prepare_autotrader_live_rejects_emit_finalize_guard_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 191
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live,
        "check_strategy_emit_finalize",
        lambda **kwargs: SimpleNamespace(
            ok=False,
            emit_requested=True,
            system_compose_ok=True,
            submit_bundle_ok=True,
            error="emit_finalize_guard_failed",
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "emit_finalize_rejected:emit_finalize_guard_failed"
    assert report.emit_finalize_ok is False
    assert report.emit_finalize_error == "emit_finalize_guard_failed"


def test_autotrader_live_require_u32_and_nonce_tau_helper_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    with pytest.raises(TypeError):
        autotrader_live._require_u32("nonce", "bad")
    with pytest.raises(ValueError):
        autotrader_live._require_u32("nonce", -1)

    receipt = autotrader_live.AutoTraderNonceTauReceipt(
        spec_id="autotrader_nonce_guard_v1",
        gate_output="o4",
        intent_id="iid.1",
        intent_nonce=1,
        last_used_nonce=0,
        expected_nonce=1,
        steps=({"i1": 1, "i2": 0, "i3": 1},),
        expected_ok=True,
    )

    monkeypatch.setattr(
        autotrader_live,
        "run_tau_spec_steps",
        lambda **kwargs: (_ for _ in ()).throw(RuntimeError("tau boom")),
    )
    assert (
        autotrader_live._verify_nonce_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "nonce_tau_runner_error:RuntimeError:tau boom"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {}})
    assert (
        autotrader_live._verify_nonce_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "nonce_tau_missing_output:o4"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 0}})
    assert (
        autotrader_live._verify_nonce_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "nonce_tau_mismatch:intent_id=iid.1,local=1,tau=0"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 1}})
    assert (
        autotrader_live._verify_nonce_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        is None
    )

    tx_receipt = autotrader_live.TauPolicyReceipt(
        strategy_id="strat.live.1",
        strategy_hash="0x1234",
        spec_id="autotrader_tx_envelope_guard_v1",
        gate_output="o4",
        steps=({"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1},),
        expected_ok=True,
    )

    monkeypatch.setattr(
        autotrader_live,
        "run_tau_spec_steps",
        lambda **kwargs: (_ for _ in ()).throw(RuntimeError("tau envelope boom")),
    )
    assert (
        autotrader_live._verify_tx_envelope_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=tx_receipt,
        )
        == "tx_envelope_tau_runner_error:RuntimeError:tau envelope boom"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {}})
    assert (
        autotrader_live._verify_tx_envelope_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=tx_receipt,
        )
        == "tx_envelope_tau_missing_output:o4"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 0}})
    assert (
        autotrader_live._verify_tx_envelope_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=tx_receipt,
        )
        == "tx_envelope_tau_mismatch:local=1,tau=0"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o4": 1}})
    assert (
        autotrader_live._verify_tx_envelope_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=tx_receipt,
        )
        is None
    )


def test_prepare_autotrader_live_rejects_wallet_capability_tau_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 82
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    verify_calls = {"count": 0}

    def _verify_tau_policy_receipt(**kwargs: object) -> str | None:
        verify_calls["count"] += 1
        if verify_calls["count"] < 3:
            return None
        return "tau_policy_mismatch:local=1,tau=0,expected=1"

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        _verify_tau_policy_receipt,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tau_policy_mismatch:local=1,tau=0,expected=1"
    assert report.live_admission_ok is False
    assert report.session_capability_tau_receipt is not None
    assert report.session_state_tau_receipt is not None
    assert report.wallet_capability_tau_receipt is not None
    assert report.signed_intents == ()
    assert verify_calls["count"] == 3


def test_prepare_autotrader_live_rejects_session_capability_tau_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 183
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        lambda **kwargs: "tau_policy_mismatch:local=1,tau=0,expected=1",
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tau_policy_mismatch:local=1,tau=0,expected=1"
    assert report.live_admission_ok is False
    assert report.session_capability_tau_receipt is not None
    assert report.wallet_capability_tau_receipt is None
    assert report.signed_intents == ()


def test_prepare_autotrader_live_rejects_session_state_tau_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 283
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    verify_calls = {"count": 0}

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )

    def _verify_tau_policy_receipt(**kwargs: object) -> str | None:
        verify_calls["count"] += 1
        if verify_calls["count"] == 2:
            return "tau_policy_mismatch:local=1,tau=0,expected=1"
        return None

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        _verify_tau_policy_receipt,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tau_policy_mismatch:local=1,tau=0,expected=1"
    assert report.live_admission_ok is False
    assert report.session_capability_tau_receipt is not None
    assert report.session_state_tau_receipt is not None
    assert report.wallet_capability_tau_receipt is None
    assert report.signed_intents == ()
    assert verify_calls["count"] == 2


def test_prepare_autotrader_live_rejects_tx_envelope_tau_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 184
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live,
        "_verify_tx_envelope_tau_receipt",
        lambda **kwargs: "tx_envelope_tau_mismatch:local=1,tau=0",
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
        tx_sequence_number=1,
        tx_expiration_time=99,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tx_envelope_tau_mismatch:local=1,tau=0"
    assert report.live_admission_ok is False
    assert report.system_compose_ok is False
    assert report.system_compose_error == "tx_envelope_rejected"
    assert report.tx_envelope_tau_receipt is not None


def test_prepare_autotrader_live_accepts_tau_tx_envelope_check(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 185
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(autotrader_live, "_verify_tx_envelope_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(autotrader_live, "_verify_boolean_tau_receipt", lambda **kwargs: None)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
        tx_sequence_number=5,
        tx_expiration_time=99,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.live_admission_ok is True
    assert report.system_compose_ok is True
    assert report.tx_envelope_tau_receipt is not None


def test_verify_boolean_tau_receipt_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    receipt = autotrader_live.TauPolicyReceipt(
        strategy_id="strat.live.1",
        strategy_hash="0x5678",
        spec_id="autotrader_system_compose_v1",
        gate_output="o3",
        steps=({"i1": 1},),
        expected_ok=True,
    )

    monkeypatch.setattr(
        autotrader_live,
        "run_tau_spec_steps",
        lambda **kwargs: (_ for _ in ()).throw(RuntimeError("tau compose boom")),
    )
    assert (
        autotrader_live._verify_boolean_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
            spec_path="spec.tau",
            error_prefix="system_compose_tau",
        )
        == "system_compose_tau_runner_error:RuntimeError:tau compose boom"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {}})
    assert (
        autotrader_live._verify_boolean_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
            spec_path="spec.tau",
            error_prefix="system_compose_tau",
        )
        == "system_compose_tau_missing_output:o3"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o3": 0}})
    assert (
        autotrader_live._verify_boolean_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
            spec_path="spec.tau",
            error_prefix="system_compose_tau",
        )
        == "system_compose_tau_mismatch:local=1,tau=0"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o3": 1}})
    assert (
        autotrader_live._verify_boolean_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
            spec_path="spec.tau",
            error_prefix="system_compose_tau",
        )
        is None
    )


def test_autotrader_live_source_registry_helper_type_guards() -> None:
    with pytest.raises(TypeError, match="packet must be an AutoTraderObservationPacket"):
        autotrader_live._observation_source_registry_ok(object())
    with pytest.raises(TypeError, match="signal must be an ExternalSignalObservation"):
        autotrader_live._trusted_external_signal_requires_registry(object())
    with pytest.raises(TypeError, match="signal must be an ExternalSignalObservation"):
        autotrader_live._registry_guard_relevant(object(), None)
    assert (
        autotrader_live._trusted_external_signal_requires_registry(
            ExternalSignalObservation(
                signal_id="sig.oracle.1",
                source_id="oracle.alpha",
                source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
                trust_tier=SignalTrustTier.VERIFIED,
                auth_ok=True,
                freshness_ok=True,
                advisory_only=False,
            )
        )
        is True
    )
    assert (
        autotrader_live._trusted_external_signal_requires_registry(
            ExternalSignalObservation(
                signal_id="sig.news.1",
                source_id="news.alpha",
                source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                trust_tier=SignalTrustTier.ADVISORY,
                auth_ok=True,
                freshness_ok=True,
                advisory_only=True,
            )
        )
        is False
    )
    with pytest.raises(TypeError, match="registry must be an ExternalSignalSourceRegistry or None"):
        autotrader_live._registry_guard_relevant(
            ExternalSignalObservation(
                signal_id="sig.news.1",
                source_id="news.alpha",
                source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                trust_tier=SignalTrustTier.ADVISORY,
                auth_ok=True,
                freshness_ok=True,
                advisory_only=True,
            ),
            object(),
        )


def test_build_external_signal_source_registry_tau_receipts_skips_irrelevant_advisory_signal() -> None:
    strategy = _compiled_strategy(owner_pubkey="0xowner", backend="tau")
    signal = ExternalSignalObservation(
        signal_id="sig.news.1",
        source_id="news.alpha",
        source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
        trust_tier=SignalTrustTier.ADVISORY,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=True,
    )
    receipts = autotrader_live._build_external_signal_source_registry_tau_receipts(
        strategy=strategy,
        external_signals=(signal,),
        signal_source_registry=None,
    )
    assert receipts == ()


def test_verify_external_signal_source_registry_tau_receipt_branches(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    receipt = autotrader_live.AutoTraderExternalSignalSourceRegistryTauReceipt(
        spec_id="autotrader_external_signal_source_registry_guard_v1",
        gate_output="o8",
        signal_id="sig.oracle.1",
        source_id="oracle.alpha",
        steps=({"i1": 1},),
        expected_ok=True,
    )

    def _boom(**kwargs: object) -> None:
        raise RuntimeError("boom")

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", _boom)
    assert (
        autotrader_live._verify_external_signal_source_registry_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "external_signal_source_registry_tau_runner_error:"
        "signal_id=sig.oracle.1,source_id=oracle.alpha,RuntimeError:boom"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {}})
    assert (
        autotrader_live._verify_external_signal_source_registry_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "external_signal_source_registry_tau_missing_output:"
        "signal_id=sig.oracle.1,source_id=oracle.alpha,o8"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o8": 0}})
    assert (
        autotrader_live._verify_external_signal_source_registry_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        == "external_signal_source_registry_tau_mismatch:"
        "signal_id=sig.oracle.1,source_id=oracle.alpha,local=1,tau=0"
    )

    monkeypatch.setattr(autotrader_live, "run_tau_spec_steps", lambda **kwargs: {0: {"o8": 1}})
    assert (
        autotrader_live._verify_external_signal_source_registry_tau_receipt(
            tau_bin=sys.executable,
            config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
            receipt=receipt,
        )
        is None
    )


def test_prepare_autotrader_live_accepts_external_signal_source_registry_tau_receipts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 286
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
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

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        lambda **kwargs: None,
    )
    monkeypatch.setattr(
        autotrader_live,
        "_verify_external_signal_source_registry_tau_receipt",
        lambda **kwargs: None,
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(autotrader_live, "_verify_boolean_tau_receipt", lambda **kwargs: None)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        external_signals=(signal,),
        signal_source_registry=registry,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.external_signal_source_registry_tau_receipts
    assert report.external_signal_source_registry_tau_receipts[0].signal_id == "sig.oracle.1"
    assert report.external_signal_source_registry_tau_receipts[0].source_id == "oracle.alpha"


def test_prepare_autotrader_live_rejects_external_signal_source_registry_tau_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 287
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
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

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live,
        "_verify_external_signal_source_registry_tau_receipt",
        lambda **kwargs: (
            "external_signal_source_registry_tau_mismatch:"
            "signal_id=sig.oracle.1,source_id=oracle.alpha,local=1,tau=0"
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        external_signals=(signal,),
        signal_source_registry=registry,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.live_admission_ok is False
    assert report.external_signal_source_registry_tau_receipts
    assert report.live_admission_error == (
        "external_signal_source_registry_tau_mismatch:"
        "signal_id=sig.oracle.1,source_id=oracle.alpha,local=1,tau=0"
    )


def test_prepare_autotrader_live_fail_closes_source_registry_when_observation_packet_build_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 288
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    signal = ExternalSignalObservation(
        signal_id="sig.news.1",
        source_id="news.alpha",
        source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
        trust_tier=SignalTrustTier.ADVISORY,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=True,
    )

    def _boom(**kwargs: object) -> None:
        raise RuntimeError("packet boom")

    monkeypatch.setattr(autotrader_live, "build_autotrader_observation_packet", _boom)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        external_signals=(signal,),
    )

    assert report.source_registry_ok is False
    assert report.decision.reason == "observation_packet_build_failed:RuntimeError:packet boom"
    assert report.observation_packet is None
    assert report.observation_packet_error == "RuntimeError:packet boom"


def test_prepare_autotrader_live_rejects_live_admission_tau_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 186
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(
        autotrader_live,
        "_verify_boolean_tau_receipt",
        lambda **kwargs: "live_admission_tau_mismatch:local=1,tau=0"
        if kwargs["error_prefix"] == "live_admission_tau"
        else None,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "live_admission_tau_mismatch:local=1,tau=0"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "live_admission_tau_mismatch:local=1,tau=0"
    assert report.system_compose_ok is False
    assert report.system_compose_error == "live_admission_tau_rejected"
    assert report.live_admission_tau_receipt is not None
    assert report.system_compose_tau_receipt is None


def test_prepare_autotrader_live_rejects_system_compose_tau_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 187
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(
        autotrader_live,
        "_verify_boolean_tau_receipt",
        lambda **kwargs: (
            "system_compose_tau_mismatch:local=1,tau=0"
            if kwargs["error_prefix"] == "system_compose_tau"
            else None
        ),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "system_compose_tau_mismatch:local=1,tau=0"
    assert report.live_admission_ok is False
    assert report.live_admission_error == "system_compose_tau_mismatch:local=1,tau=0"
    assert report.system_compose_ok is False
    assert report.system_compose_error == "system_compose_tau_rejected"
    assert report.live_admission_tau_receipt is not None
    assert report.system_compose_tau_receipt is not None


def test_prepare_autotrader_live_accepts_tau_live_and_system_compose_checks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 188
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(autotrader_live, "_verify_boolean_tau_receipt", lambda **kwargs: None)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.live_admission_ok is True
    assert report.system_compose_ok is True
    assert report.live_admission_tau_receipt is not None
    assert report.system_compose_tau_receipt is not None


def test_prepare_autotrader_live_rejects_controller_guard_bundle_gap(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 83
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    intent = create_swap_intent(
        pool_id="p_ab",
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=50,
        deadline=99,
        sender_pubkey=owner_pubkey,
        nonce=1,
    )
    decision = autotrader_live.AutoTraderDecision(
        tag=AutoTraderDecisionTag.SUBMIT,
        reason="policy_guard_passed",
        explain=("ok",),
        state=AutoTraderControllerState(),
        guard_state=AutoTraderGuardState(),
        intents=(intent,),
    )
    monkeypatch.setattr(autotrader_live, "evaluate_autotrader_quote_receipt", lambda **kwargs: decision)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt={"body": {"kind": "exact_in", "asset_in": "A", "asset_out": "B", "amount_in": 100, "quote_epoch": 5}},
        pools_by_id={},
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason.startswith("observation_packet_build_failed:TypeError:")
    assert report.live_admission_ok is False
    assert report.live_admission_error is not None
    assert report.live_admission_error.startswith("observation_packet_build_failed:TypeError:")


# ---------------------------------------------------------------------------
# Golden characterization tests for ``prepare_autotrader_live_quote_receipt``.
#
# These pin the *entire receipt output* (the function's return value, including
# every proof/verifier metadata field, rounding, ordering and nested receipt) by
# hashing a deterministic serialization of ``dataclasses.asdict(report)``. The
# golden SHA-256 constants were captured against the UNMODIFIED source. Any
# behavioral drift in receipt construction flips a hash and fails the test.
#
# Live IO is stubbed at a thin, deterministic boundary by running with
# ``tau_config`` left at ``None`` (Tau binary disabled => no subprocess/network)
# while BLS signing is deterministic for fixed integer private keys. The submit
# path therefore exercises real signing without any external dependency.
#
# TEETH: a mutation to the receipt-construction path (e.g. adding/removing a
# field on the returned report, changing an error string, changing nonce
# accounting, or reordering kwargs that change a value) changes the serialized
# asdict and flips the corresponding golden hash below.
# ---------------------------------------------------------------------------
import dataclasses as _dc_golden
import hashlib as _hashlib_golden
import pprint as _pprint_golden


def _autotrader_live_receipt_fingerprint(report: object) -> str:
    """Deterministic byte-identical fingerprint of a full live report.

    ``pprint.pformat`` with ``sort_dicts=True`` renders nested dataclasses
    (via ``asdict``) and enums in a stable, reproducible order. Hashing the
    rendered text gives a compact golden that is sensitive to every field of
    the returned receipt.
    """

    serialized = _pprint_golden.pformat(
        _dc_golden.asdict(report), width=140, sort_dicts=True
    )
    return _hashlib_golden.sha256(serialized.encode("utf-8")).hexdigest()


def test_golden_prepare_autotrader_live_submit_receipt_is_byte_identical() -> None:
    privkey = 7
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        tx_sequence_number=9,
        tx_expiration_time=999,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "f4f500d2afe8e7b8060720b2db15dc1281b1194b38eb77aada892ece8f9f4412"
    )


def test_golden_prepare_autotrader_live_uniform_load_error_receipt() -> None:
    # Pins the homogeneous pre-reassignment load-error gates (the table-driven
    # block). ``receipt_load_error`` is one of the four identically-shaped gates.
    privkey = 7
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        receipt_load_error="io_boom",
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "receipt_file_load_rejected"
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "8c134959fedc849ad2a5cbd066f594b5d60a208073baeb9c4bd0311ada3424a5"
    )


def test_golden_prepare_autotrader_live_bespoke_load_error_receipt() -> None:
    # Pins a post-reassignment load-error gate carrying bespoke kwargs
    # (signal_source_registry / source_registry_ok / external_signals). This
    # gate reads the *rebuilt* effective wallet/session defaults, so it is
    # deliberately NOT folded into the uniform table.
    privkey = 7
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        signal_source_registry_load_error="reg_boom",
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "signal_source_registry_load_rejected"
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "19e4f91fed85f6958644331567812c6ca86a265eea0c815febb0e63551609cd3"
    )


def test_golden_prepare_autotrader_live_client_policy_bundle_mismatch_receipt() -> None:
    # Pins the client-policy-bundle binding path, including the closure-captured
    # client_policy_bundle_ok/error flags propagated onto the receipt.
    privkey = 807
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    mismatched_strategy = _compiled_strategy(owner_pubkey=owner_pubkey, fixed_order_size=101)
    pools, receipt = _single_hop_receipt()
    client_policy_bundle = _client_policy_bundle(mismatched_strategy, privkey=privkey)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        client_policy_bundle=client_policy_bundle,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "client_policy_bundle_strategy_hash_mismatch"
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "e0b9cc72d1c46a869586fbc38ae1c3f9c148bb201773542f32a11e6e76d33991"
    )


def test_golden_prepare_autotrader_live_skip_receipt_is_byte_identical() -> None:
    # Pins the SKIP (no-op) path: full presentation/actionability shaping but
    # no signing.
    privkey = 11
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt(quote_epoch=1)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=3,
    )

    assert report.decision.tag is AutoTraderDecisionTag.SKIP
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "0e9c0c98b7a87bb24af31ab3f7d950c6e722c30dd8f23341ad0ae90e5e02905a"
    )


# ---------------------------------------------------------------------------
# Architectural import-boundary invariant.
#
# Advisory/live code (the ``autotrader_*`` family, including this module's
# ``autotrader_live``) must remain OUTSIDE verifier/authority. Settlement and
# proof-verification modules form the consensus-critical authority surface;
# they must NOT import advisory/live modules, even transitively. A violation
# would let advisory presentation logic creep into the authority path.
#
# This uses pure static AST analysis (no in-process ``sys.modules`` state,
# which is polluted by the surrounding test suite) and follows first-party
# ``src.*`` imports transitively.
#
# TEETH: if any authority/verifier module gains an ``import`` of an
# ``autotrader_*`` module (directly or anywhere in its first-party transitive
# closure), the offending mapping becomes non-empty and this test fails.
# ---------------------------------------------------------------------------
def test_verifier_authority_modules_do_not_import_advisory_live() -> None:
    import ast
    import pathlib

    repo_root = pathlib.Path(__file__).resolve().parents[2]

    def _module_path(module_name: str) -> pathlib.Path | None:
        candidate = repo_root / (module_name.replace(".", "/") + ".py")
        if candidate.exists():
            return candidate
        pkg_init = repo_root / module_name.replace(".", "/") / "__init__.py"
        if pkg_init.exists():
            return pkg_init
        return None

    def _first_party_imports(path: pathlib.Path) -> set[str]:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        names: set[str] = set()

        def _add_module_and_children(resolved: str, node: ast.ImportFrom) -> None:
            # Record the parent module itself...
            names.add(resolved)
            # ...and, crucially, the alias-child form
            # ``from <pkg> import <child>`` (e.g.
            # ``from src.integration import autotrader_live``), which imports a
            # *submodule* by name. ``<resolved>.<child>`` is synthesised so the
            # transitive BFS can resolve and inspect that submodule. Non-module
            # names (e.g. ``from src.core.settlement import a_function``) simply
            # fail to resolve to a file later and are harmlessly ignored.
            for alias in node.names:
                if alias.name == "*":
                    continue
                names.add(f"{resolved}.{alias.name}")

        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                names.update(
                    alias.name for alias in node.names if alias.name.startswith("src.")
                )
            elif isinstance(node, ast.ImportFrom):
                if node.level and node.level > 0:
                    # Resolve a relative import to its absolute src.* form.
                    base_parts = path.relative_to(repo_root).with_suffix("").parts
                    anchor = list(base_parts[:-1])  # drop the module filename
                    for _ in range(node.level - 1):
                        if anchor:
                            anchor.pop()
                    suffix = node.module.split(".") if node.module else []
                    resolved = ".".join(anchor + suffix)
                    if resolved.startswith("src."):
                        _add_module_and_children(resolved, node)
                elif node.module and node.module.startswith("src."):
                    _add_module_and_children(node.module, node)
        return names

    authority_roots = (
        "src.core.settlement",
        "src.core.settlement_strong_validator",
        "src.core.settlement_normal_form",
        "src.core.settlement_admission",
        "src.integration.proof_verifier",
    )

    offending: dict[str, str] = {}
    for root in authority_roots:
        # Transitive BFS over first-party imports.
        seen: set[str] = set()
        frontier = [root]
        while frontier:
            current = frontier.pop()
            if current in seen:
                continue
            seen.add(current)
            if "autotrader" in current:
                offending[root] = current
                break
            path = _module_path(current)
            if path is None:
                continue
            for imported in _first_party_imports(path):
                if imported not in seen:
                    frontier.append(imported)

    assert not offending, (
        "authority/verifier modules must not import advisory/live "
        f"(autotrader_*) modules (transitively); found: {offending}"
    )

    # Synthetic-detection proof (TEETH): a verifier module that pulls in an
    # advisory module via the *alias-child* form
    # ``from src.integration import autotrader_live`` (parent package imported,
    # then ``autotrader_live.<attr>`` used) must be detected. Without the
    # alias-child handling above this slips past, because ``node.module`` is the
    # innocuous parent ``src.integration``. We run the real extractor against a
    # synthetic source and assert the advisory submodule is surfaced and would
    # be flagged by the same ``"autotrader" in <name>`` BFS check.
    import tempfile

    with tempfile.TemporaryDirectory() as synthetic_dir:
        synthetic_module = pathlib.Path(synthetic_dir) / "fake_verifier.py"
        synthetic_module.write_text(
            "from src.integration import autotrader_live\n"
            "import src.core.settlement\n",
            encoding="utf-8",
        )
        synthetic_imports = _first_party_imports(synthetic_module)

    # The alias-child advisory submodule is now surfaced by the extractor...
    assert "src.integration.autotrader_live" in synthetic_imports, (
        "import-boundary guard regressed: alias-child form "
        "'from src.integration import autotrader_live' is no longer detected"
    )
    # ...and the BFS flag predicate ('autotrader' substring) would reject it.
    synthetic_offenders = sorted(
        name for name in synthetic_imports if "autotrader" in name
    )
    assert synthetic_offenders == ["src.integration.autotrader_live"], (
        "expected exactly the advisory submodule to be flagged, "
        f"got {synthetic_offenders}"
    )


# ---------------------------------------------------------------------------
# Golden characterization tests for the Tau-verification surface of
# ``prepare_autotrader_live_quote_receipt`` (the riskiest, highest-complexity
# region). The Tau binary is stubbed at the same thin boundary the existing
# ``*_tau_mismatch`` tests use: ``_resolve_tau_bin`` returns a canned
# ``(True, sys.executable, None)`` and the per-receipt verifiers are replaced
# with deterministic stubs, so NO subprocess is launched.
#
# These goldens pin the full receipt for each Tau reject/success path through
# the first Tau block (PolicyBackend.TAU pre-checks) — in particular they lock
# the deliberately-asymmetric propagation of
# ``external_signal_source_registry_tau_receipts`` (carried on the registry-loop
# reject, dropped on the session/wallet capability mismatch rejects). The
# constants were captured against the source with the first Tau block UNMODIFIED.
# ---------------------------------------------------------------------------
def _tau_config_for_golden() -> AutoTraderTauConfig:
    return AutoTraderTauConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False)


def _verified_external_signal_and_registry() -> tuple[
    ExternalSignalObservation, ExternalSignalSourceRegistry
]:
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
    return signal, registry


def test_golden_tau_tool_unavailable_receipt(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 401
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (False, None, "no_tau"),
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=_tau_config_for_golden(),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "tau_tool_unavailable:no_tau"
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "de8492356cd1f75ca1b397b49faaacb33c30e92dfa837e5790c902ef2c9f7043"
    )


def test_golden_tau_session_capability_mismatch_receipt(monkeypatch: pytest.MonkeyPatch) -> None:
    # First sequential verify fails. Registry receipts are NOT carried onto this
    # reject (the pinned asymmetry).
    privkey = 183
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        lambda **kwargs: "tau_policy_mismatch:local=1,tau=0,expected=1",
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=_tau_config_for_golden(),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.external_signal_source_registry_tau_receipts == ()
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "0bbae1824d5f7417e9c1e4c5a0770efc3fac44123e1f60b50d642344a69e94a7"
    )


def test_golden_tau_session_capability_mismatch_drops_registry_receipts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Same session-capability mismatch but WITH a verified external signal +
    # registry, so the registry receipts are actually built (non-empty). The
    # current behavior DROPS them from this reject; this golden pins that exact
    # asymmetry. (A regression that propagates the receipts onto this reject —
    # the natural mistake when refactoring — flips this hash.)
    privkey = 187
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    signal, registry = _verified_external_signal_and_registry()
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live,
        "_verify_external_signal_source_registry_tau_receipt",
        lambda **kwargs: None,
    )
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        lambda **kwargs: "tau_policy_mismatch:local=1,tau=0,expected=1",
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        external_signals=(signal,),
        signal_source_registry=registry,
        tau_config=_tau_config_for_golden(),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    # Registry receipts were built (the registry-loop ran and passed) but are
    # deliberately NOT carried onto this capability-mismatch reject.
    assert report.external_signal_source_registry_tau_receipts == ()
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "3c8363755886e7ecc090731e0105293f5110363a7396711a761382fcb96ae861"
    )


def test_golden_tau_session_state_mismatch_receipt(monkeypatch: pytest.MonkeyPatch) -> None:
    # Second sequential verify fails (session_capability passes, session_state fails).
    privkey = 283
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    verify_calls = {"count": 0}

    def _verify(**kwargs: object) -> str | None:
        verify_calls["count"] += 1
        if verify_calls["count"] == 2:
            return "tau_policy_mismatch:local=1,tau=0,expected=1"
        return None

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        _verify,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=_tau_config_for_golden(),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert verify_calls["count"] == 2
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "7d88e948dab78fdf25ca8341780a9dfcc88c5e65692da5b05a4aeb909fc5dadb"
    )


def test_golden_tau_wallet_capability_mismatch_receipt(monkeypatch: pytest.MonkeyPatch) -> None:
    # Third sequential verify fails (session_capability + session_state pass).
    privkey = 184
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    verify_calls = {"count": 0}

    def _verify(**kwargs: object) -> str | None:
        verify_calls["count"] += 1
        if verify_calls["count"] == 3:
            return "tau_policy_mismatch:local=1,tau=0,expected=1"
        return None

    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        _verify,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        tau_config=_tau_config_for_golden(),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.wallet_capability_tau_receipt is not None
    assert verify_calls["count"] == 3
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "082fd6af76558cfcd80ee925ea3ff1d38329e8682001f56b85094df395a37c02"
    )


def test_golden_tau_registry_receipt_mismatch_receipt(monkeypatch: pytest.MonkeyPatch) -> None:
    # Registry-loop verify fails. Registry receipts ARE carried onto this reject
    # (the other side of the pinned asymmetry).
    privkey = 586
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    signal, registry = _verified_external_signal_and_registry()
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live,
        "_verify_external_signal_source_registry_tau_receipt",
        lambda **kwargs: "registry_tau_mismatch:x",
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        external_signals=(signal,),
        signal_source_registry=registry,
        tau_config=_tau_config_for_golden(),
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "registry_tau_mismatch:x"
    assert len(report.external_signal_source_registry_tau_receipts) == 1
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "241eb09dd6a9922f9a8bf4958befc7bed253d1fa232d95a128afd26bb8f282c8"
    )


def test_golden_tau_full_success_receipt(monkeypatch: pytest.MonkeyPatch) -> None:
    # All Tau verifiers pass: exercises the success path through the first Tau
    # block and the entire downstream Tau pipeline.
    privkey = 286
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey, backend="tau")
    pools, receipt = _single_hop_receipt()
    signal, registry = _verified_external_signal_and_registry()
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_resolve_tau_bin",
        lambda config: (True, sys.executable, None),
    )
    monkeypatch.setattr(
        autotrader_live.autotrader_controller,
        "_verify_tau_policy_receipt",
        lambda **kwargs: None,
    )
    monkeypatch.setattr(
        autotrader_live,
        "_verify_external_signal_source_registry_tau_receipt",
        lambda **kwargs: None,
    )
    monkeypatch.setattr(autotrader_live, "_verify_nonce_tau_receipt", lambda **kwargs: None)
    monkeypatch.setattr(autotrader_live, "_verify_boolean_tau_receipt", lambda **kwargs: None)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        external_signals=(signal,),
        signal_source_registry=registry,
        tau_config=_tau_config_for_golden(),
    )

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert len(report.external_signal_source_registry_tau_receipts) == 1
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "d26bae724e220762787a72aeeb9fda75d4256b2976919013b58b1da8d4d395bb"
    )


# ---------------------------------------------------------------------------
# Golden characterization tests for the three capability-result rejection gates
# (session_state / session_capability / wallet_capability). These are the
# sequential ``if not <X>_result.ok`` gates that follow the Tau pre-check; they
# share an identical ``finalize_report`` payload and differ only in error
# string, the gate-specific ``explain`` suffix and the carried tau receipt.
# Pinning all three lets them be table-driven safely.
# ---------------------------------------------------------------------------
def test_golden_wallet_capability_result_reject_receipt() -> None:
    privkey = 81
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    wallet_capability = AutoTraderWalletCapability(
        session_id="session.low",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        valid_from_epoch=1,
        valid_until_epoch=100,
        notional_remaining=50,
        allowed_assets=("A", "B"),
        allowed_actions=(autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,),
        enabled=True,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        wallet_capability=wallet_capability,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "wallet_capability_notional_exceeded:100>50"
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "e7727ebc98bf110cdcd9425c411c611448f9b41136ea618f4e88357d3a506b2b"
    )


def test_golden_session_capability_result_reject_receipt() -> None:
    privkey = 181
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    wallet_capability = AutoTraderWalletCapability(
        session_id="session.wide",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        valid_from_epoch=1,
        valid_until_epoch=100,
        notional_remaining=500,
        allowed_assets=("A", "B", "C"),
        allowed_actions=(autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,),
        enabled=True,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        wallet_capability=wallet_capability,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "session_capability_asset_scope_exceeds_strategy"
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "403e2f6d86e2aa62d87fd16555fcfdc0606e26621e3873b8766f09c402f121a2"
    )


def test_golden_session_state_result_reject_receipt() -> None:
    privkey = 281
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    session_state = AutoTraderSessionState(
        session_id="session.revoked",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        enabled=True,
        revoked_at_epoch=5,
    )
    wallet_capability = AutoTraderWalletCapability(
        session_id="session.revoked",
        owner_pubkey=owner_pubkey,
        chain_id="tau-net-alpha",
        valid_from_epoch=1,
        valid_until_epoch=100,
        notional_remaining=500,
        allowed_assets=("A", "B"),
        allowed_actions=(autotrader_live.StrategyAction.PLACE_SWAP_EXACT_IN,),
        enabled=True,
    )

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        wallet_capability=wallet_capability,
        session_state=session_state,
    )

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.decision.reason == "session_state_revoked:5>=5"
    assert (
        _autotrader_live_receipt_fingerprint(report)
        == "585cc0af000650fb6960be6036a27f51365eda3b0723113a75f4bf57ad64a0e8"
    )
