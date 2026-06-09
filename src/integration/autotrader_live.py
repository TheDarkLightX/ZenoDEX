"""Live-preparation runner for the policy-constrained auto-trader."""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Any, Mapping

from ..agents.autotrader_client_policy_bundle import (
    AutoTraderClientPolicyBundle,
    verify_autotrader_client_policy_bundle_signature,
)
from ..agents.autotrader_local_guard_evaluator import (
    AutoTraderLocalGuardEvaluation,
    AutoTraderLocalGuardInputs,
    evaluate_autotrader_local_guards,
)
from ..agents.autotrader_user_rule_bundle import (
    describe_autotrader_strategy_surface_support,
    describe_autotrader_user_rule_preset,
)
from ..agents.intent_signer import sign_intent
from ..agents.krr_policy_advisor import advise_autotrader_krr
from ..agents.policy_artifacts import (
    StrategyPolicyArtifact,
    TauPolicyBundle,
    build_strategy_policy_artifact,
    build_tau_policy_bundle,
    sign_strategy_policy_artifact,
)
from ..agents.strategy_ir import PolicyBackend, StrategyAction, StrategyIR, StrategyTemplate
from ..agents.tau_policy_adapter import (
    TauPolicyReceipt,
    build_compile_contract_tau_policy_receipt,
    build_external_signal_source_registry_guard_tau_policy_receipt,
    build_nonce_guard_tau_policy_receipt,
    build_session_capability_binding_guard_tau_policy_receipt,
    build_session_state_guard_tau_policy_receipt,
    build_wallet_capability_guard_tau_policy_receipt,
)
from ..kernels.python.strategy_candidate_set_contract_v1_adapter import (
    check_strategy_candidate_set_contract,
)
from ..kernels.python.strategy_compile_contract_v1_adapter import check_strategy_compile_contract
from ..kernels.python.strategy_decision_kernel_v1_adapter import check_strategy_decision_kernel
from ..kernels.python.strategy_emit_finalize_v1_adapter import check_strategy_emit_finalize
from ..kernels.python.strategy_kill_switch_guard_v1_adapter import check_strategy_kill_switch_guard
from ..kernels.python.strategy_live_admission_bundle_v1_adapter import (
    check_strategy_live_admission_bundle,
)
from ..kernels.python.strategy_multi_action_candidate_set_contract_v1_adapter import (
    check_strategy_multi_action_candidate_set_contract,
)
from ..kernels.python.strategy_nonce_guard_v1_adapter import check_strategy_nonce
from ..kernels.python.strategy_policy_artifact_contract_v1_adapter import (
    check_strategy_policy_artifact_contract,
)
from ..kernels.python.strategy_policy_bundle_contract_v1_adapter import (
    check_strategy_policy_bundle_contract,
)
from ..kernels.python.strategy_session_capability_binding_guard_v1_adapter import (
    check_strategy_session_capability_binding,
)
from ..kernels.python.strategy_session_state_guard_v1_adapter import check_strategy_session_state
from ..kernels.python.strategy_signer_binding_guard_v1_adapter import (
    check_strategy_signer_binding,
)
from ..kernels.python.strategy_submit_bundle_guard_v1_adapter import check_strategy_submit_bundle
from ..kernels.python.strategy_system_compose_v1_adapter import check_strategy_system_compose
from ..kernels.python.strategy_tx_envelope_guard_v1_adapter import check_strategy_tx_envelope
from ..kernels.python.strategy_wallet_capability_guard_v1_adapter import check_wallet_capability
from ..state.intents import Intent
from ..state.nonces import NonceTable, validate_and_apply_intent_nonce_batch
from ..state.pools import PoolState
from .autotrader_controller import (
    AutoTraderControllerState,
    AutoTraderDecision,
    AutoTraderDecisionTag,
    AutoTraderTauConfig,
    _reject,
    evaluate_autotrader_quote_receipt,
)
from .autotrader_decision import (
    StrategyCandidateSet,
    StrategyDecisionCertificate,
    build_strategy_candidate_set,
    build_strategy_decision_certificate,
    verify_strategy_decision_certificate,
)
from .autotrader_live_release_certificate import (
    AutoTraderLiveReleaseCertificate,
    build_autotrader_live_release_certificate,
)
from .autotrader_multiaction_decision import (
    BoundedMultiActionCandidateSet,
    BoundedMultiActionDecisionCertificate,
    BoundedMultiActionTauArgmaxContractResult,
    build_bounded_multi_action_candidate_set,
    build_bounded_multi_action_decision_certificate,
    check_bounded_multi_action_decision_tau_argmax_contract,
    verify_bounded_multi_action_decision_certificate,
)
from .autotrader_signal_registry import ExternalSignalSourceRegistry
from .autotrader_signals import (
    AutoTraderObservationPacket,
    AutoTraderSessionState,
    AutoTraderWalletCapability,
    ExternalSignalObservation,
    SignalSourceKind,
    SignalTrustTier,
    build_autotrader_observation_packet,
    build_quote_receipt_signal_packet,
    build_session_state_from_capability,
    build_wallet_capability_from_strategy,
)
from .autotrader_stage_certificate import (
    AutoTraderStageCertificate,
    build_autotrader_stage_certificate,
)
from .decision_witness import (
    DecisionWitness,
    build_decision_witness_from_autotrader_multiaction_decision,
    verify_decision_witness_against_autotrader_multiaction_decision,
)
from .operations import (
    SignedIntentEnvelope,
    create_intent_operation,
    create_signed_intent_operation,
)
from .tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from .tau_runner import run_tau_spec_steps
from .tau_witness import (
    AUTOTRADER_EMIT_FINALIZE_V1,
    AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1,
    AUTOTRADER_LIVE_ADMISSION_BUNDLE_V1,
    AUTOTRADER_NONCE_GUARD_V1,
    AUTOTRADER_SUBMIT_BUNDLE_GUARD_V1,
    AUTOTRADER_SYSTEM_COMPOSE_V1,
    AUTOTRADER_TX_ENVELOPE_GUARD_V1,
    build_autotrader_emit_finalize_v1_step,
    build_autotrader_live_admission_bundle_v1_step,
    build_autotrader_submit_bundle_guard_v1_step,
    build_autotrader_system_compose_v1_step,
    build_autotrader_tx_envelope_guard_v1_step,
)

_U32_MAX = 0xFFFFFFFF


@dataclass(frozen=True)
class AutoTraderNonceTauReceipt:
    spec_id: str
    gate_output: str
    intent_id: str
    intent_nonce: int
    last_used_nonce: int
    expected_nonce: int
    steps: tuple[dict[str, int], ...]
    expected_ok: bool = True


@dataclass(frozen=True)
class AutoTraderExternalSignalSourceRegistryTauReceipt:
    spec_id: str
    gate_output: str
    signal_id: str
    source_id: str
    steps: tuple[dict[str, int], ...]
    expected_ok: bool


@dataclass(frozen=True)
class AutoTraderLiveReport:
    decision: AutoTraderDecision
    signer_pubkey: str
    chain_id: str
    last_used_nonce_before: int
    last_used_nonce_after: int
    local_guard_evaluation: AutoTraderLocalGuardEvaluation | None = None
    client_policy_bundle: AutoTraderClientPolicyBundle | None = None
    client_policy_bundle_ok: bool | None = None
    client_policy_bundle_error: str | None = None
    client_policy_bundle_signature_ok: bool | None = None
    live_admission_ok: bool | None = None
    live_admission_error: str | None = None
    wallet_capability: AutoTraderWalletCapability | None = None
    policy_artifact: StrategyPolicyArtifact | None = None
    policy_artifact_ok: bool | None = None
    policy_artifact_error: str | None = None
    tau_policy_bundle: TauPolicyBundle | None = None
    tau_policy_bundle_ok: bool | None = None
    tau_policy_bundle_error: str | None = None
    observation_packet: AutoTraderObservationPacket | None = None
    observation_packet_error: str | None = None
    signal_source_registry: ExternalSignalSourceRegistry | None = None
    source_registry_ok: bool | None = None
    external_signals: tuple[ExternalSignalObservation, ...] = ()
    session_state: AutoTraderSessionState | None = None
    session_state_tau_receipt: TauPolicyReceipt | None = None
    session_capability_tau_receipt: TauPolicyReceipt | None = None
    wallet_capability_tau_receipt: TauPolicyReceipt | None = None
    external_signal_source_registry_tau_receipts: tuple[
        AutoTraderExternalSignalSourceRegistryTauReceipt, ...
    ] = ()
    system_compose_ok: bool | None = None
    system_compose_error: str | None = None
    candidate_set: StrategyCandidateSet | None = None
    candidate_set_ok: bool | None = None
    candidate_set_error: str | None = None
    decision_certificate: StrategyDecisionCertificate | None = None
    decision_ok: bool | None = None
    decision_error: str | None = None
    bounded_multiaction_candidate_set: BoundedMultiActionCandidateSet | None = None
    bounded_multiaction_candidate_set_contract: dict[str, Any] | None = None
    bounded_multiaction_decision_certificate: BoundedMultiActionDecisionCertificate | None = None
    bounded_multiaction_decision_witness: DecisionWitness | None = None
    bounded_multiaction_decision_contract: dict[str, Any] | None = None
    bounded_multiaction_decision_witness_contract: dict[str, Any] | None = None
    bounded_multiaction_tau_argmax_contract: dict[str, Any] | None = None
    kill_switch_ok: bool | None = None
    kill_switch_error: str | None = None
    krr_advice: dict[str, Any] | None = None
    krr_advice_error: str | None = None
    krr_explanation: dict[str, Any] | None = None
    user_rule_summary: dict[str, Any] | None = None
    actionability_explanation: dict[str, Any] | None = None
    actionability_summary: dict[str, Any] | None = None
    signed_intents: tuple[SignedIntentEnvelope, ...] = ()
    operations: dict[str, Any] = field(default_factory=dict)
    nonce_tau_receipts: tuple[AutoTraderNonceTauReceipt, ...] = ()
    tx_envelope_tau_receipt: TauPolicyReceipt | None = None
    live_admission_tau_receipt: TauPolicyReceipt | None = None
    system_compose_tau_receipt: TauPolicyReceipt | None = None
    submit_bundle_ok: bool | None = None
    submit_bundle_error: str | None = None
    submit_bundle_tau_receipt: TauPolicyReceipt | None = None
    emit_finalize_ok: bool | None = None
    emit_finalize_error: str | None = None
    emit_finalize_tau_receipt: TauPolicyReceipt | None = None
    tau_tx_payload: dict[str, Any] | None = None
    stage_certificate: AutoTraderStageCertificate | None = None
    stage_certificate_error: str | None = None
    live_release_certificate: AutoTraderLiveReleaseCertificate | None = None
    live_release_certificate_error: str | None = None


def _finalize_live_report(**kwargs: Any) -> AutoTraderLiveReport:
    report = _attach_actionability_summary(
        _attach_actionability_explanation(
            _attach_user_rule_summary(_attach_krr_explanation(AutoTraderLiveReport(**kwargs)))
        )
    )
    try:
        stage_certificate = build_autotrader_stage_certificate(report)
    except Exception as exc:
        report = replace(
            report,
            stage_certificate_error=f"{type(exc).__name__}:{exc}",
        )
    else:
        report = replace(
            report,
            stage_certificate=stage_certificate,
            stage_certificate_error=None,
        )
    try:
        certificate = build_autotrader_live_release_certificate(report)
    except ValueError:
        return report
    except Exception as exc:
        return replace(
            report,
            live_release_certificate_error=f"{type(exc).__name__}:{exc}",
        )
    return replace(
        report,
        live_release_certificate=certificate,
        live_release_certificate_error=None,
    )


def _attach_local_guard_evaluation(
    report: AutoTraderLiveReport,
    evaluation: AutoTraderLocalGuardEvaluation | None,
) -> AutoTraderLiveReport:
    if evaluation is None:
        return report
    return _attach_actionability_summary(
        _attach_actionability_explanation(
            replace(report, local_guard_evaluation=evaluation)
        )
    )


def _summarize_actionability_reason(reason: object) -> str | None:
    if not isinstance(reason, str):
        return None
    reason_text = reason.strip()
    if not reason_text:
        return None
    if reason_text == "policy_guard_passed":
        return "ok"
    return reason_text


def _safe_advise_autotrader_krr(**kwargs: Any) -> tuple[dict[str, Any] | None, str | None]:
    try:
        return advise_autotrader_krr(**kwargs), None
    except Exception as exc:
        return None, f"{type(exc).__name__}:{exc}"


def _build_krr_explanation(krr_advice: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if not isinstance(krr_advice, Mapping):
        return None

    authoring_raw = krr_advice.get("authoring_summary")
    observation_raw = krr_advice.get("observation_summary")
    route_raw = krr_advice.get("route_risk_summary")
    source_quality_raw = krr_advice.get("source_quality_summary")

    authoring = authoring_raw if isinstance(authoring_raw, Mapping) else {}
    observation = observation_raw if isinstance(observation_raw, Mapping) else {}
    route = route_raw if isinstance(route_raw, Mapping) else None

    low_reliability_sources: list[str] = []
    unseen_sources: list[str] = []
    registered_sources: list[str] = []
    if isinstance(source_quality_raw, list):
        for row in source_quality_raw:
            if not isinstance(row, Mapping):
                continue
            source_id = str(row.get("source_id", "")).strip()
            if not source_id:
                continue
            if bool(row.get("registered", False)):
                registered_sources.append(source_id)
            if bool(row.get("low_reliability", False)):
                low_reliability_sources.append(source_id)
            if bool(row.get("unseen_history", False)):
                unseen_sources.append(source_id)

    advisory_risk_flags_raw = krr_advice.get("advisory_risk_flags")
    advisory_risk_flags: list[str] = []
    if isinstance(advisory_risk_flags_raw, list):
        advisory_risk_flags = [str(flag) for flag in advisory_risk_flags_raw if str(flag).strip()]
    ranking_confidence = float(krr_advice.get("ranking_confidence", 0.0) or 0.0)
    effective_confidence = float(krr_advice.get("confidence", 0.0) or 0.0)
    confidence_cap = float(krr_advice.get("confidence_cap", 0.0) or 0.0)
    discounted = effective_confidence < ranking_confidence
    discount_reasons = list(advisory_risk_flags)
    if discounted:
        discount_reasons.append("confidence_capped")

    asset_in = authoring.get("asset_in")
    asset_out = authoring.get("asset_out")
    asset_pair = None
    if isinstance(asset_in, str) and isinstance(asset_out, str) and asset_in.strip() and asset_out.strip():
        asset_pair = f"{asset_in}/{asset_out}"

    extreme_flags: list[str] = []
    if route is not None:
        if bool(route.get("extreme_input_stress_present", False)):
            extreme_flags.append("extreme_input_stress")
        if bool(route.get("extreme_output_depletion_present", False)):
            extreme_flags.append("extreme_output_depletion")
        if bool(route.get("extreme_price_impact_present", False)):
            extreme_flags.append("extreme_price_impact")

    preset_profile = describe_autotrader_user_rule_preset(
        authoring.get("source_preset_id") if isinstance(authoring.get("source_preset_id"), str) else None
    )

    return {
        "authoring_posture": {
            "source_form": authoring.get("source_form"),
            "source_preset_id": authoring.get("source_preset_id"),
            "preset_profile": preset_profile,
            "authored_via_user_bundle": bool(authoring.get("authored_via_user_bundle", False)),
            "authoring_mode": str(authoring.get("authoring_mode", "unknown")),
            "fixed_order_size": authoring.get("fixed_order_size"),
            "cadence_epochs": authoring.get("cadence_epochs"),
            "trigger_price": authoring.get("trigger_price"),
            "asset_pair": asset_pair,
        },
        "trust_posture": {
            "primary_trust_tier": observation.get("primary_trust_tier"),
            "trusted_signal_count": int(observation.get("trusted_signal_count", 0) or 0),
            "primary_weighted_trust_score": float(observation.get("primary_weighted_trust_score", 0.0) or 0.0),
            "weighted_trusted_signal_score": float(observation.get("weighted_trusted_signal_score", 0.0) or 0.0),
            "weighted_external_signal_score": float(observation.get("weighted_external_signal_score", 0.0) or 0.0),
            "source_registry_present": bool(observation.get("source_registry_present", False)),
            "source_history_present": bool(observation.get("source_history_present", False)),
            "registered_source_count": len(registered_sources),
            "low_reliability_sources": low_reliability_sources,
            "unseen_sources": unseen_sources,
        },
        "route_posture": {
            "route_risk_present": route is not None,
            "receipt_verified": None if route is None else bool(route.get("receipt_verified", False)),
            "route_shape_supported": None if route is None else bool(route.get("route_shape_supported_for_intents", False)),
            "multi_hop_present": None if route is None else bool(route.get("multi_hop_present", False)),
            "extreme_flags": extreme_flags,
        },
        "confidence_posture": {
            "effective_confidence": effective_confidence,
            "ranking_confidence": ranking_confidence,
            "confidence_cap": confidence_cap,
            "discounted": discounted,
            "discount_reasons": discount_reasons,
        },
    }


def _strategy_from_report(report: AutoTraderLiveReport) -> StrategyIR | None:
    if report.client_policy_bundle is not None:
        return report.client_policy_bundle.client_policy_surface.strategy
    if report.policy_artifact is not None:
        return report.policy_artifact.strategy
    return None


def _source_form_from_report(report: AutoTraderLiveReport) -> str | None:
    if report.client_policy_bundle is not None:
        return report.client_policy_bundle.client_policy_surface.source_form
    if report.krr_explanation is not None:
        authoring_posture = report.krr_explanation.get("authoring_posture")
        if isinstance(authoring_posture, Mapping):
            raw = authoring_posture.get("source_form")
            if isinstance(raw, str) and raw.strip():
                return raw
    return None


def _source_preset_id_from_report(report: AutoTraderLiveReport) -> str | None:
    if report.client_policy_bundle is not None:
        raw = report.client_policy_bundle.client_policy_surface.source_preset_id
        if raw is not None:
            return raw
    if report.krr_explanation is not None:
        authoring_posture = report.krr_explanation.get("authoring_posture")
        if isinstance(authoring_posture, Mapping):
            raw = authoring_posture.get("source_preset_id")
            if isinstance(raw, str) and raw.strip():
                return raw
    return None


def _authoring_mode_from_report(report: AutoTraderLiveReport) -> str:
    if report.krr_explanation is not None:
        authoring_posture = report.krr_explanation.get("authoring_posture")
        if isinstance(authoring_posture, Mapping):
            raw = authoring_posture.get("authoring_mode")
            if isinstance(raw, str) and raw.strip():
                return raw
    strategy = _strategy_from_report(report)
    if _source_form_from_report(report) == "autotrader_user_rule_bundle" and strategy is not None:
        if (
            strategy.template is StrategyTemplate.DCA
            and strategy.allowed_actions == (StrategyAction.PLACE_SWAP_EXACT_IN,)
        ):
            return "dca_swap_exact_in"
        if (
            strategy.template is StrategyTemplate.STOP_LOSS
            and strategy.allowed_actions == (StrategyAction.PLACE_ORDER_INTENT,)
        ):
            return "stop_loss_order_intent"
        if (
            strategy.template is StrategyTemplate.TAKE_PROFIT
            and strategy.allowed_actions == (StrategyAction.PLACE_ORDER_INTENT,)
        ):
            return "take_profit_order_intent"
        return "user_rule_bundle_other"
    return "strategy_ir"


def _build_user_rule_summary(report: AutoTraderLiveReport) -> dict[str, Any] | None:
    strategy = _strategy_from_report(report)
    if strategy is None:
        return None

    asset_in = strategy.template_params.get("asset_in")
    asset_out = strategy.template_params.get("asset_out")
    asset_pair = None
    if isinstance(asset_in, str) and isinstance(asset_out, str) and asset_in.strip() and asset_out.strip():
        asset_pair = f"{asset_in}/{asset_out}"
    elif len(strategy.asset_universe) >= 2:
        asset_pair = f"{strategy.asset_universe[0]}/{strategy.asset_universe[1]}"

    fixed_order_size = strategy.template_params.get("fixed_order_size")
    cadence_epochs = strategy.template_params.get("cadence_epochs")
    trigger_price = strategy.template_params.get("trigger_price")
    preset_id = _source_preset_id_from_report(report)
    preset_profile = describe_autotrader_user_rule_preset(preset_id)
    surface_support_matrix = describe_autotrader_strategy_surface_support(strategy)

    return {
        "source_form": _source_form_from_report(report),
        "preset_id": preset_id,
        "preset_profile": preset_profile,
        "authoring_mode": _authoring_mode_from_report(report),
        "overall_support_status": surface_support_matrix["overall_status"],
        "surface_support_matrix": surface_support_matrix,
        "intent": {
            "template": strategy.template.value,
            "asset_pair": asset_pair,
            "allowed_actions": [action.value for action in strategy.allowed_actions],
        },
        "sizing": {
            "fixed_order_size": fixed_order_size if isinstance(fixed_order_size, int) else None,
            "cadence_epochs": cadence_epochs if isinstance(cadence_epochs, int) else None,
            "per_order_max": int(strategy.notional_caps.per_order_max),
        },
        "trigger": {
            "trigger_price": trigger_price if isinstance(trigger_price, int) else None,
        },
        "budget": {
            "per_window_max": int(strategy.notional_caps.per_window_max),
            "lifetime_max": int(strategy.notional_caps.lifetime_max),
        },
        "risk": {
            "max_slippage_bps": int(strategy.risk_limits.max_slippage_bps),
            "max_oracle_staleness_epochs": int(strategy.risk_limits.max_oracle_staleness_epochs),
            "require_quote_receipts": bool(strategy.risk_limits.require_quote_receipts),
        },
        "window": {
            "valid_from_epoch": int(strategy.strategy_window.valid_from_epoch),
            "valid_until_epoch": int(strategy.strategy_window.valid_until_epoch),
            "min_order_spacing_epochs": int(strategy.strategy_window.min_order_spacing_epochs),
        },
        "controls": {
            "kill_switch_enabled": bool(strategy.controls.kill_switch_enabled),
            "max_live_orders": int(strategy.controls.max_live_orders),
        },
    }


def _attach_user_rule_summary(report: AutoTraderLiveReport) -> AutoTraderLiveReport:
    summary = _build_user_rule_summary(report)
    if summary is None:
        return report
    return replace(report, user_rule_summary=summary)


def _attach_krr_explanation(report: AutoTraderLiveReport) -> AutoTraderLiveReport:
    explanation = _build_krr_explanation(report.krr_advice)
    if explanation is None:
        return report
    return replace(report, krr_explanation=explanation)


def _build_actionability_explanation(report: AutoTraderLiveReport) -> dict[str, Any] | None:
    if report.user_rule_summary is None and report.local_guard_evaluation is None and report.krr_explanation is None:
        return None

    blocking_reasons: list[str] = []
    blocking_layer: str | None = None
    if report.local_guard_evaluation is not None and not report.local_guard_evaluation.ok:
        blocking_layer = "local_guards"
        first_reason = report.local_guard_evaluation.first_blocking_reason
        if first_reason is not None:
            blocking_reasons.append(first_reason)
    elif report.live_admission_ok is False:
        blocking_layer = "live_admission"

    if report.live_admission_error is not None and report.live_admission_error not in blocking_reasons:
        blocking_reasons.append(report.live_admission_error)

    trust_posture: dict[str, Any] | None = None
    route_posture: dict[str, Any] | None = None
    confidence_posture: dict[str, Any] | None = None
    if report.krr_explanation is not None:
        trust_posture_raw = report.krr_explanation.get("trust_posture")
        route_posture_raw = report.krr_explanation.get("route_posture")
        confidence_posture_raw = report.krr_explanation.get("confidence_posture")
        if isinstance(trust_posture_raw, dict):
            trust_posture = dict(trust_posture_raw)
        if isinstance(route_posture_raw, dict):
            route_posture = dict(route_posture_raw)
        if isinstance(confidence_posture_raw, dict):
            confidence_posture = dict(confidence_posture_raw)
            discount_reasons_raw = confidence_posture.get("discount_reasons")
            if isinstance(discount_reasons_raw, list):
                for reason in discount_reasons_raw:
                    if isinstance(reason, str) and reason and reason not in blocking_reasons:
                        blocking_reasons.append(reason)

    actionable = (
        report.decision.tag is AutoTraderDecisionTag.SUBMIT
        and report.live_admission_ok is True
        and (report.local_guard_evaluation is None or report.local_guard_evaluation.ok)
    )

    summary = report.user_rule_summary
    intent_summary = None if summary is None else summary.get("intent")
    sizing_summary = None if summary is None else summary.get("sizing")
    trigger_summary = None if summary is None else summary.get("trigger")
    risk_summary = None if summary is None else summary.get("risk")

    return {
        "authoring": None
        if summary is None
        else {
            "source_form": summary.get("source_form"),
            "preset_id": summary.get("preset_id"),
            "preset_profile": summary.get("preset_profile"),
            "authoring_mode": summary.get("authoring_mode"),
            "overall_support_status": summary.get("overall_support_status"),
            "surface_support_matrix": summary.get("surface_support_matrix"),
        },
        "intent": intent_summary,
        "sizing": sizing_summary,
        "trigger": trigger_summary,
        "risk": risk_summary,
        "actionability": {
            "actionable": actionable,
            "decision_tag": report.decision.tag.value,
            "decision_reason": report.decision.reason,
            "live_admission_ok": report.live_admission_ok,
            "live_admission_error": report.live_admission_error,
            "blocking_layer": blocking_layer,
            "blocking_reasons": blocking_reasons,
        },
        "guard_posture": None
        if report.local_guard_evaluation is None
        else {
            "ok": report.local_guard_evaluation.ok,
            "blocking_families": list(report.local_guard_evaluation.blocking_families),
            "blocking_reason_codes": list(report.local_guard_evaluation.blocking_reason_codes),
            "first_blocking_reason": report.local_guard_evaluation.first_blocking_reason,
        },
        "trust_posture": trust_posture,
        "route_posture": route_posture,
        "confidence_posture": confidence_posture,
    }


def _attach_actionability_explanation(report: AutoTraderLiveReport) -> AutoTraderLiveReport:
    explanation = _build_actionability_explanation(report)
    if explanation is None:
        return report
    return replace(report, actionability_explanation=explanation)


def _build_actionability_summary(report: AutoTraderLiveReport) -> dict[str, Any] | None:
    explanation = report.actionability_explanation
    if not isinstance(explanation, Mapping):
        return None

    authoring = explanation.get("authoring")
    actionability = explanation.get("actionability")
    trust_posture = explanation.get("trust_posture")
    confidence_posture = explanation.get("confidence_posture")
    if not isinstance(actionability, Mapping):
        return None

    sentences: list[str] = []
    preset_summary: str | None = None
    blocking_summary: str | None = None
    trust_summary: str | None = None
    confidence_summary: str | None = None

    if isinstance(authoring, Mapping):
        preset_profile = authoring.get("preset_profile")
        if isinstance(preset_profile, Mapping):
            label = preset_profile.get("label")
            summary = preset_profile.get("summary")
            optimize_for = preset_profile.get("optimize_for")
            if isinstance(label, str) and label.strip() and isinstance(summary, str) and summary.strip():
                preset_summary = f"{label}: {summary}"
                if isinstance(optimize_for, str) and optimize_for.strip():
                    preset_summary += f" Primary objective: {optimize_for}."
                sentences.append(preset_summary)

    actionable = bool(actionability.get("actionable", False))
    decision_tag = actionability.get("decision_tag")
    decision_reason = actionability.get("decision_reason")
    blocking_layer = actionability.get("blocking_layer")
    blocking_reasons_raw = actionability.get("blocking_reasons")
    blocking_reasons: list[str] = []
    if isinstance(blocking_reasons_raw, list):
        blocking_reasons = [str(reason) for reason in blocking_reasons_raw if str(reason).strip()]

    if actionable:
        reason_text = _summarize_actionability_reason(decision_reason) or ""
        headline = f"Actionable: {decision_tag}." if isinstance(decision_tag, str) and decision_tag else "Actionable."
        if reason_text:
            headline = headline[:-1] + f" because {reason_text}."
    else:
        if blocking_layer == "local_guards" and blocking_reasons:
            blocking_summary = f"Blocked by local guards: {blocking_reasons[0]}."
        elif blocking_layer == "live_admission" and blocking_reasons:
            blocking_summary = f"Blocked by live admission: {blocking_reasons[0]}."
        elif isinstance(decision_reason, str) and decision_reason.strip():
            blocking_summary = f"Not actionable: {decision_reason}."
        else:
            blocking_summary = "Not actionable."
        headline = blocking_summary
    sentences.append(headline)

    if isinstance(trust_posture, Mapping):
        tier = trust_posture.get("primary_trust_tier")
        trusted_signal_count = trust_posture.get("trusted_signal_count")
        registry_present = trust_posture.get("source_registry_present")
        primary_weighted = trust_posture.get("primary_weighted_trust_score")
        weighted_trusted = trust_posture.get("weighted_trusted_signal_score")
        weighted_external = trust_posture.get("weighted_external_signal_score")
        if isinstance(tier, str) and tier.strip():
            trusted_text = trusted_signal_count if isinstance(trusted_signal_count, int) else 0
            registry_text = "with registry support" if bool(registry_present) else "without registry support"
            trust_summary = (
                f"Trust posture: primary tier {tier} from {trusted_text} trusted signal"
                f"{'s' if trusted_text != 1 else ''} {registry_text}."
            )
            weighted_parts: list[str] = []
            if isinstance(primary_weighted, (int, float)):
                weighted_parts.append(f"primary={float(primary_weighted):.2f}")
            if isinstance(weighted_trusted, (int, float)):
                weighted_parts.append(f"trusted={float(weighted_trusted):.2f}")
            if isinstance(weighted_external, (int, float)) and float(weighted_external) > 0.0:
                weighted_parts.append(f"external={float(weighted_external):.2f}")
            if weighted_parts:
                trust_summary += f" Weighted support: {', '.join(weighted_parts)}."
            sentences.append(trust_summary)

    if isinstance(confidence_posture, Mapping):
        discounted = bool(confidence_posture.get("discounted", False))
        effective_confidence = confidence_posture.get("effective_confidence")
        ranking_confidence = confidence_posture.get("ranking_confidence")
        discount_reasons_raw = confidence_posture.get("discount_reasons")
        discount_reasons: list[str] = []
        if isinstance(discount_reasons_raw, list):
            discount_reasons = [str(reason) for reason in discount_reasons_raw if str(reason).strip()]
        if discounted:
            confidence_summary = (
                f"Confidence discounted from {ranking_confidence} to {effective_confidence}"
                + (f" due to {', '.join(discount_reasons)}." if discount_reasons else ".")
            )
            sentences.append(confidence_summary)
        elif effective_confidence is not None:
            confidence_summary = f"Confidence stable at {effective_confidence}."
            sentences.append(confidence_summary)

    return {
        "headline": headline,
        "preset_summary": preset_summary,
        "blocking_summary": blocking_summary,
        "trust_summary": trust_summary,
        "confidence_summary": confidence_summary,
        "sentences": sentences,
    }


def _attach_actionability_summary(report: AutoTraderLiveReport) -> AutoTraderLiveReport:
    summary = _build_actionability_summary(report)
    if summary is None:
        return report
    return replace(report, actionability_summary=summary)


def _attach_client_policy_bundle_context(
    report: AutoTraderLiveReport,
    bundle: AutoTraderClientPolicyBundle | None,
    *,
    bundle_ok: bool | None,
    bundle_error: str | None,
    bundle_signature_ok: bool | None,
) -> AutoTraderLiveReport:
    if bundle is None and bundle_ok is None and bundle_error is None and bundle_signature_ok is None:
        return report
    updated = replace(
        report,
        client_policy_bundle=bundle,
        client_policy_bundle_ok=bundle_ok,
        client_policy_bundle_error=bundle_error,
        client_policy_bundle_signature_ok=bundle_signature_ok,
    )
    return _attach_actionability_summary(
        _attach_actionability_explanation(_attach_user_rule_summary(updated))
    )


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


def _build_nonce_tau_receipts(
    *,
    strategy: StrategyIR,
    intents: tuple[Intent, ...],
    last_used_nonce: int,
) -> tuple[AutoTraderNonceTauReceipt, ...]:
    receipts: list[AutoTraderNonceTauReceipt] = []
    previous = int(last_used_nonce)
    for intent in intents:
        fields = intent.fields or {}
        nonce_raw = fields.get("nonce")
        nonce = _require_u32("intent.fields.nonce", nonce_raw, minimum=1)
        expected = previous + 1
        local_result = check_strategy_nonce(
            intent_nonce=nonce,
            last_used_nonce=previous,
            expected_nonce=expected,
        )
        tau_receipt = build_nonce_guard_tau_policy_receipt(
            strategy=strategy,
            intent_nonce=nonce,
            last_used_nonce=previous,
            expected_nonce=expected,
        )
        receipts.append(
            AutoTraderNonceTauReceipt(
                spec_id=tau_receipt.spec_id,
                gate_output=tau_receipt.gate_output,
                intent_id=intent.intent_id,
                intent_nonce=nonce,
                last_used_nonce=previous,
                expected_nonce=expected,
                steps=tau_receipt.steps,
                expected_ok=bool(local_result.ok),
            )
        )
        previous = nonce
    return tuple(receipts)


def _verify_nonce_tau_receipt(
    *,
    tau_bin: str,
    config: AutoTraderTauConfig,
    receipt: AutoTraderNonceTauReceipt,
) -> str | None:
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=AUTOTRADER_NONCE_GUARD_V1.path,
            steps=list(receipt.steps),
            timeout_s=config.timeout_s,
        )
    except Exception as exc:
        return f"nonce_tau_runner_error:{type(exc).__name__}:{exc}"
    tau_gate_value = outputs.get(0, {}).get(receipt.gate_output)
    if tau_gate_value is None:
        return f"nonce_tau_missing_output:{receipt.gate_output}"
    tau_ok = int(tau_gate_value) == 1
    if tau_ok != receipt.expected_ok:
        return (
            "nonce_tau_mismatch:"
            f"intent_id={receipt.intent_id},local={int(receipt.expected_ok)},tau={int(tau_ok)}"
        )
    return None


def _build_tx_envelope_tau_receipt(
    *,
    strategy: StrategyIR,
    tx_requested: bool,
    sequence_number: object,
    expiration_time: object,
    fee_limit: object,
    operations: Mapping[str, object],
) -> TauPolicyReceipt:
    keys = list(operations.keys()) if isinstance(operations, Mapping) else []
    intents_stream = operations.get("2") if isinstance(operations, Mapping) else None
    local_result = check_strategy_tx_envelope(
        tx_requested=tx_requested,
        sequence_number=sequence_number,
        expiration_time=expiration_time,
        fee_limit=fee_limit,
        operations=operations,
    )
    step = build_autotrader_tx_envelope_guard_v1_step(
        tx_requested=1 if tx_requested else 0,
        sequence_present=1 if sequence_number is not None else 0,
        expiration_present=1 if expiration_time is not None else 0,
        sequence_valid=1
        if isinstance(sequence_number, int) and not isinstance(sequence_number, bool) and 0 <= sequence_number <= _U32_MAX
        else 0,
        expiration_valid=1
        if isinstance(expiration_time, int)
        and not isinstance(expiration_time, bool)
        and 1 <= expiration_time <= _U32_MAX
        else 0,
        fee_limit_valid=1 if local_result.tx_fee_limit_ok else 0,
        intent_stream_present=1 if isinstance(intents_stream, list) and len(intents_stream) > 0 else 0,
        settlement_stream_absent=1 if "3" not in operations else 0,
        extra_custom_streams_absent=1 if set(keys) <= {"2"} else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_TX_ENVELOPE_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_TX_ENVELOPE_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def _verify_tx_envelope_tau_receipt(
    *,
    tau_bin: str,
    config: AutoTraderTauConfig,
    receipt: TauPolicyReceipt,
) -> str | None:
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=AUTOTRADER_TX_ENVELOPE_GUARD_V1.path,
            steps=list(receipt.steps),
            timeout_s=config.timeout_s,
        )
    except Exception as exc:
        return f"tx_envelope_tau_runner_error:{type(exc).__name__}:{exc}"
    tau_gate_value = outputs.get(0, {}).get(receipt.gate_output)
    if tau_gate_value is None:
        return f"tx_envelope_tau_missing_output:{receipt.gate_output}"
    tau_ok = int(tau_gate_value) == 1
    if tau_ok != receipt.expected_ok:
        return f"tx_envelope_tau_mismatch:local={int(receipt.expected_ok)},tau={int(tau_ok)}"
    return None


def _verify_boolean_tau_receipt(
    *,
    tau_bin: str,
    config: AutoTraderTauConfig,
    receipt: TauPolicyReceipt,
    spec_path: str,
    error_prefix: str,
) -> str | None:
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=list(receipt.steps),
            timeout_s=config.timeout_s,
        )
    except Exception as exc:
        return f"{error_prefix}_runner_error:{type(exc).__name__}:{exc}"
    tau_gate_value = outputs.get(0, {}).get(receipt.gate_output)
    if tau_gate_value is None:
        return f"{error_prefix}_missing_output:{receipt.gate_output}"
    tau_ok = int(tau_gate_value) == 1
    if tau_ok != receipt.expected_ok:
        return f"{error_prefix}_mismatch:local={int(receipt.expected_ok)},tau={int(tau_ok)}"
    return None


def _build_bounded_multiaction_live_sidecar(
    *,
    strategy: StrategyIR,
    tau_policy_bundle: TauPolicyBundle,
    policy_artifact: StrategyPolicyArtifact,
    observation_packet: AutoTraderObservationPacket,
    decision_tag: AutoTraderDecisionTag,
    kill_switch_ok: bool,
    tau_config: AutoTraderTauConfig | None,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "candidate_set": None,
        "candidate_set_contract": {
            "ok": None,
            "error": None,
            "frontier_unambiguous": None,
        },
        "decision_certificate": None,
        "decision_witness": None,
        "decision_contract": {
            "ok": None,
            "error": None,
            "frontier_unambiguous": None,
        },
        "decision_witness_contract": {
            "ok": None,
            "error": None,
            "frontier_unambiguous": None,
        },
        "tau_argmax_contract": {
            "ok": None,
            "error": None,
            "tau_enabled": bool(tau_config.enabled) if tau_config is not None else False,
            "tau_used": False,
            "frontier_unambiguous": None,
        },
    }
    if len(strategy.allowed_actions) != 1:
        result["candidate_set_contract"] = {
            "ok": None,
            "error": "multi_action_frontier_ambiguous",
            "frontier_unambiguous": False,
        }
        result["decision_contract"] = {
            "ok": None,
            "error": "multi_action_frontier_ambiguous",
            "frontier_unambiguous": False,
        }
        result["decision_witness_contract"] = {
            "ok": None,
            "error": "multi_action_frontier_ambiguous",
            "frontier_unambiguous": False,
        }
        result["tau_argmax_contract"] = {
            "ok": None,
            "error": "multi_action_frontier_ambiguous",
            "tau_enabled": bool(tau_config.enabled) if tau_config is not None else False,
            "tau_used": False,
            "frontier_unambiguous": False,
        }
        return result

    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=policy_artifact,
        tau_policy_bundle=tau_policy_bundle,
        observation_packet=observation_packet,
        action_frontier={
            strategy.allowed_actions[0]: (
                decision_tag is AutoTraderDecisionTag.SUBMIT,
                (decision_tag is AutoTraderDecisionTag.SUBMIT) and bool(kill_switch_ok),
                1,
            )
        },
    )
    candidate_set_contract = check_strategy_multi_action_candidate_set_contract(candidate_set)
    certificate = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)
    cert_ok, cert_error = verify_bounded_multi_action_decision_certificate(
        candidate_set=candidate_set,
        certificate=certificate,
    )
    result["candidate_set"] = candidate_set
    result["candidate_set_contract"] = {
        "ok": bool(candidate_set_contract.ok),
        "error": candidate_set_contract.error,
        "frontier_unambiguous": True,
    }
    if not candidate_set_contract.ok:
        result["decision_contract"] = {
            "ok": False,
            "error": f"candidate_set_rejected:{candidate_set_contract.error}",
            "frontier_unambiguous": True,
        }
        result["decision_witness_contract"] = {
            "ok": None,
            "error": "candidate_set_rejected",
            "frontier_unambiguous": True,
        }
        result["tau_argmax_contract"] = {
            "ok": None,
            "error": "candidate_set_rejected",
            "tau_enabled": bool(tau_config.enabled) if tau_config is not None else False,
            "tau_used": False,
            "frontier_unambiguous": True,
        }
        return result
    result["decision_certificate"] = certificate
    result["decision_contract"] = {
        "ok": cert_ok,
        "error": cert_error,
        "frontier_unambiguous": True,
    }
    try:
        witness = build_decision_witness_from_autotrader_multiaction_decision(
            strategy=strategy,
            observation_packet=observation_packet,
            candidate_set=candidate_set,
            certificate=certificate,
        )
        witness_ok, witness_error = verify_decision_witness_against_autotrader_multiaction_decision(
            strategy=strategy,
            observation_packet=observation_packet,
            candidate_set=candidate_set,
            certificate=certificate,
            witness_payload=witness.to_dict(),
        )
        result["decision_witness"] = witness
        result["decision_witness_contract"] = {
            "ok": witness_ok,
            "error": witness_error,
            "frontier_unambiguous": True,
        }
    except Exception as exc:
        result["decision_witness_contract"] = {
            "ok": False,
            "error": f"{type(exc).__name__}:{exc}",
            "frontier_unambiguous": True,
        }
    if tau_config is not None and tau_config.enabled:
        tau_ok, tau_bin, tau_error = autotrader_controller._resolve_tau_bin(tau_config)
        if tau_ok and tau_bin is not None:
            tau_contract: BoundedMultiActionTauArgmaxContractResult = (
                check_bounded_multi_action_decision_tau_argmax_contract(
                    candidate_set=candidate_set,
                    certificate=certificate,
                    tau_bin=tau_bin,
                    timeout_s=tau_config.timeout_s,
                )
            )
            result["tau_argmax_contract"] = {
                **tau_contract.to_dict(),
                "frontier_unambiguous": True,
            }
        else:
            result["tau_argmax_contract"] = {
                "ok": False,
                "error": tau_error or "tau_not_available",
                "tau_enabled": True,
                "tau_used": False,
                "frontier_unambiguous": True,
            }
    else:
        result["tau_argmax_contract"] = {
            "ok": None,
            "error": "tau_disabled",
            "tau_enabled": False,
            "tau_used": False,
            "frontier_unambiguous": True,
        }
    return result


def _build_submit_bundle_tau_receipt(
    *,
    strategy: StrategyIR,
    emit_requested: bool,
    signed_intents_present: bool,
    signatures_present: bool,
    signatures_verify: bool,
    sender_binding_ok: bool,
    quote_receipts_present: bool,
    operations_roundtrip_ok: bool,
    tx_requested: bool,
    tx_payload_ok: bool,
    expected_ok: bool,
) -> TauPolicyReceipt:
    step = build_autotrader_submit_bundle_guard_v1_step(
        emit_requested=1 if emit_requested else 0,
        signed_intents_present=1 if signed_intents_present else 0,
        signatures_present=1 if signatures_present else 0,
        signatures_verify=1 if signatures_verify else 0,
        sender_binding_ok=1 if sender_binding_ok else 0,
        quote_receipts_present=1 if quote_receipts_present else 0,
        operations_roundtrip_ok=1 if operations_roundtrip_ok else 0,
        tx_requested=1 if tx_requested else 0,
        tx_payload_ok=1 if tx_payload_ok else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_SUBMIT_BUNDLE_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_SUBMIT_BUNDLE_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=expected_ok,
    )


def _registry_guard_relevant(
    signal: ExternalSignalObservation,
    registry: ExternalSignalSourceRegistry | None,
) -> bool:
    if not isinstance(signal, ExternalSignalObservation):
        raise TypeError("signal must be an ExternalSignalObservation")
    if registry is not None and not isinstance(registry, ExternalSignalSourceRegistry):
        raise TypeError("registry must be an ExternalSignalSourceRegistry or None")
    return registry is not None or _trusted_external_signal_requires_registry(signal)


def _build_external_signal_source_registry_tau_receipts(
    *,
    strategy: StrategyIR,
    external_signals: tuple[ExternalSignalObservation, ...],
    signal_source_registry: ExternalSignalSourceRegistry | None,
) -> tuple[AutoTraderExternalSignalSourceRegistryTauReceipt, ...]:
    receipts: list[AutoTraderExternalSignalSourceRegistryTauReceipt] = []
    for signal in external_signals:
        if not _registry_guard_relevant(signal, signal_source_registry):
            continue
        tau_receipt = build_external_signal_source_registry_guard_tau_policy_receipt(
            strategy=strategy,
            signal=signal,
            registry=signal_source_registry,
        )
        receipts.append(
            AutoTraderExternalSignalSourceRegistryTauReceipt(
                spec_id=tau_receipt.spec_id,
                gate_output=tau_receipt.gate_output,
                signal_id=signal.signal_id,
                source_id=signal.source_id,
                steps=tau_receipt.steps,
                expected_ok=bool(tau_receipt.expected_ok),
            )
        )
    return tuple(receipts)


def _verify_external_signal_source_registry_tau_receipt(
    *,
    tau_bin: str,
    config: AutoTraderTauConfig,
    receipt: AutoTraderExternalSignalSourceRegistryTauReceipt,
) -> str | None:
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1.path,
            steps=list(receipt.steps),
            timeout_s=config.timeout_s,
        )
    except Exception as exc:
        return (
            "external_signal_source_registry_tau_runner_error:"
            f"signal_id={receipt.signal_id},source_id={receipt.source_id},"
            f"{type(exc).__name__}:{exc}"
        )
    tau_gate_value = outputs.get(0, {}).get(receipt.gate_output)
    if tau_gate_value is None:
        return (
            "external_signal_source_registry_tau_missing_output:"
            f"signal_id={receipt.signal_id},source_id={receipt.source_id},"
            f"{receipt.gate_output}"
        )
    tau_ok = int(tau_gate_value) == 1
    if tau_ok != receipt.expected_ok:
        return (
            "external_signal_source_registry_tau_mismatch:"
            f"signal_id={receipt.signal_id},source_id={receipt.source_id},"
            f"local={int(receipt.expected_ok)},tau={int(tau_ok)}"
        )
    return None


def _observation_source_registry_ok(packet: AutoTraderObservationPacket) -> bool:
    if not isinstance(packet, AutoTraderObservationPacket):
        raise TypeError("packet must be an AutoTraderObservationPacket")
    return packet.signal_source_registry is not None or packet.trusted_external_count() == 0


def _trusted_external_signal_requires_registry(signal: ExternalSignalObservation) -> bool:
    if not isinstance(signal, ExternalSignalObservation):
        raise TypeError("signal must be an ExternalSignalObservation")
    return (
        signal.source_kind is SignalSourceKind.ATTESTED_EXTERNAL
        and signal.trust_tier in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED)
        and not signal.advisory_only
    )


def _build_live_admission_tau_receipt(
    *,
    strategy: StrategyIR,
    source_registry_ok: bool,
    signal_provenance_ok: bool,
    route_economic_sanity_ok: bool,
    execution_ok: bool,
    oracle_freshness_ok: bool,
    budget_ok: bool,
    tx_envelope_ok: bool,
    session_state_ok: bool,
    session_capability_binding_ok: bool,
    wallet_capability_ok: bool,
    nonce_ok: bool,
    expected_ok: bool,
) -> TauPolicyReceipt:
    step = build_autotrader_live_admission_bundle_v1_step(
        source_registry_ok=1 if source_registry_ok else 0,
        signal_provenance_ok=1 if signal_provenance_ok else 0,
        route_economic_sanity_ok=1 if route_economic_sanity_ok else 0,
        execution_ok=1 if execution_ok else 0,
        oracle_freshness_ok=1 if oracle_freshness_ok else 0,
        budget_ok=1 if budget_ok else 0,
        tx_envelope_ok=1 if tx_envelope_ok else 0,
        session_state_ok=1 if session_state_ok else 0,
        session_capability_binding_ok=1 if session_capability_binding_ok else 0,
        wallet_capability_ok=1 if wallet_capability_ok else 0,
        nonce_ok=1 if nonce_ok else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_LIVE_ADMISSION_BUNDLE_V1.spec_id,
        gate_output=AUTOTRADER_LIVE_ADMISSION_BUNDLE_V1.gate_output,
        steps=(step,),
        expected_ok=expected_ok,
    )


def _build_system_compose_tau_receipt(
    *,
    strategy: StrategyIR,
    emit_requested: bool,
    policy_artifact_ok: bool,
    tau_policy_bundle_ok: bool,
    signer_binding_ok: bool,
    compile_ok: bool,
    source_registry_ok: bool,
    signal_provenance_ok: bool,
    route_economic_sanity_ok: bool,
    execution_ok: bool,
    oracle_freshness_ok: bool,
    budget_ok: bool,
    candidate_set_ok: bool,
    decision_ok: bool,
    kill_switch_ok: bool,
    tx_envelope_ok: bool,
    session_state_ok: bool,
    session_capability_binding_ok: bool,
    wallet_capability_ok: bool,
    nonce_ok: bool,
    expected_ok: bool,
) -> TauPolicyReceipt:
    step = build_autotrader_system_compose_v1_step(
        emit_requested=1 if emit_requested else 0,
        policy_artifact_ok=1 if policy_artifact_ok else 0,
        tau_policy_bundle_ok=1 if tau_policy_bundle_ok else 0,
        signer_binding_ok=1 if signer_binding_ok else 0,
        compile_ok=1 if compile_ok else 0,
        source_registry_ok=1 if source_registry_ok else 0,
        signal_provenance_ok=1 if signal_provenance_ok else 0,
        route_economic_sanity_ok=1 if route_economic_sanity_ok else 0,
        execution_ok=1 if execution_ok else 0,
        oracle_freshness_ok=1 if oracle_freshness_ok else 0,
        budget_ok=1 if budget_ok else 0,
        candidate_set_ok=1 if candidate_set_ok else 0,
        decision_ok=1 if decision_ok else 0,
        kill_switch_ok=1 if kill_switch_ok else 0,
        tx_envelope_ok=1 if tx_envelope_ok else 0,
        session_state_ok=1 if session_state_ok else 0,
        session_capability_binding_ok=1 if session_capability_binding_ok else 0,
        wallet_capability_ok=1 if wallet_capability_ok else 0,
        nonce_ok=1 if nonce_ok else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_SYSTEM_COMPOSE_V1.spec_id,
        gate_output=AUTOTRADER_SYSTEM_COMPOSE_V1.gate_output,
        steps=(step,),
        expected_ok=expected_ok,
    )


def _build_emit_finalize_tau_receipt(
    *,
    strategy: StrategyIR,
    emit_requested: bool,
    system_compose_ok: bool,
    submit_bundle_ok: bool,
    expected_ok: bool,
) -> TauPolicyReceipt:
    step = build_autotrader_emit_finalize_v1_step(
        emit_requested=1 if emit_requested else 0,
        system_compose_ok=1 if system_compose_ok else 0,
        submit_bundle_ok=1 if submit_bundle_ok else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_EMIT_FINALIZE_V1.spec_id,
        gate_output=AUTOTRADER_EMIT_FINALIZE_V1.gate_output,
        steps=(step,),
        expected_ok=expected_ok,
    )


def _build_signer_mismatch_report(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    chain_id: str,
    signer_pubkey: str,
    reason: str,
    last_used_nonce: int,
) -> AutoTraderLiveReport:
    decision = _reject(
        state=controller_state,
        reason=reason,
        explain=(
            f"strategy_id={strategy.strategy_id}",
            f"backend={strategy.policy_backend.value}",
            f"chain_id={chain_id}",
            f"strategy_owner_pubkey={strategy.owner_pubkey}",
            f"signer_pubkey={signer_pubkey}",
        ),
    )
    return _finalize_live_report(
        decision=decision,
        signer_pubkey=signer_pubkey,
        chain_id=chain_id,
        last_used_nonce_before=last_used_nonce,
        last_used_nonce_after=last_used_nonce,
        live_admission_ok=False,
        live_admission_error=reason,
        system_compose_ok=False,
        system_compose_error="signer_binding_rejected",
    )


def _check_client_policy_bundle_identity(
    bundle: AutoTraderClientPolicyBundle,
    *,
    strategy: StrategyIR,
) -> tuple[str | None, bool | None]:
    """Validate a client policy bundle's identity binding to ``strategy``.

    Returns ``(error_reason, signature_ok)``. ``error_reason`` is ``None`` when
    every binding check passes; otherwise it is the stable reject code that the
    caller surfaces. ``signature_ok`` mirrors the live report's
    ``client_policy_bundle_signature_ok`` field: it stays ``None`` until the
    signature stage is reached, then reflects the verification result.

    This is a pure re-expression of the inline binding ladder; the order of
    checks (strategy hash -> owner pubkey -> signature present -> signature
    valid) is part of the reject-precedence contract and is preserved exactly.
    """

    if bundle.strategy_hash != strategy.strategy_hash_hex():
        return "client_policy_bundle_strategy_hash_mismatch", None
    if bundle.owner_pubkey != strategy.owner_pubkey:
        return "client_policy_bundle_owner_pubkey_mismatch", None
    if bundle.signature is None:
        return "client_policy_bundle_signature_missing", False
    signature_ok = verify_autotrader_client_policy_bundle_signature(bundle)
    if not signature_ok:
        return "client_policy_bundle_signature_invalid", False
    return None, signature_ok


def _check_client_policy_bundle_artifact_binding(
    bundle: AutoTraderClientPolicyBundle,
    *,
    policy_artifact: StrategyPolicyArtifact,
    tau_policy_bundle: TauPolicyBundle,
) -> str | None:
    """Validate a client policy bundle's hash binding to the built artifacts.

    Returns the stable reject code for the first failing hash binding, or
    ``None`` when every present hash matches. Each ``*_hash`` field on the
    bundle's client policy surface is optional; a ``None`` field is skipped.
    The check order (source artifact -> tau policy bundle -> policy artifact)
    is part of the reject-precedence contract and is preserved exactly.
    """

    surface = bundle.client_policy_surface
    if (
        surface.source_artifact_hash is not None
        and surface.source_artifact_hash != policy_artifact.source_artifact_hash
    ):
        return "client_policy_bundle_source_artifact_hash_mismatch"
    if (
        surface.tau_policy_bundle_hash is not None
        and surface.tau_policy_bundle_hash != tau_policy_bundle.tau_policy_bundle_hash_hex()
    ):
        return "client_policy_bundle_tau_policy_bundle_hash_mismatch"
    if (
        surface.policy_artifact_hash is not None
        and surface.policy_artifact_hash != policy_artifact.policy_artifact_hash_hex()
    ):
        return "client_policy_bundle_policy_artifact_hash_mismatch"
    return None


@dataclass(frozen=True)
class _TauPolicyBackendPrecheck:
    """Outcome of the ``PolicyBackend.TAU`` pre-check stage (first Tau block).

    On success ``error_reason`` and ``reject_finalize_kwargs`` are ``None`` and
    the four receipt fields carry whatever was built (for the downstream
    success path). On failure ``error_reason`` is the stable reject code and
    ``reject_finalize_kwargs`` is the *exact* extra-kwargs payload for the
    failing stage's ``finalize_report(...)`` call, so the caller reproduces the
    original per-stage report byte-for-byte (including the deliberately
    asymmetric ``external_signal_source_registry_tau_receipts`` propagation:
    carried only on the tau-unavailable/registry-loop stages' successors and
    dropped on the session/wallet capability mismatch stages).
    """

    error_reason: str | None
    reject_finalize_kwargs: dict[str, Any] | None
    session_capability_tau_receipt: TauPolicyReceipt | None
    session_state_tau_receipt: TauPolicyReceipt | None
    wallet_capability_tau_receipt: TauPolicyReceipt | None
    external_signal_source_registry_tau_receipts: tuple[
        AutoTraderExternalSignalSourceRegistryTauReceipt, ...
    ]


def _run_tau_policy_backend_precheck(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    resolved_tau_config: AutoTraderTauConfig,
    chain_id: str,
    signer_pubkey: str,
    last_used_nonce: int,
    effective_wallet_capability: AutoTraderWalletCapability,
    effective_session_state: AutoTraderSessionState,
    observation_packet: AutoTraderObservationPacket | None,
    observation_packet_error: str | None,
    signal_source_registry: ExternalSignalSourceRegistry | None,
    source_registry_ok: bool,
    external_signals: tuple[ExternalSignalObservation, ...],
    current_epoch: int,
    asset_in: str,
    asset_out: str,
    fixed_order_size: int,
) -> _TauPolicyBackendPrecheck:
    """Build and verify the Tau policy-backend pre-check receipts.

    This is a faithful re-expression of the inline first Tau block. The control
    flow (resolve tau bin -> verify each registry receipt -> verify session
    capability / session state / wallet capability receipts in that order) and
    the exact reject payloads are preserved; only the bookkeeping moves here so
    the orchestrator keeps a single reject-return.
    """

    explain = (
        f"strategy_id={strategy.strategy_id}",
        f"backend={strategy.policy_backend.value}",
        f"chain_id={chain_id}",
    )
    common_kwargs: dict[str, Any] = dict(
        signer_pubkey=signer_pubkey,
        chain_id=chain_id,
        last_used_nonce_before=last_used_nonce,
        last_used_nonce_after=last_used_nonce,
        wallet_capability=effective_wallet_capability,
        session_state=effective_session_state,
        observation_packet=observation_packet,
        observation_packet_error=observation_packet_error,
        signal_source_registry=signal_source_registry,
        source_registry_ok=source_registry_ok,
        external_signals=tuple(external_signals),
    )
    session_capability_tau_receipt: TauPolicyReceipt | None = None
    session_state_tau_receipt: TauPolicyReceipt | None = None
    wallet_capability_tau_receipt: TauPolicyReceipt | None = None
    external_signal_source_registry_tau_receipts: tuple[
        AutoTraderExternalSignalSourceRegistryTauReceipt, ...
    ] = ()

    def _result(
        *, error_reason: str | None, reject_finalize_kwargs: dict[str, Any] | None
    ) -> _TauPolicyBackendPrecheck:
        return _TauPolicyBackendPrecheck(
            error_reason=error_reason,
            reject_finalize_kwargs=reject_finalize_kwargs,
            session_capability_tau_receipt=session_capability_tau_receipt,
            session_state_tau_receipt=session_state_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            external_signal_source_registry_tau_receipts=external_signal_source_registry_tau_receipts,
        )

    ok, tau_bin, err = autotrader_controller._resolve_tau_bin(resolved_tau_config)
    if not ok or tau_bin is None:
        reject = _reject(
            state=controller_state,
            reason=f"tau_tool_unavailable:{err}",
            explain=explain,
        )
        return _result(
            error_reason=f"tau_tool_unavailable:{err}",
            reject_finalize_kwargs={"decision": reject, **common_kwargs},
        )

    external_signal_source_registry_tau_receipts = (
        _build_external_signal_source_registry_tau_receipts(
            strategy=strategy,
            external_signals=tuple(external_signals),
            signal_source_registry=signal_source_registry,
        )
    )
    for registry_receipt in external_signal_source_registry_tau_receipts:
        tau_error = _verify_external_signal_source_registry_tau_receipt(
            tau_bin=tau_bin,
            config=resolved_tau_config,
            receipt=registry_receipt,
        )
        if tau_error is not None:
            reject = _reject(
                state=controller_state,
                reason=tau_error,
                explain=explain,
            )
            return _result(
                error_reason=tau_error,
                reject_finalize_kwargs={
                    "decision": reject,
                    "live_admission_ok": False,
                    "live_admission_error": tau_error,
                    **common_kwargs,
                    "external_signal_source_registry_tau_receipts": external_signal_source_registry_tau_receipts,
                },
            )

    session_capability_tau_receipt = build_session_capability_binding_guard_tau_policy_receipt(
        strategy=strategy,
        capability=effective_wallet_capability,
        chain_id=chain_id,
    )
    tau_error = autotrader_controller._verify_tau_policy_receipt(
        tau_bin=tau_bin,
        config=resolved_tau_config,
        receipt=session_capability_tau_receipt,
    )
    if tau_error is not None:
        reject = _reject(
            state=controller_state,
            reason=tau_error,
            explain=explain,
            tau_policy_receipt=session_capability_tau_receipt,
        )
        return _result(
            error_reason=tau_error,
            reject_finalize_kwargs={
                "decision": reject,
                "live_admission_ok": False,
                "live_admission_error": tau_error,
                **common_kwargs,
                "session_capability_tau_receipt": session_capability_tau_receipt,
            },
        )

    session_state_tau_receipt = build_session_state_guard_tau_policy_receipt(
        strategy=strategy,
        session_state=effective_session_state,
        capability=effective_wallet_capability,
        chain_id=chain_id,
        current_epoch=current_epoch,
    )
    tau_error = autotrader_controller._verify_tau_policy_receipt(
        tau_bin=tau_bin,
        config=resolved_tau_config,
        receipt=session_state_tau_receipt,
    )
    if tau_error is not None:
        reject = _reject(
            state=controller_state,
            reason=tau_error,
            explain=explain,
            tau_policy_receipt=session_state_tau_receipt,
        )
        return _result(
            error_reason=tau_error,
            reject_finalize_kwargs={
                "decision": reject,
                "live_admission_ok": False,
                "live_admission_error": tau_error,
                **common_kwargs,
                "session_state_tau_receipt": session_state_tau_receipt,
                "session_capability_tau_receipt": session_capability_tau_receipt,
            },
        )

    wallet_capability_tau_receipt = build_wallet_capability_guard_tau_policy_receipt(
        strategy=strategy,
        capability=effective_wallet_capability,
        signer_pubkey=signer_pubkey,
        chain_id=chain_id,
        current_epoch=current_epoch,
        asset_in=asset_in,
        asset_out=asset_out,
        order_amount=fixed_order_size,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    tau_error = autotrader_controller._verify_tau_policy_receipt(
        tau_bin=tau_bin,
        config=resolved_tau_config,
        receipt=wallet_capability_tau_receipt,
    )
    if tau_error is not None:
        reject = _reject(
            state=controller_state,
            reason=tau_error,
            explain=explain,
            tau_policy_receipt=wallet_capability_tau_receipt,
        )
        return _result(
            error_reason=tau_error,
            reject_finalize_kwargs={
                "decision": reject,
                "live_admission_ok": False,
                "live_admission_error": tau_error,
                **common_kwargs,
                "session_state_tau_receipt": session_state_tau_receipt,
                "session_capability_tau_receipt": session_capability_tau_receipt,
                "wallet_capability_tau_receipt": wallet_capability_tau_receipt,
            },
        )

    return _result(error_reason=None, reject_finalize_kwargs=None)


def prepare_autotrader_live_quote_receipt(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    controller_state_load_error: str | None = None,
    receipt: Mapping[str, object],
    receipt_load_error: str | None = None,
    pools_by_id: Mapping[str, PoolState],
    pools_load_error: str | None = None,
    current_epoch: int,
    intent_deadline: int,
    signer_privkey: str | int | bytes | bytearray,
    last_used_nonce: int,
    chain_id: str = "tau-net-alpha",
    wallet_capability: AutoTraderWalletCapability | None = None,
    wallet_capability_load_error: str | None = None,
    session_state: AutoTraderSessionState | None = None,
    session_state_load_error: str | None = None,
    external_signals: tuple[ExternalSignalObservation, ...] = (),
    external_signals_load_error: str | None = None,
    signal_source_registry: ExternalSignalSourceRegistry | None = None,
    signal_source_registry_load_error: str | None = None,
    policy_artifact: StrategyPolicyArtifact | None = None,
    policy_artifact_load_error: str | None = None,
    tau_policy_bundle: TauPolicyBundle | None = None,
    tau_policy_bundle_load_error: str | None = None,
    client_policy_bundle: AutoTraderClientPolicyBundle | None = None,
    client_policy_bundle_load_error: str | None = None,
    slippage_bps: int | None = None,
    tau_config: AutoTraderTauConfig | None = None,
    krr_backend: str = "off",
    krr_kb_path: str | None = None,
    krr_kb: Mapping[str, Any] | None = None,
    history_check_stats: Mapping[str, object] | None = None,
    tx_sequence_number: int | None = None,
    tx_expiration_time: int | None = None,
    tx_fee_limit: str | int = "0",
) -> AutoTraderLiveReport:
    last_used_nonce = _require_u32("last_used_nonce", last_used_nonce, minimum=0)
    tx_requested = tx_sequence_number is not None or tx_expiration_time is not None

    signer_binding = check_strategy_signer_binding(
        signer_pubkey="0x" + bls_pubkey_hex_from_privkey(signer_privkey),
        owner_pubkey=strategy.owner_pubkey,
    )
    signer_pubkey = signer_binding.signer_pubkey or str("0x" + bls_pubkey_hex_from_privkey(signer_privkey))
    strategy_owner_pubkey = signer_binding.owner_pubkey or str(strategy.owner_pubkey)
    if not signer_binding.ok:
        return _build_signer_mismatch_report(
            strategy=strategy,
            controller_state=controller_state,
            chain_id=chain_id,
            signer_pubkey=signer_pubkey,
            reason=str(signer_binding.error),
            last_used_nonce=last_used_nonce,
        )

    resolved_tau_config = tau_config or AutoTraderTauConfig()
    fixed_order_size = _require_u32(
        "strategy.template_params.fixed_order_size",
        strategy.template_params.get("fixed_order_size"),
        minimum=1,
    )
    asset_in = str(strategy.template_params.get("asset_in", "")).strip()
    asset_out = str(strategy.template_params.get("asset_out", "")).strip()
    if not asset_in or not asset_out:
        raise ValueError("strategy template params must define asset_in and asset_out")
    effective_wallet_capability = wallet_capability
    effective_session_state = session_state
    effective_client_policy_bundle = client_policy_bundle
    client_policy_bundle_ok: bool | None = None
    client_policy_bundle_error: str | None = None
    client_policy_bundle_signature_ok: bool | None = None

    def finalize_report(**kwargs: Any) -> AutoTraderLiveReport:
        return _attach_client_policy_bundle_context(
            _finalize_live_report(**kwargs),
            effective_client_policy_bundle,
            bundle_ok=client_policy_bundle_ok,
            bundle_error=client_policy_bundle_error,
            bundle_signature_ok=client_policy_bundle_signature_ok,
        )

    # Homogeneous pre-reassignment load-error gates. These four share an
    # identical reject shape and read only the as-yet-unbuilt effective wallet/
    # session inputs; the tuple order is the reject-precedence contract.
    _pre_build_load_error_gates: tuple[tuple[str | None, str], ...] = (
        (receipt_load_error, "receipt_file_load_rejected"),
        (controller_state_load_error, "controller_state_load_rejected"),
        (wallet_capability_load_error, "wallet_capability_load_rejected"),
        (session_state_load_error, "session_state_load_rejected"),
    )
    for load_error_value, reject_reason in _pre_build_load_error_gates:
        if load_error_value is not None:
            reject = _reject(
                state=controller_state,
                reason=reject_reason,
                explain=(
                    f"strategy_id={strategy.strategy_id}",
                    f"backend={strategy.policy_backend.value}",
                    f"chain_id={chain_id}",
                    f"load_error={load_error_value}",
                ),
            )
            return finalize_report(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=reject_reason,
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
            )

    effective_wallet_capability = wallet_capability or build_wallet_capability_from_strategy(
        strategy=strategy,
        chain_id=chain_id,
        lifetime_spent=controller_state.lifetime_spent,
    )
    effective_session_state = session_state or build_session_state_from_capability(
        capability=effective_wallet_capability
    )

    if signal_source_registry_load_error is not None:
        reject = _reject(
            state=controller_state,
            reason="signal_source_registry_load_rejected",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
                f"load_error={signal_source_registry_load_error}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error="signal_source_registry_load_rejected",
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
            signal_source_registry=None,
            source_registry_ok=False,
            external_signals=tuple(external_signals),
        )

    if external_signals_load_error is not None:
        reject = _reject(
            state=controller_state,
            reason="external_signals_load_rejected",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
                f"load_error={external_signals_load_error}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error="external_signals_load_rejected",
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
            signal_source_registry=signal_source_registry,
            source_registry_ok=(signal_source_registry is not None),
            external_signals=(),
        )

    if tau_policy_bundle_load_error is not None:
        reject = _reject(
            state=controller_state,
            reason="tau_policy_bundle_load_rejected",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
                f"load_error={tau_policy_bundle_load_error}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error="tau_policy_bundle_load_rejected",
            wallet_capability=effective_wallet_capability,
            tau_policy_bundle_ok=False,
            tau_policy_bundle_error="tau_policy_bundle_load_rejected",
            session_state=effective_session_state,
        )

    if policy_artifact_load_error is not None:
        reject = _reject(
            state=controller_state,
            reason="policy_artifact_load_rejected",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
                f"load_error={policy_artifact_load_error}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error="policy_artifact_load_rejected",
            wallet_capability=effective_wallet_capability,
            policy_artifact_ok=False,
            policy_artifact_error="policy_artifact_load_rejected",
            session_state=effective_session_state,
        )

    if pools_load_error is not None:
        reject = _reject(
            state=controller_state,
            reason="pools_file_load_rejected",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
                f"load_error={pools_load_error}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error="pools_file_load_rejected",
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
        )

    if client_policy_bundle_load_error is not None:
        client_policy_bundle_ok = False
        client_policy_bundle_error = "client_policy_bundle_load_rejected"
        reject = _reject(
            state=controller_state,
            reason=client_policy_bundle_error,
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
                f"load_error={client_policy_bundle_load_error}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=client_policy_bundle_error,
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
        )

    if effective_client_policy_bundle is not None:
        identity_error, identity_signature_ok = _check_client_policy_bundle_identity(
            effective_client_policy_bundle,
            strategy=strategy,
        )
        if identity_signature_ok is not None:
            client_policy_bundle_signature_ok = identity_signature_ok
        if identity_error is not None:
            client_policy_bundle_ok = False
            client_policy_bundle_error = identity_error
            reject = _reject(
                state=controller_state,
                reason=client_policy_bundle_error,
                explain=(
                    f"strategy_id={strategy.strategy_id}",
                    f"backend={strategy.policy_backend.value}",
                    f"chain_id={chain_id}",
                ),
            )
            return finalize_report(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=client_policy_bundle_error,
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
            )
        client_policy_bundle_ok = True

    compile_contract_ok = check_strategy_compile_contract(strategy).ok
    effective_tau_policy_bundle = tau_policy_bundle
    if effective_tau_policy_bundle is None:
        effective_tau_policy_bundle = build_tau_policy_bundle(
            strategy=strategy,
            compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
        )
    tau_policy_bundle_result = check_strategy_policy_bundle_contract(effective_tau_policy_bundle)
    if not tau_policy_bundle_result.ok:
        reject = _reject(
            state=controller_state,
            reason=f"tau_policy_bundle_rejected:{tau_policy_bundle_result.error}",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            wallet_capability=effective_wallet_capability,
            tau_policy_bundle=effective_tau_policy_bundle,
            tau_policy_bundle_ok=False,
            tau_policy_bundle_error=tau_policy_bundle_result.error,
            session_state=effective_session_state,
        )
    effective_policy_artifact = policy_artifact
    if effective_policy_artifact is None:
        effective_policy_artifact = build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=effective_tau_policy_bundle,
        )
        effective_policy_artifact = sign_strategy_policy_artifact(
            effective_policy_artifact,
            privkey=signer_privkey,
        )
    if effective_client_policy_bundle is not None:
        artifact_binding_error = _check_client_policy_bundle_artifact_binding(
            effective_client_policy_bundle,
            policy_artifact=effective_policy_artifact,
            tau_policy_bundle=effective_tau_policy_bundle,
        )
        if artifact_binding_error is not None:
            client_policy_bundle_ok = False
            client_policy_bundle_error = artifact_binding_error
            reject = _reject(
                state=controller_state,
                reason=client_policy_bundle_error,
                explain=(
                    f"strategy_id={strategy.strategy_id}",
                    f"backend={strategy.policy_backend.value}",
                    f"chain_id={chain_id}",
                ),
            )
            return finalize_report(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=client_policy_bundle_error,
                wallet_capability=effective_wallet_capability,
                policy_artifact=effective_policy_artifact,
                tau_policy_bundle=effective_tau_policy_bundle,
                tau_policy_bundle_ok=True,
                session_state=effective_session_state,
            )
    policy_artifact_result = check_strategy_policy_artifact_contract(
        effective_policy_artifact,
        tau_policy_bundle=effective_tau_policy_bundle,
    )
    if not policy_artifact_result.ok:
        reject = _reject(
            state=controller_state,
            reason=f"policy_artifact_rejected:{policy_artifact_result.error}",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"backend={strategy.policy_backend.value}",
                f"chain_id={chain_id}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            wallet_capability=effective_wallet_capability,
            policy_artifact=effective_policy_artifact,
            policy_artifact_ok=False,
            policy_artifact_error=policy_artifact_result.error,
            tau_policy_bundle=effective_tau_policy_bundle,
            tau_policy_bundle_ok=True,
            session_state=effective_session_state,
        )
    if not (
        strategy.template is StrategyTemplate.DCA
        and StrategyAction.PLACE_SWAP_EXACT_IN in strategy.allowed_actions
    ):
        reject = _reject(
            state=controller_state,
            reason="unsupported_live_strategy_mode",
            explain=(
                f"strategy_id={strategy.strategy_id}",
                f"template={strategy.template.value}",
                f"allowed_actions={','.join(action.value for action in strategy.allowed_actions)}",
                f"chain_id={chain_id}",
            ),
        )
        return finalize_report(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error="unsupported_live_strategy_mode",
            policy_artifact=effective_policy_artifact,
            policy_artifact_ok=True,
            tau_policy_bundle=effective_tau_policy_bundle,
            tau_policy_bundle_ok=True,
        )
    observation_packet = None
    observation_packet_error: str | None = None
    source_registry_ok = signal_source_registry is not None or not any(
        _trusted_external_signal_requires_registry(signal) for signal in external_signals
    )
    try:
        primary_signal = build_quote_receipt_signal_packet(
            receipt=receipt,
            pools_by_id=pools_by_id,
            current_epoch=current_epoch,
        )
        observation_packet = build_autotrader_observation_packet(
            primary_signal=primary_signal,
            wallet_capability=effective_wallet_capability,
            external_signals=tuple(external_signals),
            signal_source_registry=signal_source_registry,
            tau_enabled=resolved_tau_config.enabled,
        )
    except Exception as exc:
        observation_packet = None
        observation_packet_error = f"{type(exc).__name__}:{exc}"
        if external_signals:
            source_registry_ok = False
    else:
        source_registry_ok = _observation_source_registry_ok(observation_packet)
    wallet_capability_result = check_wallet_capability(
        capability=effective_wallet_capability,
        signer_pubkey=signer_pubkey,
        chain_id=chain_id,
        current_epoch=current_epoch,
        asset_in=asset_in,
        asset_out=asset_out,
        order_amount=fixed_order_size,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    session_capability_result = check_strategy_session_capability_binding(
        strategy=strategy,
        capability=effective_wallet_capability,
        chain_id=chain_id,
    )
    session_state_result = check_strategy_session_state(
        session_state=effective_session_state,
        capability=effective_wallet_capability,
        chain_id=chain_id,
        current_epoch=current_epoch,
    )
    session_state_tau_receipt: TauPolicyReceipt | None = None
    session_capability_tau_receipt: TauPolicyReceipt | None = None
    wallet_capability_tau_receipt: TauPolicyReceipt | None = None
    external_signal_source_registry_tau_receipts: tuple[
        AutoTraderExternalSignalSourceRegistryTauReceipt, ...
    ] = ()
    if strategy.policy_backend is PolicyBackend.TAU and resolved_tau_config.enabled:
        tau_precheck = _run_tau_policy_backend_precheck(
            strategy=strategy,
            controller_state=controller_state,
            resolved_tau_config=resolved_tau_config,
            chain_id=chain_id,
            signer_pubkey=signer_pubkey,
            last_used_nonce=last_used_nonce,
            effective_wallet_capability=effective_wallet_capability,
            effective_session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            current_epoch=current_epoch,
            asset_in=asset_in,
            asset_out=asset_out,
            fixed_order_size=fixed_order_size,
        )
        session_capability_tau_receipt = tau_precheck.session_capability_tau_receipt
        session_state_tau_receipt = tau_precheck.session_state_tau_receipt
        wallet_capability_tau_receipt = tau_precheck.wallet_capability_tau_receipt
        external_signal_source_registry_tau_receipts = (
            tau_precheck.external_signal_source_registry_tau_receipts
        )
        if tau_precheck.reject_finalize_kwargs is not None:
            return finalize_report(**tau_precheck.reject_finalize_kwargs)
    # Sequential capability-result gates. Identical reject payload across all
    # three; only the error string, the gate-specific explain suffix and the
    # carried tau policy receipt vary. Tuple order is the reject-precedence
    # contract (session_state -> session_capability -> wallet_capability).
    _capability_result_gates: tuple[
        tuple[object, tuple[str, ...], TauPolicyReceipt | None], ...
    ] = (
        (
            session_state_result,
            (f"session_id={effective_session_state.session_id}",),
            session_state_tau_receipt,
        ),
        (
            session_capability_result,
            (f"session_id={effective_wallet_capability.session_id}",),
            session_capability_tau_receipt,
        ),
        (
            wallet_capability_result,
            (
                f"asset_pair={asset_in}/{asset_out}",
                f"order_amount={fixed_order_size}",
            ),
            wallet_capability_tau_receipt,
        ),
    )
    for capability_result, explain_suffix, capability_tau_receipt in _capability_result_gates:
        if not capability_result.ok:
            capability_error = str(capability_result.error)
            reject = _reject(
                state=controller_state,
                reason=capability_error,
                explain=(
                    f"strategy_id={strategy.strategy_id}",
                    f"backend={strategy.policy_backend.value}",
                    f"chain_id={chain_id}",
                )
                + explain_suffix,
                tau_policy_receipt=capability_tau_receipt,
            )
            return finalize_report(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=capability_error,
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
                observation_packet=observation_packet,
                observation_packet_error=observation_packet_error,
                signal_source_registry=signal_source_registry,
                source_registry_ok=source_registry_ok,
                external_signals=tuple(external_signals),
                session_state_tau_receipt=session_state_tau_receipt,
                session_capability_tau_receipt=session_capability_tau_receipt,
                wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            )
    krr_source_form = "compiled_strategy_ir"
    krr_source_preset_id: str | None = None
    if (
        effective_client_policy_bundle is not None
        and effective_client_policy_bundle.client_policy_surface.source_form is not None
    ):
        krr_source_form = effective_client_policy_bundle.client_policy_surface.source_form
        krr_source_preset_id = effective_client_policy_bundle.client_policy_surface.source_preset_id
    krr_advice, krr_advice_error = _safe_advise_autotrader_krr(
        strategy=strategy,
        phase="live",
        current_epoch=current_epoch,
        backend=krr_backend,
        kb_path=krr_kb_path,
        kb=krr_kb,
        history_check_stats=history_check_stats,
        source_form=krr_source_form,
        source_preset_id=krr_source_preset_id,
        spent_in_window=controller_state.budget_state.spent_in_window,
        lifetime_spent=controller_state.lifetime_spent,
        live_orders=controller_state.live_orders,
        nonce_start=last_used_nonce + 1,
        tau_enabled=resolved_tau_config.enabled,
        observation_packet=observation_packet,
        quote_receipt=receipt,
        pools_by_id=pools_by_id,
    )

    decision = evaluate_autotrader_quote_receipt(
        strategy=strategy,
        controller_state=controller_state,
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=current_epoch,
        intent_deadline=intent_deadline,
        slippage_bps=slippage_bps,
        nonce_start=last_used_nonce + 1,
        tau_config=tau_config,
    )
    effective_observation_packet = observation_packet
    if effective_observation_packet is None:
        try:
            effective_observation_packet = build_autotrader_observation_packet(
                primary_signal=build_quote_receipt_signal_packet(
                    receipt=receipt,
                    pools_by_id=pools_by_id,
                    current_epoch=current_epoch,
                ),
                wallet_capability=effective_wallet_capability,
                external_signals=tuple(external_signals),
                signal_source_registry=signal_source_registry,
                tau_enabled=resolved_tau_config.enabled,
            )
        except Exception as exc:
            packet_error = f"{type(exc).__name__}:{exc}"
            reject = _reject(
                state=controller_state,
                reason=f"observation_packet_build_failed:{packet_error}",
                explain=decision.explain + (f"observation_packet_error={packet_error}",),
                tau_policy_receipt=decision.tau_policy_receipt,
                guard_state=decision.guard_state,
            )
            return finalize_report(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=f"observation_packet_build_failed:{packet_error}",
                wallet_capability=effective_wallet_capability,
                policy_artifact=effective_policy_artifact,
                policy_artifact_ok=True,
                tau_policy_bundle=effective_tau_policy_bundle,
                tau_policy_bundle_ok=True,
                session_state=effective_session_state,
                observation_packet=None,
                observation_packet_error=packet_error,
                signal_source_registry=signal_source_registry,
                source_registry_ok=False if external_signals else source_registry_ok,
                external_signals=tuple(external_signals),
                external_signal_source_registry_tau_receipts=external_signal_source_registry_tau_receipts,
                session_state_tau_receipt=session_state_tau_receipt,
                session_capability_tau_receipt=session_capability_tau_receipt,
                wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                system_compose_ok=False,
                system_compose_error="observation_packet_rejected",
                kill_switch_ok=None,
                kill_switch_error=packet_error,
                krr_advice=krr_advice,
                krr_advice_error=krr_advice_error,
            )
    local_guard_evaluation = evaluate_autotrader_local_guards(
        strategy=strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=current_epoch,
            order_amount=effective_observation_packet.primary_signal.amount_in,
            projected_live_orders=controller_state.live_orders + 1,
            lifetime_spent=controller_state.lifetime_spent,
            spent_in_window=controller_state.budget_state.spent_in_window,
            budget_window_id=controller_state.budget_state.window_id,
            kill_switch_active=controller_state.budget_state.kill_switch_on,
            last_action_epoch=controller_state.last_action_epoch,
            slippage_bps=slippage_bps,
            signal_packet=effective_observation_packet.primary_signal,
        ),
    )

    def finalize_with_local_guard(**kwargs: Any) -> AutoTraderLiveReport:
        return _attach_local_guard_evaluation(finalize_report(**kwargs), local_guard_evaluation)

    kill_switch = check_strategy_kill_switch_guard(
        kill_switch_enabled=strategy.controls.kill_switch_enabled,
        kill_switch_active=controller_state.budget_state.kill_switch_on,
    )
    candidate_set = build_strategy_candidate_set(
        policy_artifact=effective_policy_artifact,
        tau_policy_bundle=effective_tau_policy_bundle,
        observation_packet=effective_observation_packet,
        emit_requested=decision.tag is AutoTraderDecisionTag.SUBMIT,
        emit_admissible=decision.tag is AutoTraderDecisionTag.SUBMIT,
    )
    candidate_set_result = check_strategy_candidate_set_contract(candidate_set)
    decision_certificate = build_strategy_decision_certificate(
        candidate_set=candidate_set,
        kill_switch_active=controller_state.budget_state.kill_switch_on,
    )
    decision_runtime = check_strategy_decision_kernel(
        emit_requested=decision.tag is AutoTraderDecisionTag.SUBMIT,
        emit_admissible=(decision.tag is AutoTraderDecisionTag.SUBMIT) and kill_switch.ok,
    )
    decision_certificate_ok, decision_certificate_error = verify_strategy_decision_certificate(
        candidate_set=candidate_set,
        certificate=decision_certificate,
        expected_kill_switch_active=controller_state.budget_state.kill_switch_on,
    )
    expected_winner_index = 1 if decision.tag is AutoTraderDecisionTag.SUBMIT else 0
    decision_contract_ok = (
        decision_runtime.ok
        and decision_certificate_ok
        and decision_certificate.winner_index == expected_winner_index
    )
    decision_contract_error = None
    if not candidate_set_result.ok:
        decision_contract_error = f"candidate_set_rejected:{candidate_set_result.error}"
    elif not decision_certificate_ok:
        decision_contract_error = f"decision_certificate_rejected:{decision_certificate_error}"
    elif not decision_contract_ok:
        decision_contract_error = (
            "decision_prefers_noop"
            if expected_winner_index == 1
            else "decision_prefers_emit"
        )
    if decision_contract_error is not None:
        reject = _reject(
            state=controller_state,
            reason=decision_contract_error,
            explain=decision.explain + (decision_contract_error,),
            tau_policy_receipt=decision.tau_policy_receipt,
            guard_state=decision.guard_state,
        )
        return finalize_with_local_guard(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=decision_contract_error,
            wallet_capability=effective_wallet_capability,
            policy_artifact=effective_policy_artifact,
            policy_artifact_ok=True,
            tau_policy_bundle=effective_tau_policy_bundle,
            tau_policy_bundle_ok=True,
            session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            external_signal_source_registry_tau_receipts=external_signal_source_registry_tau_receipts,
            session_state_tau_receipt=session_state_tau_receipt,
            session_capability_tau_receipt=session_capability_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            system_compose_ok=False,
            system_compose_error=decision_contract_error,
            candidate_set=candidate_set,
            candidate_set_ok=candidate_set_result.ok,
            candidate_set_error=candidate_set_result.error,
            decision_certificate=decision_certificate,
            decision_ok=decision_contract_ok,
            decision_error=decision_contract_error,
            kill_switch_ok=kill_switch.ok,
            kill_switch_error=kill_switch.error,
            krr_advice=krr_advice,
            krr_advice_error=krr_advice_error,
        )
    bounded_multiaction_sidecar = _build_bounded_multiaction_live_sidecar(
        strategy=strategy,
        tau_policy_bundle=effective_tau_policy_bundle,
        policy_artifact=effective_policy_artifact,
        observation_packet=effective_observation_packet,
        decision_tag=decision.tag,
        kill_switch_ok=kill_switch.ok,
        tau_config=resolved_tau_config,
    )
    if decision.tag is not AutoTraderDecisionTag.SUBMIT:
        system_compose = check_strategy_system_compose(
            emit_requested=False,
            policy_artifact_ok=True,
            tau_policy_bundle_ok=True,
            signer_binding_ok=signer_binding.ok,
            compile_ok=compile_contract_ok,
            source_registry_ok=source_registry_ok,
            signal_provenance_ok=decision.guard_state.signal_provenance_ok,
            route_economic_sanity_ok=decision.guard_state.route_economic_sanity_ok,
            execution_ok=decision.guard_state.execution_ok,
            oracle_freshness_ok=decision.guard_state.oracle_freshness_ok,
            budget_ok=decision.guard_state.budget_ok,
            candidate_set_ok=candidate_set_result.ok,
            decision_ok=decision_contract_ok,
            kill_switch_ok=kill_switch.ok,
            tx_envelope_ok=True,
            session_state_ok=session_state_result.ok,
            session_capability_binding_ok=session_capability_result.ok,
            wallet_capability_ok=wallet_capability_result.ok,
            nonce_ok=True,
        )
        return finalize_with_local_guard(
            decision=decision,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=decision.reason,
            wallet_capability=effective_wallet_capability,
            policy_artifact=effective_policy_artifact,
            policy_artifact_ok=True,
            tau_policy_bundle=effective_tau_policy_bundle,
            tau_policy_bundle_ok=True,
            session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            session_state_tau_receipt=session_state_tau_receipt,
            session_capability_tau_receipt=session_capability_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            system_compose_ok=system_compose.ok,
            system_compose_error=system_compose.error,
            candidate_set=candidate_set,
            candidate_set_ok=candidate_set_result.ok,
            candidate_set_error=candidate_set_result.error,
            decision_certificate=decision_certificate,
            decision_ok=decision_contract_ok,
            decision_error=None if decision_contract_ok else decision_contract_error,
            bounded_multiaction_candidate_set=bounded_multiaction_sidecar["candidate_set"],
            bounded_multiaction_candidate_set_contract=bounded_multiaction_sidecar["candidate_set_contract"],
            bounded_multiaction_decision_certificate=bounded_multiaction_sidecar["decision_certificate"],
            bounded_multiaction_decision_witness=bounded_multiaction_sidecar["decision_witness"],
            bounded_multiaction_decision_contract=bounded_multiaction_sidecar["decision_contract"],
            bounded_multiaction_decision_witness_contract=bounded_multiaction_sidecar["decision_witness_contract"],
            bounded_multiaction_tau_argmax_contract=bounded_multiaction_sidecar["tau_argmax_contract"],
            kill_switch_ok=kill_switch.ok,
            kill_switch_error=kill_switch.error,
            krr_advice=krr_advice,
            krr_advice_error=krr_advice_error,
        )

    intents = tuple(decision.intents)
    nonce_table = NonceTable()
    nonce_table.set_last(strategy_owner_pubkey, last_used_nonce)
    nonces_ok, nonce_error, staged_nonce_table = validate_and_apply_intent_nonce_batch(
        nonces=nonce_table,
        intents=intents,
        require_all_nonces=True,
    )
    if not nonces_ok or staged_nonce_table is None:
        reject = _reject(
            state=controller_state,
            reason=f"live_nonce_validation_failed:{nonce_error}",
            explain=decision.explain,
            tau_policy_receipt=decision.tau_policy_receipt,
        )
        return finalize_with_local_guard(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=f"live_nonce_validation_failed:{nonce_error}",
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            session_state_tau_receipt=session_state_tau_receipt,
            session_capability_tau_receipt=session_capability_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            system_compose_ok=False,
            system_compose_error="nonce_rejected",
            krr_advice=krr_advice,
            krr_advice_error=krr_advice_error,
        )

    nonce_tau_receipts = _build_nonce_tau_receipts(
        strategy=strategy,
        intents=intents,
        last_used_nonce=last_used_nonce,
    )
    preview_operations = create_intent_operation(list(intents))
    tx_envelope_result = check_strategy_tx_envelope(
        tx_requested=tx_requested,
        sequence_number=tx_sequence_number,
        expiration_time=tx_expiration_time,
        fee_limit=tx_fee_limit,
        operations=preview_operations,
    )
    tx_envelope_tau_receipt: TauPolicyReceipt | None = None
    live_admission_tau_receipt: TauPolicyReceipt | None = None
    system_compose_tau_receipt: TauPolicyReceipt | None = None
    submit_bundle_tau_receipt: TauPolicyReceipt | None = None
    emit_finalize_tau_receipt: TauPolicyReceipt | None = None
    live_tau_bin: str | None = None
    if resolved_tau_config.enabled:
        ok, tau_bin, err = autotrader_controller._resolve_tau_bin(resolved_tau_config)
        if not ok or tau_bin is None:
            reject = _reject(
                state=controller_state,
                reason=f"tau_tool_unavailable:{err}",
                explain=decision.explain,
                tau_policy_receipt=decision.tau_policy_receipt,
            )
            return finalize_with_local_guard(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=f"tau_tool_unavailable:{err}",
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
                observation_packet=observation_packet,
                observation_packet_error=observation_packet_error,
                signal_source_registry=signal_source_registry,
                source_registry_ok=source_registry_ok,
                external_signals=tuple(external_signals),
                session_state_tau_receipt=session_state_tau_receipt,
                session_capability_tau_receipt=session_capability_tau_receipt,
                wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                krr_advice=krr_advice,
                krr_advice_error=krr_advice_error,
                nonce_tau_receipts=nonce_tau_receipts,
            )
        if tx_requested:
            tx_envelope_tau_receipt = _build_tx_envelope_tau_receipt(
                strategy=strategy,
                tx_requested=tx_requested,
                sequence_number=tx_sequence_number,
                expiration_time=tx_expiration_time,
                fee_limit=tx_fee_limit,
                operations=preview_operations,
            )
            tau_error = _verify_tx_envelope_tau_receipt(
                tau_bin=tau_bin,
                config=resolved_tau_config,
                receipt=tx_envelope_tau_receipt,
            )
            if tau_error is not None:
                reject = _reject(
                    state=controller_state,
                    reason=tau_error,
                    explain=decision.explain,
                    tau_policy_receipt=decision.tau_policy_receipt,
                )
                return finalize_with_local_guard(
                    decision=reject,
                    signer_pubkey=signer_pubkey,
                    chain_id=chain_id,
                    last_used_nonce_before=last_used_nonce,
                    last_used_nonce_after=last_used_nonce,
                    live_admission_ok=False,
                    live_admission_error=tau_error,
                    wallet_capability=effective_wallet_capability,
                    session_state=effective_session_state,
                    observation_packet=observation_packet,
                    observation_packet_error=observation_packet_error,
                    signal_source_registry=signal_source_registry,
                    source_registry_ok=source_registry_ok,
                    external_signals=tuple(external_signals),
                    session_state_tau_receipt=session_state_tau_receipt,
                    session_capability_tau_receipt=session_capability_tau_receipt,
                    wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                    system_compose_ok=False,
                    system_compose_error="tx_envelope_rejected",
                    krr_advice=krr_advice,
                    krr_advice_error=krr_advice_error,
                    nonce_tau_receipts=nonce_tau_receipts,
                    tx_envelope_tau_receipt=tx_envelope_tau_receipt,
                )
        live_tau_bin = tau_bin
        for nonce_receipt in nonce_tau_receipts:
            tau_error = _verify_nonce_tau_receipt(
                tau_bin=tau_bin,
                config=resolved_tau_config,
                receipt=nonce_receipt,
            )
            if tau_error is not None:
                reject = _reject(
                    state=controller_state,
                    reason=tau_error,
                    explain=decision.explain,
                    tau_policy_receipt=decision.tau_policy_receipt,
                )
                return finalize_with_local_guard(
                    decision=reject,
                    signer_pubkey=signer_pubkey,
                    chain_id=chain_id,
                    last_used_nonce_before=last_used_nonce,
                    last_used_nonce_after=last_used_nonce,
                    live_admission_ok=False,
                    live_admission_error=tau_error,
                    wallet_capability=effective_wallet_capability,
                    session_state=effective_session_state,
                    observation_packet=observation_packet,
                    observation_packet_error=observation_packet_error,
                    signal_source_registry=signal_source_registry,
                    source_registry_ok=source_registry_ok,
                    external_signals=tuple(external_signals),
                    session_state_tau_receipt=session_state_tau_receipt,
                    session_capability_tau_receipt=session_capability_tau_receipt,
                    wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                    system_compose_ok=False,
                    system_compose_error="nonce_rejected",
                    krr_advice=krr_advice,
                    krr_advice_error=krr_advice_error,
                    nonce_tau_receipts=nonce_tau_receipts,
                    tx_envelope_tau_receipt=tx_envelope_tau_receipt,
                )

    live_admission = check_strategy_live_admission_bundle(
        source_registry_ok=source_registry_ok,
        signal_provenance_ok=decision.guard_state.signal_provenance_ok,
        route_economic_sanity_ok=decision.guard_state.route_economic_sanity_ok,
        execution_ok=decision.guard_state.execution_ok,
        oracle_freshness_ok=decision.guard_state.oracle_freshness_ok,
        budget_ok=decision.guard_state.budget_ok,
        tx_envelope_ok=tx_envelope_result.ok,
        session_state_ok=session_state_result.ok,
        session_capability_binding_ok=session_capability_result.ok,
        wallet_capability_ok=wallet_capability_result.ok,
        nonce_ok=True,
    )
    if resolved_tau_config.enabled and live_tau_bin is not None:
        live_admission_tau_receipt = _build_live_admission_tau_receipt(
            strategy=strategy,
            source_registry_ok=source_registry_ok,
            signal_provenance_ok=decision.guard_state.signal_provenance_ok,
            route_economic_sanity_ok=decision.guard_state.route_economic_sanity_ok,
            execution_ok=decision.guard_state.execution_ok,
            oracle_freshness_ok=decision.guard_state.oracle_freshness_ok,
            budget_ok=decision.guard_state.budget_ok,
            tx_envelope_ok=tx_envelope_result.ok,
            session_state_ok=session_state_result.ok,
            session_capability_binding_ok=session_capability_result.ok,
            wallet_capability_ok=wallet_capability_result.ok,
            nonce_ok=True,
            expected_ok=bool(live_admission.ok),
        )
        tau_error = _verify_boolean_tau_receipt(
            tau_bin=live_tau_bin,
            config=resolved_tau_config,
            receipt=live_admission_tau_receipt,
            spec_path=str(AUTOTRADER_LIVE_ADMISSION_BUNDLE_V1.path),
            error_prefix="live_admission_tau",
        )
        if tau_error is not None:
            reject = _reject(
                state=controller_state,
                reason=tau_error,
                explain=decision.explain,
                tau_policy_receipt=decision.tau_policy_receipt,
            )
            return finalize_with_local_guard(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=tau_error,
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
                observation_packet=observation_packet,
                observation_packet_error=observation_packet_error,
                signal_source_registry=signal_source_registry,
                source_registry_ok=source_registry_ok,
                external_signals=tuple(external_signals),
                session_state_tau_receipt=session_state_tau_receipt,
                session_capability_tau_receipt=session_capability_tau_receipt,
                wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                system_compose_ok=False,
                system_compose_error="live_admission_tau_rejected",
                krr_advice=krr_advice,
                krr_advice_error=krr_advice_error,
                nonce_tau_receipts=nonce_tau_receipts,
                tx_envelope_tau_receipt=tx_envelope_tau_receipt,
                live_admission_tau_receipt=live_admission_tau_receipt,
            )
    if not live_admission.ok:
        reject = _reject(
            state=controller_state,
            reason=f"live_admission_bundle_rejected:{live_admission.error}",
            explain=decision.explain + (f"live_admission_error={live_admission.error}",),
            tau_policy_receipt=decision.tau_policy_receipt,
            guard_state=decision.guard_state,
        )
        return finalize_with_local_guard(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=live_admission.error,
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            session_state_tau_receipt=session_state_tau_receipt,
            session_capability_tau_receipt=session_capability_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            system_compose_ok=False,
            system_compose_error=live_admission.error,
            krr_advice=krr_advice,
            krr_advice_error=krr_advice_error,
            nonce_tau_receipts=nonce_tau_receipts,
            tx_envelope_tau_receipt=tx_envelope_tau_receipt,
            live_admission_tau_receipt=live_admission_tau_receipt,
        )
    system_compose = check_strategy_system_compose(
        emit_requested=True,
        policy_artifact_ok=True,
        tau_policy_bundle_ok=True,
        signer_binding_ok=signer_binding.ok,
        compile_ok=compile_contract_ok,
        source_registry_ok=source_registry_ok,
        signal_provenance_ok=decision.guard_state.signal_provenance_ok,
        route_economic_sanity_ok=decision.guard_state.route_economic_sanity_ok,
        execution_ok=decision.guard_state.execution_ok,
        oracle_freshness_ok=decision.guard_state.oracle_freshness_ok,
        budget_ok=decision.guard_state.budget_ok,
        candidate_set_ok=candidate_set_result.ok,
        decision_ok=decision_contract_ok,
        kill_switch_ok=kill_switch.ok,
        tx_envelope_ok=tx_envelope_result.ok,
        session_state_ok=session_state_result.ok,
        session_capability_binding_ok=session_capability_result.ok,
        wallet_capability_ok=wallet_capability_result.ok,
        nonce_ok=True,
    )
    if resolved_tau_config.enabled and live_tau_bin is not None:
        system_compose_tau_receipt = _build_system_compose_tau_receipt(
            strategy=strategy,
            emit_requested=True,
            policy_artifact_ok=True,
            tau_policy_bundle_ok=True,
            signer_binding_ok=signer_binding.ok,
            compile_ok=compile_contract_ok,
            source_registry_ok=source_registry_ok,
            signal_provenance_ok=decision.guard_state.signal_provenance_ok,
            route_economic_sanity_ok=decision.guard_state.route_economic_sanity_ok,
            execution_ok=decision.guard_state.execution_ok,
            oracle_freshness_ok=decision.guard_state.oracle_freshness_ok,
            budget_ok=decision.guard_state.budget_ok,
            candidate_set_ok=candidate_set_result.ok,
            decision_ok=decision_contract_ok,
            kill_switch_ok=kill_switch.ok,
            tx_envelope_ok=tx_envelope_result.ok,
            session_state_ok=session_state_result.ok,
            session_capability_binding_ok=session_capability_result.ok,
            wallet_capability_ok=wallet_capability_result.ok,
            nonce_ok=True,
            expected_ok=bool(system_compose.ok),
        )
        tau_error = _verify_boolean_tau_receipt(
            tau_bin=live_tau_bin,
            config=resolved_tau_config,
            receipt=system_compose_tau_receipt,
            spec_path=str(AUTOTRADER_SYSTEM_COMPOSE_V1.path),
            error_prefix="system_compose_tau",
        )
        if tau_error is not None:
            reject = _reject(
                state=controller_state,
                reason=tau_error,
                explain=decision.explain,
                tau_policy_receipt=decision.tau_policy_receipt,
                guard_state=decision.guard_state,
            )
            return finalize_with_local_guard(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=tau_error,
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
                observation_packet=observation_packet,
                observation_packet_error=observation_packet_error,
                signal_source_registry=signal_source_registry,
                source_registry_ok=source_registry_ok,
                external_signals=tuple(external_signals),
                session_state_tau_receipt=session_state_tau_receipt,
                session_capability_tau_receipt=session_capability_tau_receipt,
                wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                system_compose_ok=False,
                system_compose_error="system_compose_tau_rejected",
                krr_advice=krr_advice,
                krr_advice_error=krr_advice_error,
                nonce_tau_receipts=nonce_tau_receipts,
                tx_envelope_tau_receipt=tx_envelope_tau_receipt,
                live_admission_tau_receipt=live_admission_tau_receipt,
                system_compose_tau_receipt=system_compose_tau_receipt,
            )
    if not system_compose.ok:
        reject = _reject(
            state=controller_state,
            reason=f"system_compose_rejected:{system_compose.error}",
            explain=decision.explain + (f"system_compose_error={system_compose.error}",),
            tau_policy_receipt=decision.tau_policy_receipt,
            guard_state=decision.guard_state,
        )
        return finalize_with_local_guard(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=system_compose.error,
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            session_state_tau_receipt=session_state_tau_receipt,
            session_capability_tau_receipt=session_capability_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            system_compose_ok=False,
            system_compose_error=system_compose.error,
            krr_advice=krr_advice,
            krr_advice_error=krr_advice_error,
            nonce_tau_receipts=nonce_tau_receipts,
            tx_envelope_tau_receipt=tx_envelope_tau_receipt,
            live_admission_tau_receipt=live_admission_tau_receipt,
            system_compose_tau_receipt=system_compose_tau_receipt,
        )

    signed_intents = tuple(
        SignedIntentEnvelope(
            intent=intent,
            signature=sign_intent(intent, signer_privkey, chain_id=chain_id).signature,
            quote_receipt=dict(receipt),
        )
        for intent in intents
    )
    operations = create_signed_intent_operation(list(signed_intents))
    tau_tx_payload: dict[str, Any] | None = None
    if tx_sequence_number is not None and tx_expiration_time is not None:
        tau_tx_payload = build_signed_tau_transaction(
            privkey=signer_privkey,
            sequence_number=_require_u32("tx_sequence_number", tx_sequence_number, minimum=0),
            expiration_time=_require_u32("tx_expiration_time", tx_expiration_time, minimum=1),
            operations=operations,
            fee_limit=tx_fee_limit,
        )

    submit_bundle = check_strategy_submit_bundle(
        emit_requested=True,
        signed_intents=signed_intents,
        operations=operations,
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
        tx_requested=tx_requested,
        sequence_number=tx_sequence_number,
        expiration_time=tx_expiration_time,
        fee_limit=tx_fee_limit,
        tau_tx_payload=tau_tx_payload,
    )
    if resolved_tau_config.enabled and live_tau_bin is not None:
        submit_bundle_tau_receipt = _build_submit_bundle_tau_receipt(
            strategy=strategy,
            emit_requested=True,
            signed_intents_present=submit_bundle.signed_intents_present,
            signatures_present=submit_bundle.signatures_present,
            signatures_verify=submit_bundle.signatures_verify,
            sender_binding_ok=submit_bundle.sender_binding_ok,
            quote_receipts_present=submit_bundle.quote_receipts_present,
            operations_roundtrip_ok=submit_bundle.operations_roundtrip_ok,
            tx_requested=tx_requested,
            tx_payload_ok=submit_bundle.tx_payload_ok,
            expected_ok=bool(submit_bundle.ok),
        )
        tau_error = _verify_boolean_tau_receipt(
            tau_bin=live_tau_bin,
            config=resolved_tau_config,
            receipt=submit_bundle_tau_receipt,
            spec_path=str(AUTOTRADER_SUBMIT_BUNDLE_GUARD_V1.path),
            error_prefix="submit_bundle_tau",
        )
        if tau_error is not None:
            reject = _reject(
                state=controller_state,
                reason=tau_error,
                explain=decision.explain,
                tau_policy_receipt=decision.tau_policy_receipt,
                guard_state=decision.guard_state,
            )
            return finalize_with_local_guard(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=tau_error,
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
                observation_packet=observation_packet,
                observation_packet_error=observation_packet_error,
                signal_source_registry=signal_source_registry,
                source_registry_ok=source_registry_ok,
                external_signals=tuple(external_signals),
                session_state_tau_receipt=session_state_tau_receipt,
                session_capability_tau_receipt=session_capability_tau_receipt,
                wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                system_compose_ok=system_compose.ok,
                system_compose_error=system_compose.error,
                krr_advice=krr_advice,
                krr_advice_error=krr_advice_error,
                signed_intents=signed_intents,
                operations=operations,
                nonce_tau_receipts=nonce_tau_receipts,
                tx_envelope_tau_receipt=tx_envelope_tau_receipt,
                live_admission_tau_receipt=live_admission_tau_receipt,
                system_compose_tau_receipt=system_compose_tau_receipt,
                submit_bundle_ok=False,
                submit_bundle_error="submit_bundle_tau_rejected",
                submit_bundle_tau_receipt=submit_bundle_tau_receipt,
                tau_tx_payload=tau_tx_payload,
            )
    if not submit_bundle.ok:
        reject = _reject(
            state=controller_state,
            reason=f"submit_bundle_rejected:{submit_bundle.error}",
            explain=decision.explain + (f"submit_bundle_error={submit_bundle.error}",),
            tau_policy_receipt=decision.tau_policy_receipt,
            guard_state=decision.guard_state,
        )
        return finalize_with_local_guard(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=submit_bundle.error,
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            session_state_tau_receipt=session_state_tau_receipt,
            session_capability_tau_receipt=session_capability_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            system_compose_ok=system_compose.ok,
            system_compose_error=system_compose.error,
            krr_advice=krr_advice,
            krr_advice_error=krr_advice_error,
            signed_intents=signed_intents,
            operations=operations,
            nonce_tau_receipts=nonce_tau_receipts,
            tx_envelope_tau_receipt=tx_envelope_tau_receipt,
            live_admission_tau_receipt=live_admission_tau_receipt,
            system_compose_tau_receipt=system_compose_tau_receipt,
            submit_bundle_ok=False,
            submit_bundle_error=submit_bundle.error,
            submit_bundle_tau_receipt=submit_bundle_tau_receipt,
            tau_tx_payload=tau_tx_payload,
        )

    emit_finalize = check_strategy_emit_finalize(
        emit_requested=True,
        system_compose_ok=system_compose.ok,
        submit_bundle_ok=submit_bundle.ok,
    )
    if resolved_tau_config.enabled and live_tau_bin is not None:
        emit_finalize_tau_receipt = _build_emit_finalize_tau_receipt(
            strategy=strategy,
            emit_requested=True,
            system_compose_ok=system_compose.ok,
            submit_bundle_ok=submit_bundle.ok,
            expected_ok=bool(emit_finalize.ok),
        )
        tau_error = _verify_boolean_tau_receipt(
            tau_bin=live_tau_bin,
            config=resolved_tau_config,
            receipt=emit_finalize_tau_receipt,
            spec_path=str(AUTOTRADER_EMIT_FINALIZE_V1.path),
            error_prefix="emit_finalize_tau",
        )
        if tau_error is not None:
            reject = _reject(
                state=controller_state,
                reason=tau_error,
                explain=decision.explain,
                tau_policy_receipt=decision.tau_policy_receipt,
                guard_state=decision.guard_state,
            )
            return finalize_with_local_guard(
                decision=reject,
                signer_pubkey=signer_pubkey,
                chain_id=chain_id,
                last_used_nonce_before=last_used_nonce,
                last_used_nonce_after=last_used_nonce,
                live_admission_ok=False,
                live_admission_error=tau_error,
                wallet_capability=effective_wallet_capability,
                session_state=effective_session_state,
                observation_packet=observation_packet,
                observation_packet_error=observation_packet_error,
                signal_source_registry=signal_source_registry,
                source_registry_ok=source_registry_ok,
                external_signals=tuple(external_signals),
                session_state_tau_receipt=session_state_tau_receipt,
                session_capability_tau_receipt=session_capability_tau_receipt,
                wallet_capability_tau_receipt=wallet_capability_tau_receipt,
                system_compose_ok=system_compose.ok,
                system_compose_error=system_compose.error,
                krr_advice=krr_advice,
                krr_advice_error=krr_advice_error,
                signed_intents=signed_intents,
                operations=operations,
                nonce_tau_receipts=nonce_tau_receipts,
                tx_envelope_tau_receipt=tx_envelope_tau_receipt,
                live_admission_tau_receipt=live_admission_tau_receipt,
                system_compose_tau_receipt=system_compose_tau_receipt,
                submit_bundle_ok=submit_bundle.ok,
                submit_bundle_error=submit_bundle.error,
                submit_bundle_tau_receipt=submit_bundle_tau_receipt,
                emit_finalize_ok=False,
                emit_finalize_error="emit_finalize_tau_rejected",
                emit_finalize_tau_receipt=emit_finalize_tau_receipt,
                tau_tx_payload=tau_tx_payload,
            )
    if not emit_finalize.ok:
        reject = _reject(
            state=controller_state,
            reason=f"emit_finalize_rejected:{emit_finalize.error}",
            explain=decision.explain + (f"emit_finalize_error={emit_finalize.error}",),
            tau_policy_receipt=decision.tau_policy_receipt,
            guard_state=decision.guard_state,
        )
        return finalize_with_local_guard(
            decision=reject,
            signer_pubkey=signer_pubkey,
            chain_id=chain_id,
            last_used_nonce_before=last_used_nonce,
            last_used_nonce_after=last_used_nonce,
            live_admission_ok=False,
            live_admission_error=emit_finalize.error,
            wallet_capability=effective_wallet_capability,
            session_state=effective_session_state,
            observation_packet=observation_packet,
            observation_packet_error=observation_packet_error,
            signal_source_registry=signal_source_registry,
            source_registry_ok=source_registry_ok,
            external_signals=tuple(external_signals),
            session_state_tau_receipt=session_state_tau_receipt,
            session_capability_tau_receipt=session_capability_tau_receipt,
            wallet_capability_tau_receipt=wallet_capability_tau_receipt,
            system_compose_ok=system_compose.ok,
            system_compose_error=system_compose.error,
            krr_advice=krr_advice,
            krr_advice_error=krr_advice_error,
            signed_intents=signed_intents,
            operations=operations,
            nonce_tau_receipts=nonce_tau_receipts,
            tx_envelope_tau_receipt=tx_envelope_tau_receipt,
            live_admission_tau_receipt=live_admission_tau_receipt,
            system_compose_tau_receipt=system_compose_tau_receipt,
            submit_bundle_ok=submit_bundle.ok,
            submit_bundle_error=submit_bundle.error,
            submit_bundle_tau_receipt=submit_bundle_tau_receipt,
            emit_finalize_ok=False,
            emit_finalize_error=emit_finalize.error,
            emit_finalize_tau_receipt=emit_finalize_tau_receipt,
            tau_tx_payload=tau_tx_payload,
        )

    return finalize_with_local_guard(
        decision=decision,
        signer_pubkey=signer_pubkey,
        chain_id=chain_id,
        last_used_nonce_before=last_used_nonce,
        last_used_nonce_after=staged_nonce_table.get_last(strategy_owner_pubkey),
        live_admission_ok=True,
        wallet_capability=effective_wallet_capability,
        policy_artifact=effective_policy_artifact,
        policy_artifact_ok=True,
        tau_policy_bundle=effective_tau_policy_bundle,
        tau_policy_bundle_ok=True,
        session_state=effective_session_state,
        observation_packet=observation_packet,
        observation_packet_error=observation_packet_error,
        signal_source_registry=signal_source_registry,
        source_registry_ok=source_registry_ok,
        external_signals=tuple(external_signals),
        external_signal_source_registry_tau_receipts=external_signal_source_registry_tau_receipts,
        session_state_tau_receipt=session_state_tau_receipt,
        session_capability_tau_receipt=session_capability_tau_receipt,
        wallet_capability_tau_receipt=wallet_capability_tau_receipt,
        system_compose_ok=system_compose.ok,
        system_compose_error=system_compose.error,
        candidate_set=candidate_set,
        candidate_set_ok=candidate_set_result.ok,
        candidate_set_error=candidate_set_result.error,
        decision_certificate=decision_certificate,
        decision_ok=decision_contract_ok,
        decision_error=decision_contract_error,
        bounded_multiaction_candidate_set=bounded_multiaction_sidecar["candidate_set"],
        bounded_multiaction_candidate_set_contract=bounded_multiaction_sidecar["candidate_set_contract"],
        bounded_multiaction_decision_certificate=bounded_multiaction_sidecar["decision_certificate"],
        bounded_multiaction_decision_witness=bounded_multiaction_sidecar["decision_witness"],
        bounded_multiaction_decision_contract=bounded_multiaction_sidecar["decision_contract"],
        bounded_multiaction_decision_witness_contract=bounded_multiaction_sidecar["decision_witness_contract"],
        bounded_multiaction_tau_argmax_contract=bounded_multiaction_sidecar["tau_argmax_contract"],
        kill_switch_ok=kill_switch.ok,
        kill_switch_error=kill_switch.error,
        krr_advice=krr_advice,
        krr_advice_error=krr_advice_error,
        signed_intents=signed_intents,
        operations=operations,
        nonce_tau_receipts=nonce_tau_receipts,
        tx_envelope_tau_receipt=tx_envelope_tau_receipt,
        live_admission_tau_receipt=live_admission_tau_receipt,
        system_compose_tau_receipt=system_compose_tau_receipt,
        submit_bundle_ok=submit_bundle.ok,
        submit_bundle_error=submit_bundle.error,
        submit_bundle_tau_receipt=submit_bundle_tau_receipt,
        emit_finalize_ok=emit_finalize.ok,
        emit_finalize_error=emit_finalize.error,
        emit_finalize_tau_receipt=emit_finalize_tau_receipt,
        tau_tx_payload=tau_tx_payload,
    )


# Imported lazily by tests/consumers; kept at module bottom to avoid circular import noise.
from . import autotrader_controller  # noqa: E402
