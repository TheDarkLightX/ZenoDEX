from __future__ import annotations

from copy import deepcopy
from typing import Any, Literal, Mapping, TypedDict

from ..integration.autotrader_signals import AutoTraderObservationPacket, SignalTrustTier
from ..state.pools import PoolState
from .autotrader_user_rule_bundle import describe_autotrader_strategy_surface_support
from .route_economic_sanity import build_route_economic_sanity_snapshot
from .strategy_ir import PolicyBackend, StrategyAction, StrategyIR, StrategyTemplate

AutoTraderKRRPhase = Literal["compile", "shadow", "live"]


class AutoTraderObservationSummary(TypedDict):
    current_epoch: int
    primary_source_kind: str
    primary_trust_tier: str
    primary_quote_verified: bool
    primary_binding_ok: bool
    primary_age_epochs: int
    primary_freshness_ok: bool
    primary_weighted_trust_score: float
    trusted_signal_count: int
    advisory_signal_count: int
    external_signal_count: int
    trusted_external_signal_count: int
    advisory_external_signal_count: int
    weighted_trusted_signal_score: float
    weighted_external_signal_score: float
    source_registry_present: bool
    registered_external_signal_count: int
    source_history_present: bool
    source_history_available_count: int
    low_reliability_external_count: int
    unseen_external_count: int
    wallet_capability_present: bool
    tau_enabled: bool


class AutoTraderSourceQualityRow(TypedDict):
    source_id: str
    source_kind: str
    trust_tier: str
    advisory_only: bool
    auth_ok: bool
    freshness_ok: bool
    registered: bool
    registry_requires_auth: bool
    registry_requires_freshness: bool
    registry_allowed_trust_tiers: list[str]
    history_total: int
    history_submit: int
    history_reject: int
    history_skip: int
    history_submit_rate: float
    trust_tier_weight: float
    registry_weight: float
    auth_weight: float
    freshness_weight: float
    history_weight: float
    effective_weight: float
    low_reliability: bool
    unseen_history: bool


class AutoTraderRouteRiskSummary(TypedDict):
    receipt_verified: bool
    verification_error: str | None
    receipt_kind: str
    leg_count: int
    hop_count: int
    multi_hop_present: bool
    route_shape_supported_for_intents: bool
    max_hop_input_vs_reserve_bps: int
    max_hop_output_vs_reserve_bps: int
    max_hop_price_impact_bps: int
    dominant_hop_pool_id: str
    dominant_hop_asset_in: str
    dominant_hop_asset_out: str
    dominant_hop_amount_in: int
    dominant_hop_reserve_in: int
    dominant_hop_amount_out: int
    dominant_hop_reserve_out: int
    extreme_input_stress_present: bool
    extreme_output_depletion_present: bool
    extreme_price_impact_present: bool


class AutoTraderAuthoringSummary(TypedDict):
    source_form: str | None
    source_preset_id: str | None
    authored_via_user_bundle: bool
    authoring_mode: str
    fixed_order_size: int | None
    cadence_epochs: int | None
    trigger_price: int | None
    asset_in: str | None
    asset_out: str | None


class AutoTraderSurfaceSupportSummary(TypedDict):
    phase: str
    overall_status: str
    current_phase_supported: bool
    current_phase_status: str
    current_phase_executor: str | None
    current_phase_reject_reason: str | None
    surface_support_matrix: dict[str, Any]


AUTOTRADER_KRR_SCHEMA = "zenodex/autotrader-krr-advice/v1"
AUTOTRADER_KRR_DEFAULT_BACKEND = "python"
_USER_RULE_SOURCE_FORM = "autotrader_user_rule_bundle"
_ROUTE_RISK_CHECKS: tuple[str, ...] = (
    "quote::route_shape_support",
    "quote::route_economic_sanity",
)

_PHASE_CHECKS: dict[AutoTraderKRRPhase, tuple[str, ...]] = {
    "compile": (
        "policy::compile_guard",
        "tau::compile_contract",
        "policy::template_bounds",
        "policy::owner_binding",
        "policy::budget_guard",
    ),
    "shadow": (
    "policy::signal_provenance",
    "signal::source_registry",
    "policy::window_guard",
    "policy::cadence_guard",
        "policy::budget_guard",
        "policy::lifetime_cap",
        "policy::live_order_cap",
        "policy::oracle_freshness",
        "quote::receipt_verify",
    ),
    "live": (
        "policy::signal_provenance",
        "signal::source_registry",
        "policy::window_guard",
        "policy::cadence_guard",
        "policy::budget_guard",
        "policy::lifetime_cap",
        "policy::live_order_cap",
        "policy::oracle_freshness",
        "quote::receipt_verify",
        "live::session_state",
        "live::wallet_capability",
        "live::signer_match",
        "live::nonce_guard",
        "live::tx_envelope_guard",
        "live::signed_intent_envelope",
    ),
}

_AUTOTRADER_CHECK_PRIORS: dict[str, dict[str, Any]] = {
    "policy::compile_guard": {"score_bias": 0.03, "evidence_total": 6, "evidence_supported": 5.5},
    "policy::template_bounds": {"score_bias": 0.03, "evidence_total": 5, "evidence_supported": 4.5},
    "policy::owner_binding": {"score_bias": 0.04, "evidence_total": 5, "evidence_supported": 4.8},
    "policy::budget_guard": {"score_bias": 0.05, "evidence_total": 10, "evidence_supported": 9.5},
    "policy::signal_provenance": {"score_bias": 0.05, "evidence_total": 9, "evidence_supported": 8.7},
    "policy::oracle_freshness": {"score_bias": 0.05, "evidence_total": 8, "evidence_supported": 7.5},
    "signal::observation_packet": {"score_bias": 0.03, "evidence_total": 7, "evidence_supported": 6.4},
    "signal::trusted_primary": {"score_bias": 0.05, "evidence_total": 8, "evidence_supported": 7.6},
    "signal::external_advisory_separation": {"score_bias": 0.04, "evidence_total": 6, "evidence_supported": 5.5},
    "signal::external_attestation": {"score_bias": 0.05, "evidence_total": 6, "evidence_supported": 5.7},
    "signal::source_registry": {"score_bias": 0.05, "evidence_total": 6, "evidence_supported": 5.8},
    "signal::source_quality": {"score_bias": 0.04, "evidence_total": 5, "evidence_supported": 4.7},
    "signal::source_history": {"score_bias": 0.04, "evidence_total": 5, "evidence_supported": 4.4},
    "policy::window_guard": {"score_bias": 0.03, "evidence_total": 6, "evidence_supported": 5.6},
    "policy::cadence_guard": {"score_bias": 0.03, "evidence_total": 6, "evidence_supported": 5.5},
    "policy::lifetime_cap": {"score_bias": 0.04, "evidence_total": 7, "evidence_supported": 6.6},
    "policy::live_order_cap": {"score_bias": 0.04, "evidence_total": 7, "evidence_supported": 6.4},
    "policy::kill_switch": {"score_bias": 0.05, "evidence_total": 5, "evidence_supported": 4.8},
    "policy::tau_bundle": {"score_bias": 0.04, "evidence_total": 4, "evidence_supported": 3.8},
    "quote::receipt_verify": {"score_bias": 0.05, "evidence_total": 10, "evidence_supported": 9.4},
    "quote::receipt_binding": {"score_bias": 0.05, "evidence_total": 9, "evidence_supported": 8.5},
    "quote::route_shape_support": {"score_bias": 0.05, "evidence_total": 6, "evidence_supported": 5.6},
    "quote::route_economic_sanity": {"score_bias": 0.05, "evidence_total": 7, "evidence_supported": 6.3},
    "action::swap_exact_in": {"score_bias": 0.02, "evidence_total": 4, "evidence_supported": 3.7},
    "action::swap_exact_out": {"score_bias": 0.02, "evidence_total": 4, "evidence_supported": 3.4},
    "action::order_intent": {"score_bias": 0.02, "evidence_total": 4, "evidence_supported": 3.6},
    "live::signer_match": {"score_bias": 0.06, "evidence_total": 8, "evidence_supported": 7.9},
    "live::session_state": {"score_bias": 0.06, "evidence_total": 8, "evidence_supported": 7.7},
    "live::wallet_capability": {"score_bias": 0.06, "evidence_total": 8, "evidence_supported": 7.8},
    "live::nonce_guard": {"score_bias": 0.06, "evidence_total": 9, "evidence_supported": 8.8},
    "live::tx_envelope_guard": {"score_bias": 0.06, "evidence_total": 8, "evidence_supported": 7.7},
    "live::signed_intent_envelope": {"score_bias": 0.04, "evidence_total": 6, "evidence_supported": 5.6},
    "tau::budget_guard": {"score_bias": 0.06, "evidence_total": 7, "evidence_supported": 6.7},
    "tau::compile_contract": {"score_bias": 0.06, "evidence_total": 6, "evidence_supported": 5.8},
    "tau::execution_guard": {"score_bias": 0.06, "evidence_total": 7, "evidence_supported": 6.8},
    "tau::oracle_freshness_guard": {"score_bias": 0.06, "evidence_total": 7, "evidence_supported": 6.7},
    "tau::session_state_guard": {"score_bias": 0.06, "evidence_total": 7, "evidence_supported": 6.8},
    "tau::signal_provenance_guard": {"score_bias": 0.06, "evidence_total": 7, "evidence_supported": 6.8},
    "tau::wallet_capability_guard": {"score_bias": 0.06, "evidence_total": 7, "evidence_supported": 6.8},
    "tau::nonce_guard": {"score_bias": 0.06, "evidence_total": 7, "evidence_supported": 6.9},
    "surface::mode_support": {"score_bias": 0.07, "evidence_total": 6, "evidence_supported": 6.0},
}

_AUTOTRADER_CHECK_FAMILY_PRIORS: dict[str, dict[str, Any]] = {
    "policy": {"score_bias": 0.03, "evidence_total": 24, "evidence_supported": 22},
    "signal": {"score_bias": 0.03, "evidence_total": 12, "evidence_supported": 11},
    "quote": {"score_bias": 0.03, "evidence_total": 14, "evidence_supported": 13},
    "action": {"score_bias": 0.01, "evidence_total": 8, "evidence_supported": 7},
    "live": {"score_bias": 0.04, "evidence_total": 16, "evidence_supported": 15},
    "tau": {"score_bias": 0.05, "evidence_total": 18, "evidence_supported": 17},
    "surface": {"score_bias": 0.06, "evidence_total": 6, "evidence_supported": 6},
}

_AUTOTRADER_SEMANTIC_RULES: tuple[dict[str, Any], ...] = (
    {
        "name": "autotrader_compile_phase",
        "if_semantic_contains": ["phase=compile"],
        "then_prefer_checks": [
            "policy::compile_guard",
            "tau::compile_contract",
            "policy::template_bounds",
            "policy::owner_binding",
        ],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_live_phase",
        "if_semantic_contains": ["phase=live"],
        "then_prefer_checks": [
            "live::session_state",
            "live::wallet_capability",
            "live::signer_match",
            "live::nonce_guard",
            "live::tx_envelope_guard",
            "live::signed_intent_envelope",
        ],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_tau_bundle",
        "if_semantic_contains": ["backend=tau"],
        "then_prefer_checks": [
            "policy::tau_bundle",
            "tau::compile_contract",
            "tau::signal_provenance_guard",
            "tau::budget_guard",
            "tau::execution_guard",
            "tau::oracle_freshness_guard",
            "tau::session_state_guard",
            "tau::wallet_capability_guard",
        ],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_tau_live_nonce",
        "if_semantic_all": ["live", "tau"],
        "then_prefer_checks": ["tau::nonce_guard"],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_quote_receipts",
        "if_semantic_contains": ["require_quote_receipts=1"],
        "then_prefer_checks": ["policy::signal_provenance", "quote::receipt_verify", "quote::receipt_binding"],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_route_risk_present",
        "if_semantic_contains": ["route_risk_present=1"],
        "then_prefer_checks": ["quote::route_shape_support", "quote::route_economic_sanity"],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_route_shape_unsupported",
        "if_semantic_contains": ["route_shape_supported=0"],
        "then_prefer_checks": ["quote::route_shape_support", "quote::route_economic_sanity"],
        "score_bias": 0.05,
    },
    {
        "name": "autotrader_route_extreme_input_stress",
        "if_semantic_contains": ["route_extreme_input_stress=1"],
        "then_prefer_checks": ["quote::route_economic_sanity", "quote::route_shape_support"],
        "score_bias": 0.05,
    },
    {
        "name": "autotrader_route_extreme_output_depletion",
        "if_semantic_contains": ["route_extreme_output_depletion=1"],
        "then_prefer_checks": ["quote::route_economic_sanity"],
        "score_bias": 0.05,
    },
    {
        "name": "autotrader_route_extreme_price_impact",
        "if_semantic_contains": ["route_extreme_price_impact=1"],
        "then_prefer_checks": ["quote::route_economic_sanity"],
        "score_bias": 0.05,
    },
    {
        "name": "autotrader_observation_packet",
        "if_semantic_contains": ["observation_packet=1"],
        "then_prefer_checks": ["signal::observation_packet", "signal::trusted_primary"],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_low_trust_primary",
        "if_semantic_contains": ["primary_trust_tier=advisory"],
        "then_prefer_checks": ["policy::signal_provenance", "signal::trusted_primary"],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_advisory_external_signals",
        "if_semantic_contains": ["external_advisory_count=1"],
        "then_prefer_checks": ["signal::external_advisory_separation", "signal::source_registry"],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_trusted_external_signals",
        "if_semantic_contains": ["external_trusted_count=1"],
        "then_prefer_checks": ["signal::external_attestation", "signal::source_registry"],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_registered_external_signals",
        "if_semantic_contains": ["source_registry_present=1"],
        "then_prefer_checks": ["signal::source_registry", "signal::source_quality"],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_external_source_history",
        "if_semantic_contains": ["source_history_present=1"],
        "then_prefer_checks": ["signal::source_history", "signal::source_quality"],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_low_reliability_external_sources",
        "if_semantic_contains": ["low_reliability_external_present=1"],
        "then_prefer_checks": ["signal::source_history", "signal::source_registry"],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_unseen_external_sources",
        "if_semantic_contains": ["unseen_external_present=1"],
        "then_prefer_checks": ["signal::source_quality", "signal::source_registry"],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_kill_switch",
        "if_semantic_contains": ["kill_switch_enabled=1"],
        "then_prefer_checks": ["policy::kill_switch"],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_user_rule_bundle_authoring",
        "if_semantic_contains": ["authored_via_user_bundle=1"],
        "then_prefer_checks": [
            "policy::signal_provenance",
            "policy::cadence_guard",
            "policy::budget_guard",
        ],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_dca_swap_exact_in_authoring",
        "if_semantic_contains": ["authoring_mode=dca_swap_exact_in"],
        "then_prefer_checks": [
            "action::swap_exact_in",
            "policy::cadence_guard",
            "policy::budget_guard",
        ],
        "score_bias": 0.02,
    },
    {
        "name": "autotrader_stop_loss_order_intent_authoring",
        "if_semantic_contains": ["authoring_mode=stop_loss_order_intent"],
        "then_prefer_checks": [
            "action::order_intent",
            "policy::signal_provenance",
            "policy::oracle_freshness",
            "quote::receipt_verify",
        ],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_take_profit_order_intent_authoring",
        "if_semantic_contains": ["authoring_mode=take_profit_order_intent"],
        "then_prefer_checks": [
            "action::order_intent",
            "policy::signal_provenance",
            "policy::oracle_freshness",
            "quote::receipt_verify",
        ],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_surface_phase_unsupported",
        "if_semantic_contains": ["surface_current_phase_supported=0"],
        "then_prefer_checks": ["surface::mode_support"],
        "score_bias": 0.08,
    },
    {
        "name": "autotrader_budget_pressure",
        "if_semantic_contains": ["budget_pressure=1"],
        "then_prefer_checks": ["policy::budget_guard", "policy::lifetime_cap"],
        "score_bias": 0.03,
    },
    {
        "name": "autotrader_live_order_pressure",
        "if_semantic_contains": ["live_order_pressure=1"],
        "then_prefer_checks": ["policy::live_order_cap"],
        "score_bias": 0.02,
    },
)


def _uniq(items: list[str] | tuple[str, ...]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for raw in items:
        item = str(raw).strip()
        if not item or item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _merge_list(existing: object, defaults: list[str]) -> list[str]:
    values: list[str] = []
    if isinstance(existing, list):
        values = [str(x).strip() for x in existing if str(x).strip()]
    return _uniq(values + defaults)


def _merge_named_rules(existing: object, defaults: tuple[dict[str, Any], ...]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    if isinstance(existing, list):
        for row in existing:
            if not isinstance(row, dict):
                continue
            name = str(row.get("name", "")).strip()
            if not name or name in seen:
                continue
            seen.add(name)
            rows.append(dict(row))
    for row in defaults:
        name = str(row.get("name", "")).strip()
        if not name or name in seen:
            continue
        seen.add(name)
        rows.append(dict(row))
    return rows


def _load_history_check_rows(existing: Mapping[str, Any] | None) -> dict[str, dict[str, Any]]:
    if not isinstance(existing, Mapping):
        return {}
    root = existing.get("history_check_stats", existing)
    if not isinstance(root, Mapping):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for raw_check, raw_stats in root.items():
        check = str(raw_check).strip()
        if not check or not isinstance(raw_stats, Mapping):
            continue
        out[check] = dict(raw_stats)
    return out


def _load_source_history_rows(existing: Mapping[str, Any] | None) -> dict[str, dict[str, Any]]:
    if not isinstance(existing, Mapping):
        return {}
    root = existing.get("history_source_stats", {})
    if not isinstance(root, Mapping):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for raw_source_id, raw_stats in root.items():
        source_id = str(raw_source_id).strip()
        if not source_id or not isinstance(raw_stats, Mapping):
            continue
        out[source_id] = dict(raw_stats)
    return out


def _template_param_int(strategy: StrategyIR, key: str) -> int | None:
    raw = strategy.template_params.get(key)
    if isinstance(raw, int) and not isinstance(raw, bool):
        return int(raw)
    return None


def _template_param_text(strategy: StrategyIR, key: str) -> str | None:
    raw = strategy.template_params.get(key)
    if isinstance(raw, str):
        text = raw.strip()
        if text:
            return text
    return None


def _authoring_summary(
    *,
    strategy: StrategyIR,
    source_form: str | None,
    source_preset_id: str | None = None,
) -> AutoTraderAuthoringSummary:
    authored_via_user_bundle = source_form == _USER_RULE_SOURCE_FORM
    authoring_mode = "strategy_ir"
    if authored_via_user_bundle:
        if (
            strategy.template is StrategyTemplate.DCA
            and strategy.allowed_actions == (StrategyAction.PLACE_SWAP_EXACT_IN,)
        ):
            authoring_mode = "dca_swap_exact_in"
        elif (
            strategy.template is StrategyTemplate.STOP_LOSS
            and strategy.allowed_actions == (StrategyAction.PLACE_ORDER_INTENT,)
        ):
            authoring_mode = "stop_loss_order_intent"
        elif (
            strategy.template is StrategyTemplate.TAKE_PROFIT
            and strategy.allowed_actions == (StrategyAction.PLACE_ORDER_INTENT,)
        ):
            authoring_mode = "take_profit_order_intent"
        else:
            authoring_mode = "user_rule_bundle_other"
    return {
        "source_form": source_form,
        "source_preset_id": source_preset_id,
        "authored_via_user_bundle": authored_via_user_bundle,
        "authoring_mode": authoring_mode,
        "fixed_order_size": _template_param_int(strategy, "fixed_order_size"),
        "cadence_epochs": _template_param_int(strategy, "cadence_epochs"),
        "trigger_price": _template_param_int(strategy, "trigger_price"),
        "asset_in": _template_param_text(strategy, "asset_in"),
        "asset_out": _template_param_text(strategy, "asset_out"),
    }


def _build_route_risk_summary(
    *,
    quote_receipt: Mapping[str, Any] | None,
    pools_by_id: Mapping[str, PoolState] | None,
) -> AutoTraderRouteRiskSummary | None:
    snapshot = build_route_economic_sanity_snapshot(
        quote_receipt=quote_receipt,
        pools_by_id=pools_by_id,
    )
    if snapshot is None:
        return None

    return {
        "receipt_verified": bool(snapshot.receipt_verified),
        "verification_error": snapshot.verification_error,
        "receipt_kind": snapshot.receipt_kind,
        "leg_count": int(snapshot.leg_count),
        "hop_count": int(snapshot.hop_count),
        "multi_hop_present": bool(snapshot.multi_hop_present),
        "route_shape_supported_for_intents": bool(snapshot.route_shape_supported_for_intents),
        "max_hop_input_vs_reserve_bps": int(snapshot.max_hop_input_vs_reserve_bps),
        "max_hop_output_vs_reserve_bps": int(snapshot.max_hop_output_vs_reserve_bps),
        "max_hop_price_impact_bps": int(snapshot.max_hop_price_impact_bps),
        "dominant_hop_pool_id": snapshot.dominant_hop_pool_id,
        "dominant_hop_asset_in": snapshot.dominant_hop_asset_in,
        "dominant_hop_asset_out": snapshot.dominant_hop_asset_out,
        "dominant_hop_amount_in": int(snapshot.dominant_hop_amount_in),
        "dominant_hop_reserve_in": int(snapshot.dominant_hop_reserve_in),
        "dominant_hop_amount_out": int(snapshot.dominant_hop_amount_out),
        "dominant_hop_reserve_out": int(snapshot.dominant_hop_reserve_out),
        "extreme_input_stress_present": bool(snapshot.extreme_input_stress_present),
        "extreme_output_depletion_present": bool(snapshot.extreme_output_depletion_present),
        "extreme_price_impact_present": bool(snapshot.extreme_price_impact_present),
    }


def _surface_support_summary(
    *,
    strategy: StrategyIR,
    phase: AutoTraderKRRPhase,
) -> AutoTraderSurfaceSupportSummary:
    matrix = describe_autotrader_strategy_surface_support(strategy)
    phase_entry_raw = matrix.get(phase)
    phase_entry = phase_entry_raw if isinstance(phase_entry_raw, Mapping) else {}
    return {
        "phase": str(phase),
        "overall_status": str(matrix.get("overall_status", "unknown")),
        "current_phase_supported": bool(phase_entry.get("supported", False)),
        "current_phase_status": str(phase_entry.get("status", "unknown")),
        "current_phase_executor": (
            str(phase_entry.get("current_executor"))
            if phase_entry.get("current_executor") is not None
            else None
        ),
        "current_phase_reject_reason": (
            str(phase_entry.get("reject_reason_when_unsupported"))
            if phase_entry.get("reject_reason_when_unsupported") is not None
            else None
        ),
        "surface_support_matrix": dict(matrix),
    }


def _merge_autotrader_krr_defaults(kb: Mapping[str, Any] | None) -> dict[str, Any]:
    merged = deepcopy(dict(kb or {}))
    merged.setdefault("schema", "zenodex/krr-kb/v1")

    operator_priors = dict(merged.get("operator_priors", {})) if isinstance(merged.get("operator_priors"), Mapping) else {}
    for template in StrategyTemplate:
        for phase in ("compile", "shadow", "live"):
            operator_id = f"autotrader_{template.value}_{phase}_v1"
            current = dict(operator_priors.get(operator_id, {})) if isinstance(operator_priors.get(operator_id), Mapping) else {}
            current["check_preferences"] = _merge_list(
                current.get("check_preferences"),
                list(_PHASE_CHECKS[phase]),
            )
            current.setdefault("score_bias", 0.02 if phase != "live" else 0.03)
            operator_priors[operator_id] = current
    merged["operator_priors"] = operator_priors

    check_priors = dict(merged.get("check_priors", {})) if isinstance(merged.get("check_priors"), Mapping) else {}
    for check, defaults in _AUTOTRADER_CHECK_PRIORS.items():
        if check in check_priors and isinstance(check_priors[check], Mapping):
            current = dict(check_priors[check])
            for key, value in defaults.items():
                current.setdefault(key, value)
            check_priors[check] = current
        else:
            check_priors[check] = dict(defaults)
    merged["check_priors"] = check_priors

    family_priors = (
        dict(merged.get("check_family_priors", {}))
        if isinstance(merged.get("check_family_priors"), Mapping)
        else {}
    )
    for family, defaults in _AUTOTRADER_CHECK_FAMILY_PRIORS.items():
        if family in family_priors and isinstance(family_priors[family], Mapping):
            current = dict(family_priors[family])
            for key, value in defaults.items():
                current.setdefault(key, value)
            family_priors[family] = current
        else:
            family_priors[family] = dict(defaults)
    merged["check_family_priors"] = family_priors

    merged["semantic_rules"] = _merge_named_rules(merged.get("semantic_rules"), _AUTOTRADER_SEMANTIC_RULES)
    return merged


def autotrader_krr_check_options(
    *,
    strategy: StrategyIR,
    phase: AutoTraderKRRPhase,
    tau_enabled: bool = False,
    observation_packet: AutoTraderObservationPacket | None = None,
    route_risk_summary: AutoTraderRouteRiskSummary | None = None,
    history_source_stats: Mapping[str, Any] | None = None,
    surface_support_summary: AutoTraderSurfaceSupportSummary | None = None,
) -> list[str]:
    checks = list(_PHASE_CHECKS[phase])
    if observation_packet is not None:
        checks.append("signal::observation_packet")
        if observation_packet.trusted_primary():
            checks.append("signal::trusted_primary")
        if observation_packet.external_signals:
            checks.append("signal::source_quality")
        if any(signal.advisory_only for signal in observation_packet.external_signals):
            checks.append("signal::external_advisory_separation")
        if any(not signal.advisory_only for signal in observation_packet.external_signals):
            checks.append("signal::external_attestation")
        if observation_packet.signal_source_registry is not None:
            checks.append("signal::source_registry")
        source_history_rows = _load_source_history_rows(history_source_stats)
        if source_history_rows and observation_packet.external_signals:
            checks.append("signal::source_history")
    if route_risk_summary is not None:
        checks.extend(_ROUTE_RISK_CHECKS)
    if strategy.controls.kill_switch_enabled:
        checks.append("policy::kill_switch")
    if strategy.risk_limits.require_quote_receipts:
        checks.extend(("quote::receipt_verify", "quote::receipt_binding"))
    if StrategyAction.PLACE_SWAP_EXACT_IN in strategy.allowed_actions:
        checks.append("action::swap_exact_in")
    if StrategyAction.PLACE_SWAP_EXACT_OUT in strategy.allowed_actions:
        checks.append("action::swap_exact_out")
    if StrategyAction.PLACE_ORDER_INTENT in strategy.allowed_actions:
        checks.append("action::order_intent")
    if surface_support_summary is not None and not surface_support_summary["current_phase_supported"]:
        checks.append("surface::mode_support")
    if strategy.policy_backend is PolicyBackend.TAU or tau_enabled:
        checks.extend(
            (
                "policy::tau_bundle",
                "tau::compile_contract",
                "tau::signal_provenance_guard",
                "tau::budget_guard",
                "tau::execution_guard",
                "tau::oracle_freshness_guard",
                "tau::session_state_guard",
                "tau::wallet_capability_guard",
            )
        )
        if phase == "live":
            checks.append("tau::nonce_guard")
    return _uniq(checks)


def _trust_tier_weight(value: SignalTrustTier) -> float:
    if value is SignalTrustTier.PROTOCOL:
        return 1.0
    if value is SignalTrustTier.VERIFIED:
        return 0.95
    if value is SignalTrustTier.ATTESTED:
        return 0.75
    return 0.25


def _history_submit_weight(*, history_total: int, history_submit_rate: float) -> float:
    if history_total <= 0:
        return 0.65
    rate = _clamp_unit_interval(history_submit_rate)
    return round(0.25 + (0.75 * rate), 6)


def _primary_signal_weight(
    *,
    trust_tier: SignalTrustTier,
    quote_verified: bool,
    binding_ok: bool,
    freshness_ok: bool,
) -> float:
    quote_weight = 1.0 if quote_verified else 0.35
    binding_weight = 1.0 if binding_ok else 0.25
    freshness_weight = 1.0 if freshness_ok else 0.4
    return round(
        _trust_tier_weight(trust_tier) * quote_weight * binding_weight * freshness_weight,
        6,
    )


def _source_quality_summary(
    *,
    observation_packet: AutoTraderObservationPacket | None,
    history_source_stats: Mapping[str, Any] | None = None,
) -> list[AutoTraderSourceQualityRow]:
    if observation_packet is None:
        return []
    source_history_rows = _load_source_history_rows(history_source_stats)
    registry = observation_packet.signal_source_registry
    out: list[AutoTraderSourceQualityRow] = []
    for signal in observation_packet.external_signals:
        entry = registry.get(signal.source_id) if registry is not None else None
        history = source_history_rows.get(signal.source_id, {})
        history_total = max(0, int(history.get("total", 0))) if isinstance(history, Mapping) else 0
        history_submit = max(0, min(history_total, int(history.get("submit", 0)))) if isinstance(history, Mapping) else 0
        history_reject = max(0, min(history_total, int(history.get("reject", 0)))) if isinstance(history, Mapping) else 0
        history_skip = max(0, min(history_total, int(history.get("skip", 0)))) if isinstance(history, Mapping) else 0
        history_submit_rate = (
            float(history.get("submit_rate", float(history_submit) / float(history_total)))
            if history_total > 0 and isinstance(history, Mapping)
            else 0.0
        )
        low_reliability = history_total >= 2 and history_submit_rate < 0.5
        trust_tier_weight = _trust_tier_weight(signal.trust_tier)
        registry_weight = 1.0 if entry is not None else 0.6
        auth_required = bool(entry.require_auth) if entry is not None else False
        freshness_required = bool(entry.require_freshness) if entry is not None else False
        auth_weight = 1.0 if signal.auth_ok else (0.0 if auth_required else 0.85)
        freshness_weight = 1.0 if signal.freshness_ok else (0.0 if freshness_required else 0.85)
        history_weight = _history_submit_weight(
            history_total=history_total,
            history_submit_rate=history_submit_rate,
        )
        effective_weight = round(
            trust_tier_weight * registry_weight * auth_weight * freshness_weight * history_weight,
            6,
        )
        out.append(
            {
                "source_id": signal.source_id,
                "source_kind": signal.source_kind.value,
                "trust_tier": signal.trust_tier.value,
                "advisory_only": bool(signal.advisory_only),
                "auth_ok": bool(signal.auth_ok),
                "freshness_ok": bool(signal.freshness_ok),
                "registered": bool(entry is not None),
                "registry_requires_auth": auth_required,
                "registry_requires_freshness": freshness_required,
                "registry_allowed_trust_tiers": (
                    [tier.value for tier in entry.allowed_trust_tiers] if entry is not None else []
                ),
                "history_total": int(history_total),
                "history_submit": int(history_submit),
                "history_reject": int(history_reject),
                "history_skip": int(history_skip),
                "history_submit_rate": round(float(history_submit_rate), 6),
                "trust_tier_weight": round(trust_tier_weight, 6),
                "registry_weight": round(registry_weight, 6),
                "auth_weight": round(auth_weight, 6),
                "freshness_weight": round(freshness_weight, 6),
                "history_weight": round(history_weight, 6),
                "effective_weight": effective_weight,
                "low_reliability": bool(low_reliability),
                "unseen_history": bool(history_total == 0),
            }
        )
    return out


def _observation_summary(
    *,
    strategy: StrategyIR,
    observation_packet: AutoTraderObservationPacket | None,
    history_source_stats: Mapping[str, Any] | None = None,
) -> AutoTraderObservationSummary | None:
    if observation_packet is None:
        return None
    primary_signal = observation_packet.primary_signal
    primary_age_epochs = observation_packet.current_epoch - primary_signal.quote_epoch
    primary_freshness_ok = (
        primary_age_epochs >= 0
        and primary_age_epochs <= strategy.risk_limits.max_oracle_staleness_epochs
    )
    trusted_external_signal_count = observation_packet.trusted_external_count()
    trusted_signal_count = int(observation_packet.trusted_primary()) + int(trusted_external_signal_count)
    advisory_external_signal_count = observation_packet.advisory_external_count()
    advisory_signal_count = int(primary_signal.trust_tier is SignalTrustTier.ADVISORY) + advisory_external_signal_count
    source_quality = _source_quality_summary(
        observation_packet=observation_packet,
        history_source_stats=history_source_stats,
    )
    primary_weighted_trust_score = _primary_signal_weight(
        trust_tier=primary_signal.trust_tier,
        quote_verified=bool(primary_signal.quote_receipt_verified),
        binding_ok=bool(primary_signal.binding_ok),
        freshness_ok=bool(primary_freshness_ok),
    )
    weighted_external_signal_score = round(
        sum(float(row["effective_weight"]) for row in source_quality),
        6,
    )
    weighted_trusted_signal_score = round(
        primary_weighted_trust_score + weighted_external_signal_score,
        6,
    )
    return {
        "current_epoch": int(observation_packet.current_epoch),
        "primary_source_kind": primary_signal.source_kind.value,
        "primary_trust_tier": primary_signal.trust_tier.value,
        "primary_quote_verified": bool(primary_signal.quote_receipt_verified),
        "primary_binding_ok": bool(primary_signal.binding_ok),
        "primary_age_epochs": int(primary_age_epochs),
        "primary_freshness_ok": bool(primary_freshness_ok),
        "primary_weighted_trust_score": primary_weighted_trust_score,
        "trusted_signal_count": int(trusted_signal_count),
        "advisory_signal_count": int(advisory_signal_count),
        "external_signal_count": int(len(observation_packet.external_signals)),
        "trusted_external_signal_count": int(trusted_external_signal_count),
        "advisory_external_signal_count": int(advisory_external_signal_count),
        "weighted_trusted_signal_score": weighted_trusted_signal_score,
        "weighted_external_signal_score": weighted_external_signal_score,
        "source_registry_present": bool(observation_packet.signal_source_registry is not None),
        "registered_external_signal_count": (
            int(len(observation_packet.external_signals))
            if observation_packet.signal_source_registry is not None
            else 0
        ),
        "source_history_present": bool(any(row["history_total"] > 0 for row in source_quality)),
        "source_history_available_count": int(sum(1 for row in source_quality if row["history_total"] > 0)),
        "low_reliability_external_count": int(sum(1 for row in source_quality if row["low_reliability"])),
        "unseen_external_count": int(sum(1 for row in source_quality if row["unseen_history"])),
        "wallet_capability_present": bool(observation_packet.wallet_capability is not None),
        "tau_enabled": bool(observation_packet.tau_enabled),
    }


def _clamp_unit_interval(value: object) -> float:
    if isinstance(value, bool):
        out = float(int(value))
    elif isinstance(value, (int, float)):
        out = float(value)
    elif isinstance(value, str):
        try:
            out = float(value)
        except ValueError:
            return 0.0
    else:
        return 0.0
    if out < 0.0:
        return 0.0
    if out > 1.0:
        return 1.0
    return out


def _advisory_risk_flags(
    *,
    observation_summary: AutoTraderObservationSummary | None,
    route_risk_summary: AutoTraderRouteRiskSummary | None = None,
    surface_support_summary: AutoTraderSurfaceSupportSummary | None = None,
) -> list[str]:
    flags: list[str] = []
    if surface_support_summary is not None and not surface_support_summary["current_phase_supported"]:
        flags.append("surface_phase_unsupported")
    if observation_summary is not None:
        if observation_summary["trusted_signal_count"] == 0:
            flags.append("no_trusted_signals")
        if observation_summary["primary_trust_tier"] == SignalTrustTier.ADVISORY.value:
            flags.append("advisory_primary_signal")
        if not observation_summary["primary_quote_verified"]:
            flags.append("primary_quote_unverified")
        if not observation_summary["primary_binding_ok"]:
            flags.append("primary_binding_failed")
        if not observation_summary["primary_freshness_ok"]:
            flags.append("primary_signal_stale")
        if observation_summary["external_signal_count"] > 0 and not observation_summary["source_registry_present"]:
            flags.append("external_sources_unregistered")
        if observation_summary["advisory_external_signal_count"] > 0:
            flags.append("advisory_external_present")
        if observation_summary["weighted_external_signal_score"] < 0.4 and observation_summary["external_signal_count"] > 0:
            flags.append("weak_weighted_external_support")
        if observation_summary["low_reliability_external_count"] > 0:
            flags.append("low_reliability_external_present")
        if observation_summary["unseen_external_count"] > 0:
            flags.append("unseen_external_present")
    if route_risk_summary is not None:
        if not route_risk_summary["receipt_verified"]:
            flags.append("route_receipt_unverified")
        if not route_risk_summary["route_shape_supported_for_intents"]:
            flags.append("route_shape_unsupported")
        if route_risk_summary["multi_hop_present"]:
            flags.append("route_multi_hop_present")
        if route_risk_summary["extreme_input_stress_present"]:
            flags.append("route_extreme_input_stress")
        if route_risk_summary["extreme_output_depletion_present"]:
            flags.append("route_extreme_output_depletion")
        if route_risk_summary["extreme_price_impact_present"]:
            flags.append("route_extreme_price_impact")
    return flags


def _advisory_confidence_cap(
    *,
    observation_summary: AutoTraderObservationSummary | None,
    route_risk_summary: AutoTraderRouteRiskSummary | None = None,
    surface_support_summary: AutoTraderSurfaceSupportSummary | None = None,
) -> float:
    cap = 1.0
    if surface_support_summary is not None and not surface_support_summary["current_phase_supported"]:
        cap = min(cap, 0.05)
    if observation_summary is not None:
        if observation_summary["trusted_signal_count"] == 0:
            cap = min(cap, 0.25)
        if observation_summary["primary_trust_tier"] == SignalTrustTier.ADVISORY.value:
            cap = min(cap, 0.25)
        if not observation_summary["primary_quote_verified"]:
            cap = min(cap, 0.25)
        if not observation_summary["primary_binding_ok"]:
            cap = min(cap, 0.25)
        if not observation_summary["primary_freshness_ok"]:
            cap = min(cap, 0.35)
        if observation_summary["external_signal_count"] > 0 and not observation_summary["source_registry_present"]:
            cap = min(cap, 0.5)
        if observation_summary["external_signal_count"] > 0 and observation_summary["weighted_external_signal_score"] < 0.4:
            cap = min(cap, 0.45)
        if observation_summary["low_reliability_external_count"] > 0:
            cap = min(cap, 0.55)
        if observation_summary["unseen_external_count"] > 0:
            cap = min(cap, 0.65)
        if observation_summary["advisory_external_signal_count"] > 0:
            cap = min(cap, 0.75)
    if route_risk_summary is not None:
        if not route_risk_summary["receipt_verified"]:
            cap = min(cap, 0.25)
        if not route_risk_summary["route_shape_supported_for_intents"]:
            cap = min(cap, 0.15)
        if route_risk_summary["extreme_input_stress_present"]:
            cap = min(cap, 0.2)
        if route_risk_summary["extreme_output_depletion_present"]:
            cap = min(cap, 0.2)
        if route_risk_summary["extreme_price_impact_present"]:
            cap = min(cap, 0.25)
    return cap


def autotrader_krr_semantic_signature(
    *,
    strategy: StrategyIR,
    phase: AutoTraderKRRPhase,
    current_epoch: int,
    source_form: str | None = None,
    source_preset_id: str | None = None,
    spent_in_window: int = 0,
    lifetime_spent: int = 0,
    live_orders: int = 0,
    nonce_start: int | None = None,
    tau_enabled: bool = False,
    observation_packet: AutoTraderObservationPacket | None = None,
    route_risk_summary: AutoTraderRouteRiskSummary | None = None,
    history_source_stats: Mapping[str, Any] | None = None,
) -> str:
    authoring_summary = _authoring_summary(
        strategy=strategy,
        source_form=source_form,
        source_preset_id=source_preset_id,
    )
    surface_support_summary = _surface_support_summary(strategy=strategy, phase=phase)
    pieces = [
        f"phase={phase}",
        f"template={strategy.template.value}",
        f"backend={strategy.policy_backend.value}",
        f"actions={','.join(action.value for action in strategy.allowed_actions)}",
        f"assets={','.join(strategy.asset_universe)}",
        f"require_quote_receipts={int(strategy.risk_limits.require_quote_receipts)}",
        f"max_slippage_bps={strategy.risk_limits.max_slippage_bps}",
        f"max_oracle_staleness_epochs={strategy.risk_limits.max_oracle_staleness_epochs}",
        f"valid_from_epoch={strategy.strategy_window.valid_from_epoch}",
        f"valid_until_epoch={strategy.strategy_window.valid_until_epoch}",
        f"min_order_spacing_epochs={strategy.strategy_window.min_order_spacing_epochs}",
        f"kill_switch_enabled={int(strategy.controls.kill_switch_enabled)}",
        f"max_live_orders={strategy.controls.max_live_orders}",
        f"per_order_max={strategy.notional_caps.per_order_max}",
        f"per_window_max={strategy.notional_caps.per_window_max}",
        f"lifetime_max={strategy.notional_caps.lifetime_max}",
        f"current_epoch={current_epoch}",
        f"spent_in_window={spent_in_window}",
        f"lifetime_spent={lifetime_spent}",
        f"live_orders={live_orders}",
        f"budget_pressure={int((spent_in_window * 10 >= strategy.notional_caps.per_window_max * 8) or (lifetime_spent * 10 >= strategy.notional_caps.lifetime_max * 8))}",
        f"live_order_pressure={int(live_orders + 1 >= strategy.controls.max_live_orders)}",
        f"tau_enabled={int(tau_enabled)}",
        f"authored_via_user_bundle={int(authoring_summary['authored_via_user_bundle'])}",
        f"authoring_mode={authoring_summary['authoring_mode']}",
        f"surface_overall_status={surface_support_summary['overall_status']}",
        f"surface_current_phase_supported={int(surface_support_summary['current_phase_supported'])}",
        f"surface_current_phase_status={surface_support_summary['current_phase_status']}",
    ]
    summary = _observation_summary(
        strategy=strategy,
        observation_packet=observation_packet,
        history_source_stats=history_source_stats,
    )
    if summary is None:
        pieces.append("observation_packet=0")
    else:
        external_advisory_count = int(summary["advisory_external_signal_count"] > 0)
        external_trusted_count = int(summary["trusted_external_signal_count"] > 0)
        pieces.extend(
            [
                "observation_packet=1",
                f"primary_source_kind={summary['primary_source_kind']}",
                f"primary_trust_tier={summary['primary_trust_tier']}",
                f"primary_quote_verified={int(bool(summary['primary_quote_verified']))}",
                f"primary_binding_ok={int(bool(summary['primary_binding_ok']))}",
                f"primary_age_epochs={summary['primary_age_epochs']}",
                f"primary_freshness_ok={int(bool(summary['primary_freshness_ok']))}",
                f"trusted_signal_count={summary['trusted_signal_count']}",
                f"external_advisory_count={external_advisory_count}",
                f"external_trusted_count={external_trusted_count}",
                f"source_registry_present={int(bool(summary['source_registry_present']))}",
                f"source_history_present={int(bool(summary['source_history_present']))}",
                f"low_reliability_external_present={int(summary['low_reliability_external_count'] > 0)}",
                f"unseen_external_present={int(summary['unseen_external_count'] > 0)}",
                f"wallet_capability_present={int(bool(summary['wallet_capability_present']))}",
            ]
        )
    if route_risk_summary is None:
        pieces.append("route_risk_present=0")
    else:
        pieces.extend(
            [
                "route_risk_present=1",
                f"route_receipt_verified={int(bool(route_risk_summary['receipt_verified']))}",
                f"route_leg_count={route_risk_summary['leg_count']}",
                f"route_hop_count={route_risk_summary['hop_count']}",
                f"route_multi_hop_present={int(bool(route_risk_summary['multi_hop_present']))}",
                f"route_shape_supported={int(bool(route_risk_summary['route_shape_supported_for_intents']))}",
                f"route_extreme_input_stress={int(bool(route_risk_summary['extreme_input_stress_present']))}",
                f"route_extreme_output_depletion={int(bool(route_risk_summary['extreme_output_depletion_present']))}",
                f"route_extreme_price_impact={int(bool(route_risk_summary['extreme_price_impact_present']))}",
                f"route_max_hop_input_vs_reserve_bps={route_risk_summary['max_hop_input_vs_reserve_bps']}",
                f"route_max_hop_output_vs_reserve_bps={route_risk_summary['max_hop_output_vs_reserve_bps']}",
                f"route_max_hop_price_impact_bps={route_risk_summary['max_hop_price_impact_bps']}",
            ]
        )
    if source_form:
        pieces.append(f"source_form={source_form}")
    if source_preset_id:
        pieces.append(f"source_preset_id={source_preset_id}")
    if nonce_start is not None:
        pieces.append(f"nonce_start={nonce_start}")
    for key in sorted(strategy.template_params):
        pieces.append(f"param_{key}={strategy.template_params[key]}")
    return "|".join(pieces)


def advise_autotrader_krr(
    *,
    strategy: StrategyIR,
    phase: AutoTraderKRRPhase,
    current_epoch: int,
    backend: str = AUTOTRADER_KRR_DEFAULT_BACKEND,
    kb_path: str | None = None,
    kb: Mapping[str, Any] | None = None,
    history_check_stats: Mapping[str, object] | None = None,
    source_form: str | None = None,
    source_preset_id: str | None = None,
    spent_in_window: int = 0,
    lifetime_spent: int = 0,
    live_orders: int = 0,
    nonce_start: int | None = None,
    tau_enabled: bool = False,
    observation_packet: AutoTraderObservationPacket | None = None,
    quote_receipt: Mapping[str, Any] | None = None,
    pools_by_id: Mapping[str, PoolState] | None = None,
) -> dict[str, Any] | None:
    if backend == "off":
        return None
    from tools.krr_reasoner_engine import advise_candidate_krr, load_krr_kb, normalize_krr_kb_object

    operator_id = f"autotrader_{strategy.template.value}_{phase}_v1"
    source_history = _load_source_history_rows(history_check_stats)
    route_risk_summary = _build_route_risk_summary(
        quote_receipt=quote_receipt,
        pools_by_id=pools_by_id,
    )
    surface_support_summary = _surface_support_summary(strategy=strategy, phase=phase)
    semantic_signature = autotrader_krr_semantic_signature(
        strategy=strategy,
        phase=phase,
        current_epoch=current_epoch,
        source_form=source_form,
        source_preset_id=source_preset_id,
        spent_in_window=spent_in_window,
        lifetime_spent=lifetime_spent,
        live_orders=live_orders,
        nonce_start=nonce_start,
        tau_enabled=tau_enabled,
        observation_packet=observation_packet,
        route_risk_summary=route_risk_summary,
        history_source_stats=history_check_stats,
    )
    candidate_checks = autotrader_krr_check_options(
        strategy=strategy,
        phase=phase,
        tau_enabled=tau_enabled,
        observation_packet=observation_packet,
        route_risk_summary=route_risk_summary,
        history_source_stats=history_check_stats,
        surface_support_summary=surface_support_summary,
    )
    loaded_kb = (
        normalize_krr_kb_object(kb, kb_path=kb_path)
        if isinstance(kb, Mapping)
        else load_krr_kb(kb_path)
    )
    kb = _merge_autotrader_krr_defaults(loaded_kb)
    history = _load_history_check_rows(history_check_stats)
    advice = advise_candidate_krr(
        operator_id=operator_id,
        schema=AUTOTRADER_KRR_SCHEMA,
        semantic_signature=semantic_signature,
        check_options=candidate_checks,
        history_check_stats=history,
        kb=kb,
        backend=backend,
    )
    authoring_summary = _authoring_summary(
        strategy=strategy,
        source_form=source_form,
        source_preset_id=source_preset_id,
    )
    observation_summary = _observation_summary(
        strategy=strategy,
        observation_packet=observation_packet,
        history_source_stats=history_check_stats,
    )
    source_quality_summary = _source_quality_summary(
        observation_packet=observation_packet,
        history_source_stats=history_check_stats,
    )
    out = dict(advice)
    ranking_confidence = _clamp_unit_interval(out.get("confidence", 0.0))
    confidence_cap = _advisory_confidence_cap(
        observation_summary=observation_summary,
        route_risk_summary=route_risk_summary,
        surface_support_summary=surface_support_summary,
    )
    effective_confidence = min(ranking_confidence, confidence_cap)
    advisory_risk_flags = _advisory_risk_flags(
        observation_summary=observation_summary,
        route_risk_summary=route_risk_summary,
        surface_support_summary=surface_support_summary,
    )
    explain = list(out.get("explain", [])) if isinstance(out.get("explain"), list) else []
    if advisory_risk_flags:
        explain.append("risk_flags=" + ",".join(advisory_risk_flags))
    if effective_confidence < ranking_confidence:
        explain.append(f"confidence_cap={confidence_cap:.4f}")
    out["schema"] = AUTOTRADER_KRR_SCHEMA
    out["phase"] = str(phase)
    out["operator_id"] = operator_id
    out["candidate_checks"] = list(candidate_checks)
    out["semantic_signature"] = semantic_signature
    out["tau_enabled"] = bool(tau_enabled)
    out["confidence"] = effective_confidence
    out["ranking_confidence"] = ranking_confidence
    out["confidence_cap"] = confidence_cap
    out["advisory_risk_flags"] = advisory_risk_flags
    out["explain"] = explain
    out["observation_summary"] = observation_summary
    out["route_risk_summary"] = route_risk_summary
    out["surface_support_summary"] = surface_support_summary
    out["source_quality_summary"] = source_quality_summary
    out["authoring_summary"] = authoring_summary
    out["source_history_present"] = bool(source_history)
    return out
