"""Slippage and pokayoke handlers for the DEX dispatch registry.

These advisory endpoints operate on caller-supplied reserve snapshots and do
not read oracle prices. Reserve freshness is enforced by the upstream quote and
ledger witness paths that turn advisory output into value-moving actions.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Mapping

from src.core.pokayoke_swap_guardrails import (
    SwapGuardrailContext,
    build_swap_proofux_regret_decision,
    default_swap_proofux_minimax_policy,
    decide_swap_guardrails,
)
from src.core.pokayoke_swap_suggest import (
    suggest_amount_in_exact_in_cpmm,
    suggest_amount_in_for_impact_lt_bps,
    suggest_amount_in_for_required_slippage_le_bps,
)
from src.core.slippage_advisor import slippage_advice_exact_in_cpmm
from src.core.zeno_ux_certificate import (
    zeno_ux_minimax_regret_certificate_hash,
    zeno_ux_minimax_regret_certificate_to_payload,
)
from src.integration.api_server_dex_dispatch import (
    DexRequestContext,
    DexResponse,
    _register,
)

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)


@dataclass(frozen=True)
class _SuggestionInputs:
    reserve_in: int
    reserve_out: int
    amount_in: int
    fee_bps: int
    pending_same_dir: int
    confidence_bps: int
    user_slippage_bps: int | None
    max_option_bps: int | None


@dataclass(frozen=True)
class SwapExecutionRegretTauProjection:
    tau_step: Mapping[str, int]
    certificate_hash: str | None
    reason: str


@dataclass(frozen=True)
class SwapExecutionRegretTauBinding:
    schema: str
    binding_hash: str
    certificate_hash: str
    request_hash: str
    quote_snapshot_hash: str
    tau_fact_hash: str
    spec_id: str
    spec_path: str
    projection_reason: str


_SWAP_EXECUTION_REGRET_TAU_SLOTS: tuple[str, ...] = tuple(f"i{i}" for i in range(1, 13))
_SWAP_EXECUTION_REGRET_TAU_BINDING_SCHEMA = "zenodex.proofux.swap_execution_regret_tau_binding.v1"
_SWAP_EXECUTION_REGRET_TAU_SPEC_ID = "swap_execution_regret_guard_v1"
_SWAP_EXECUTION_REGRET_TAU_SPEC_PATH = "src/tau_specs/recommended/swap_execution_regret_guard_v1.tau"


def _coerce_int(value: Any, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{field} must be an int")
    return int(value)


def _optional_int(value: Any, field: str) -> int | None:
    if value is None:
        return None
    return _coerce_int(value, field)


def _slippage_options(raw_opts: Any, *, clamp_to_bps: bool) -> list[int] | None:
    if not isinstance(raw_opts, list):
        return None
    values: list[int] = []
    for raw_value in raw_opts:
        try:
            value = _coerce_int(raw_value, "slippage_options_bps[]")
        except BOUNDARY_DOMAIN_ERRORS:
            continue
        if clamp_to_bps and (value < 0 or value > 10_000):
            continue
        values.append(value)
    return values


def _canonical_json_bytes(value: Mapping[str, Any]) -> bytes:
    try:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise ValueError("binding payload must be canonical JSON-compatible") from exc


def _canonical_json_hash(value: Mapping[str, Any]) -> str:
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _require_sha256_hash(value: Any, *, field: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{field} must be a sha256 string")
    if len(value) != 71 or not value.startswith("sha256:"):
        raise ValueError(f"{field} must use sha256:<64 hex chars>")
    hex_part = value.removeprefix("sha256:")
    try:
        int(hex_part, 16)
    except ValueError as exc:
        raise ValueError(f"{field} must use sha256:<64 hex chars>") from exc
    return value


def _normalize_tau_step(tau_step: Mapping[str, int]) -> Mapping[str, int]:
    if not isinstance(tau_step, Mapping):
        raise TypeError("tau_step must be a mapping")
    normalized: dict[str, int] = {}
    for slot in _SWAP_EXECUTION_REGRET_TAU_SLOTS:
        raw = tau_step.get(slot)
        if isinstance(raw, bool) or not isinstance(raw, int):
            raise TypeError(f"{slot} must be int 0 or 1")
        if raw not in (0, 1):
            raise ValueError(f"{slot} must be 0 or 1")
        normalized[slot] = int(raw)
    if set(tau_step) != set(_SWAP_EXECUTION_REGRET_TAU_SLOTS):
        raise ValueError("tau_step must contain exactly i1..i12")
    return normalized


def _sbf_flag(value: bool) -> int:
    if not isinstance(value, bool):
        raise TypeError("Tau projection flags must be bool")
    return 1 if value else 0


def _zero_swap_execution_regret_tau_projection(reason: str) -> SwapExecutionRegretTauProjection:
    return SwapExecutionRegretTauProjection(
        tau_step={slot: 0 for slot in _SWAP_EXECUTION_REGRET_TAU_SLOTS},
        certificate_hash=None,
        reason=reason,
    )


def project_swap_execution_regret_tau_facts(
    pokayoke_payload: Mapping[str, Any],
    *,
    impact_within_limit_ok: bool,
    quote_age_within_limit_ok: bool,
    hop_count_within_limit_ok: bool,
    route_cert_ok: bool,
    oracle_fresh_ok: bool,
    not_expired_ok: bool,
    require_route_cert: bool,
    require_oracle_fresh: bool,
    require_not_expired: bool,
    proof_ok: bool,
    binding_ok: bool,
) -> SwapExecutionRegretTauProjection:
    """Project ProofUX swap regret evidence into `swap_execution_regret_guard_v1`.

    Missing or malformed ProofUX evidence projects to all-zero Tau facts, so
    the Tau guard fails closed rather than inferring a missing regret witness.
    """
    if not isinstance(pokayoke_payload, Mapping):
        return _zero_swap_execution_regret_tau_projection("missing_pokayoke_payload")
    proofux = pokayoke_payload.get("proofux")
    if not isinstance(proofux, Mapping):
        return _zero_swap_execution_regret_tau_projection("missing_proofux_payload")
    certificate_hash = proofux.get("minimax_certificate_hash")
    if not isinstance(certificate_hash, str) or not certificate_hash.startswith("sha256:"):
        return _zero_swap_execution_regret_tau_projection("missing_minimax_certificate_hash")
    regret_ok = proofux.get("regret_within_limit_ok")
    if not isinstance(regret_ok, bool):
        return _zero_swap_execution_regret_tau_projection("malformed_regret_flag")

    tau_step = {
        "i1": _sbf_flag(regret_ok),
        "i2": _sbf_flag(impact_within_limit_ok),
        "i3": _sbf_flag(quote_age_within_limit_ok),
        "i4": _sbf_flag(hop_count_within_limit_ok),
        "i5": _sbf_flag(route_cert_ok),
        "i6": _sbf_flag(oracle_fresh_ok),
        "i7": _sbf_flag(not_expired_ok),
        "i8": _sbf_flag(require_route_cert),
        "i9": _sbf_flag(require_oracle_fresh),
        "i10": _sbf_flag(require_not_expired),
        "i11": _sbf_flag(proof_ok),
        "i12": _sbf_flag(binding_ok),
    }
    reason = "ok" if regret_ok else "regret_outside_limit"
    return SwapExecutionRegretTauProjection(
        tau_step=tau_step,
        certificate_hash=certificate_hash,
        reason=reason,
    )


def swap_execution_regret_tau_binding_to_payload(
    binding: SwapExecutionRegretTauBinding,
) -> Mapping[str, Any]:
    return {
        "schema": binding.schema,
        "binding_hash": binding.binding_hash,
        "certificate_hash": binding.certificate_hash,
        "request_hash": binding.request_hash,
        "quote_snapshot_hash": binding.quote_snapshot_hash,
        "tau_fact_hash": binding.tau_fact_hash,
        "spec_id": binding.spec_id,
        "spec_path": binding.spec_path,
        "projection_reason": binding.projection_reason,
    }


def build_swap_execution_regret_tau_binding(
    *,
    request_snapshot: Mapping[str, Any],
    quote_snapshot: Mapping[str, Any],
    projection: SwapExecutionRegretTauProjection,
) -> SwapExecutionRegretTauBinding:
    """Bind ProofUX certificate hash, request, quote snapshot, and Tau facts."""
    certificate_hash = _require_sha256_hash(projection.certificate_hash, field="certificate_hash")
    tau_step = _normalize_tau_step(projection.tau_step)
    request_hash = _canonical_json_hash(
        {
            "schema": "zenodex.proofux.swap_execution_request_snapshot.v1",
            "request": dict(request_snapshot),
        }
    )
    quote_snapshot_hash = _canonical_json_hash(
        {
            "schema": "zenodex.proofux.swap_execution_quote_snapshot.v1",
            "quote_snapshot": dict(quote_snapshot),
        }
    )
    tau_fact_hash = _canonical_json_hash(
        {
            "schema": "zenodex.proofux.swap_execution_tau_facts.v1",
            "spec_id": _SWAP_EXECUTION_REGRET_TAU_SPEC_ID,
            "spec_path": _SWAP_EXECUTION_REGRET_TAU_SPEC_PATH,
            "tau_step": tau_step,
        }
    )
    unsigned_payload = {
        "schema": _SWAP_EXECUTION_REGRET_TAU_BINDING_SCHEMA,
        "certificate_hash": certificate_hash,
        "projection_reason": str(projection.reason),
        "quote_snapshot_hash": quote_snapshot_hash,
        "request_hash": request_hash,
        "spec_id": _SWAP_EXECUTION_REGRET_TAU_SPEC_ID,
        "spec_path": _SWAP_EXECUTION_REGRET_TAU_SPEC_PATH,
        "tau_fact_hash": tau_fact_hash,
    }
    return SwapExecutionRegretTauBinding(
        schema=_SWAP_EXECUTION_REGRET_TAU_BINDING_SCHEMA,
        binding_hash=_canonical_json_hash(unsigned_payload),
        certificate_hash=certificate_hash,
        request_hash=request_hash,
        quote_snapshot_hash=quote_snapshot_hash,
        tau_fact_hash=tau_fact_hash,
        spec_id=_SWAP_EXECUTION_REGRET_TAU_SPEC_ID,
        spec_path=_SWAP_EXECUTION_REGRET_TAU_SPEC_PATH,
        projection_reason=str(projection.reason),
    )


def verify_swap_execution_regret_tau_binding(
    binding_payload: Mapping[str, Any],
    *,
    request_snapshot: Mapping[str, Any],
    quote_snapshot: Mapping[str, Any],
    projection: SwapExecutionRegretTauProjection,
) -> bool:
    if not isinstance(binding_payload, Mapping):
        return False
    try:
        expected = swap_execution_regret_tau_binding_to_payload(
            build_swap_execution_regret_tau_binding(
                request_snapshot=request_snapshot,
                quote_snapshot=quote_snapshot,
                projection=projection,
            )
        )
    except (TypeError, ValueError):
        return False
    return dict(binding_payload) == dict(expected)


def _proofux_payload_from_decision(decision: Any) -> Mapping[str, Any]:
    certificate = decision.minimax_certificate
    return {
        "selected_action": str(decision.selected_action),
        "legacy_action": str(decision.legacy_action),
        "regret_within_limit_ok": bool(decision.regret_within_limit_ok),
        "inaction_regret_bps": int(decision.inaction_regret_bps),
        "candidate_ids": [str(item) for item in decision.candidate_ids],
        "minimax_certificate": zeno_ux_minimax_regret_certificate_to_payload(certificate),
        "minimax_certificate_hash": zeno_ux_minimax_regret_certificate_hash(certificate),
    }


def _guardrail_payload_from_advice(
    advice: Any,
    user_slippage_bps: int,
    *,
    inaction_regret_bps: int | None = None,
    proofux_max_value_loss_bps: int | None = None,
    proofux_max_mev_exposure_bps: int | None = None,
    proofux_max_capital_at_risk_bps: int | None = None,
) -> dict[str, Any]:
    inner_ctx = SwapGuardrailContext(
        price_impact_bps=int(advice.price_impact_bps),
        slippage_advice_status=str(advice.status),
        required_slippage_bps=int(advice.required_slippage_bps),
        recommended_slippage_bps_revert_safe=(
            int(advice.recommended_slippage_bps_revert_safe)
            if advice.recommended_slippage_bps_revert_safe is not None
            else None
        ),
        recommended_slippage_bps_mev_safe=(
            int(advice.recommended_slippage_bps_mev_safe)
            if advice.recommended_slippage_bps_mev_safe is not None
            else None
        ),
        recommended_slippage_bps=(
            int(advice.recommended_slippage_bps)
            if advice.recommended_slippage_bps is not None
            else None
        ),
    )
    decision = decide_swap_guardrails(ctx=inner_ctx, user_slippage_bps=user_slippage_bps)
    proofux = None
    if inaction_regret_bps is not None:
        proofux_policy = default_swap_proofux_minimax_policy(
            max_value_loss_bps=proofux_max_value_loss_bps,
            max_mev_exposure_bps=proofux_max_mev_exposure_bps,
            max_capital_at_risk_bps=proofux_max_capital_at_risk_bps,
        )
        proofux = _proofux_payload_from_decision(
            build_swap_proofux_regret_decision(
                ctx=inner_ctx,
                user_slippage_bps=user_slippage_bps,
                inaction_regret_bps=inaction_regret_bps,
                policy=proofux_policy,
            )
        )
    return {
        "action": str(decision.action),
        "reasons": list(decision.reasons),
        "messages": list(decision.messages),
        "typed_confirm_phrase": decision.typed_confirm_phrase,
        "proofux": proofux,
    }


def _slippage_option_payload(option: Any) -> dict[str, Any]:
    return {
        "slippage_bps": int(option.slippage_bps),
        "min_amount_out": int(option.min_amount_out),
        "is_revert_safe_at_confidence": bool(option.is_revert_safe_at_confidence),
        "sandwich_status": str(option.sandwich_status),
        "sandwich_max_profit": int(option.sandwich_max_profit),
        "sandwich_attacker_amount_in": int(option.sandwich_attacker_amount_in),
        "sandwich_victim_amount_out": int(option.sandwich_victim_amount_out),
        "sandwich_scanned_max_attacker_amount_in": int(option.sandwich_scanned_max_attacker_amount_in),
    }


def _slippage_advice_payload(advice: Any, pokayoke: dict[str, Any] | None) -> dict[str, Any]:
    return {
        "best_amount_out": int(advice.best_amount_out),
        "price_impact_bps": int(advice.price_impact_bps),
        "amount_out_at_confidence": int(advice.amount_out_at_confidence),
        "pending_volume_at_confidence": int(advice.pending_volume_at_confidence),
        "confidence_bps": int(advice.confidence_bps),
        "required_slippage_bps": int(advice.required_slippage_bps),
        "recommended_slippage_bps_revert_safe": (
            int(advice.recommended_slippage_bps_revert_safe)
            if advice.recommended_slippage_bps_revert_safe is not None
            else None
        ),
        "recommended_slippage_bps_mev_safe": (
            int(advice.recommended_slippage_bps_mev_safe)
            if advice.recommended_slippage_bps_mev_safe is not None
            else None
        ),
        "recommended_slippage_bps": (
            int(advice.recommended_slippage_bps)
            if advice.recommended_slippage_bps is not None
            else None
        ),
        "status": str(advice.status),
        "pokayoke": pokayoke,
        "options": [_slippage_option_payload(option) for option in advice.options],
    }


def _handle_slippage_advice(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        reserve_in = _coerce_int(obj.get("reserve_in", 0), "reserve_in")
        reserve_out = _coerce_int(obj.get("reserve_out", 0), "reserve_out")
        amount_in = _coerce_int(obj.get("amount_in", 0), "amount_in")
        fee_bps = _coerce_int(obj.get("fee_bps", 0), "fee_bps")
        pending_same_dir = _coerce_int(
            obj.get("pending_volume_same_direction", 0), "pending_volume_same_direction"
        )
        confidence_bps = _coerce_int(obj.get("confidence_bps", 9500), "confidence_bps")
        max_attacker_amount_in = _coerce_int(
            obj.get("max_attacker_amount_in", 5000), "max_attacker_amount_in"
        )
        user_slippage_bps = _optional_int(obj.get("user_slippage_bps", None), "user_slippage_bps")
        inaction_regret_bps = _optional_int(obj.get("inaction_regret_bps", None), "inaction_regret_bps")
        proofux_max_value_loss_bps = _optional_int(
            obj.get("proofux_max_value_loss_bps", None),
            "proofux_max_value_loss_bps",
        )
        proofux_max_mev_exposure_bps = _optional_int(
            obj.get("proofux_max_mev_exposure_bps", None),
            "proofux_max_mev_exposure_bps",
        )
        proofux_max_capital_at_risk_bps = _optional_int(
            obj.get("proofux_max_capital_at_risk_bps", None),
            "proofux_max_capital_at_risk_bps",
        )
        slippage_options_bps = _slippage_options(obj.get("slippage_options_bps"), clamp_to_bps=False)

        advice = slippage_advice_exact_in_cpmm(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            amount_in=amount_in,
            pending_volume_same_direction=pending_same_dir,
            confidence_bps=confidence_bps,
            slippage_options_bps=slippage_options_bps,
            max_attacker_amount_in=max_attacker_amount_in,
        )
        pokayoke = (
            _guardrail_payload_from_advice(
                advice,
                user_slippage_bps,
                inaction_regret_bps=inaction_regret_bps,
                proofux_max_value_loss_bps=proofux_max_value_loss_bps,
                proofux_max_mev_exposure_bps=proofux_max_mev_exposure_bps,
                proofux_max_capital_at_risk_bps=proofux_max_capital_at_risk_bps,
            )
            if user_slippage_bps is not None
            else None
        )
        return 200, {"ok": True, "advice": _slippage_advice_payload(advice, pokayoke)}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "slippage_advice_error", "details": "request failed"}


def _simple_suggestion_payload(suggestion: Any) -> dict[str, Any] | None:
    if suggestion is None:
        return None
    return {
        "kind": str(suggestion.kind),
        "target_bps": int(suggestion.target_bps),
        "suggested_amount_in": (
            int(suggestion.suggested_amount_in)
            if suggestion.suggested_amount_in is not None
            else None
        ),
        "status": str(suggestion.status),
        "eval_count": int(suggestion.eval_count),
        "baseline_value_bps": int(suggestion.baseline_value_bps),
        "suggested_value_bps": (
            int(suggestion.suggested_value_bps)
            if suggestion.suggested_value_bps is not None
            else None
        ),
    }


def _parse_suggestion_inputs(obj: Mapping[str, Any]) -> _SuggestionInputs:
    opts = _slippage_options(obj.get("slippage_options_bps"), clamp_to_bps=True) or []
    return _SuggestionInputs(
        reserve_in=_coerce_int(obj.get("reserve_in", 0), "reserve_in"),
        reserve_out=_coerce_int(obj.get("reserve_out", 0), "reserve_out"),
        amount_in=_coerce_int(obj.get("amount_in", 0), "amount_in"),
        fee_bps=_coerce_int(obj.get("fee_bps", 0), "fee_bps"),
        pending_same_dir=_coerce_int(
            obj.get("pending_volume_same_direction", 0), "pending_volume_same_direction"
        ),
        confidence_bps=_coerce_int(obj.get("confidence_bps", 9500), "confidence_bps"),
        user_slippage_bps=_optional_int(obj.get("user_slippage_bps", None), "user_slippage_bps"),
        max_option_bps=max(opts) if opts else None,
    )


def _impact_suggestion(inputs: _SuggestionInputs, *, target_impact_bps: int) -> Any:
    return suggest_amount_in_for_impact_lt_bps(
        reserve_in=inputs.reserve_in,
        reserve_out=inputs.reserve_out,
        fee_bps=inputs.fee_bps,
        amount_in=inputs.amount_in,
        target_impact_bps=target_impact_bps,
        window=256,
    )


def _required_slippage_suggestion(inputs: _SuggestionInputs, target_bps: int | None) -> Any:
    if target_bps is None:
        return None
    return suggest_amount_in_for_required_slippage_le_bps(
        reserve_in=inputs.reserve_in,
        reserve_out=inputs.reserve_out,
        fee_bps=inputs.fee_bps,
        amount_in=inputs.amount_in,
        pending_volume_same_direction=inputs.pending_same_dir,
        confidence_bps=inputs.confidence_bps,
        target_required_slippage_bps=target_bps,
        window=256,
    )


def _handle_pokayoke_swap_suggest(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        inputs = _parse_suggestion_inputs(obj)
        return 200, {
            "ok": True,
            "suggestions": {
                "impact_lt_500_bps": _simple_suggestion_payload(
                    _impact_suggestion(inputs, target_impact_bps=500)
                ),
                "impact_lt_100_bps": _simple_suggestion_payload(
                    _impact_suggestion(inputs, target_impact_bps=100)
                ),
                "required_slippage_le_user_bps": _simple_suggestion_payload(
                    _required_slippage_suggestion(inputs, inputs.user_slippage_bps)
                ),
                "required_slippage_le_max_option_bps": _simple_suggestion_payload(
                    _required_slippage_suggestion(inputs, inputs.max_option_bps)
                ),
            },
        }
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"}


def _target_actions(raw_targets: Any) -> tuple[str, ...]:
    if not isinstance(raw_targets, list):
        return ("confirm", "allow")
    cleaned: list[str] = []
    for raw_target in raw_targets:
        target = str(raw_target or "").strip().lower()
        if target in {"confirm", "allow"} and target not in cleaned:
            cleaned.append(target)
    return tuple(cleaned) if cleaned else ("confirm", "allow")


def _heavy_suggestion_payload(suggestion: Any) -> dict[str, Any]:
    return {
        "target_action": str(suggestion.target_action),
        "suggested_amount_in": (
            int(suggestion.suggested_amount_in)
            if suggestion.suggested_amount_in is not None
            else None
        ),
        "status": str(suggestion.status),
        "eval_count": int(suggestion.eval_count),
        "baseline_action": str(suggestion.baseline_action),
        "suggested_action": (
            str(suggestion.suggested_action)
            if suggestion.suggested_action is not None
            else None
        ),
        "baseline_reasons": [str(item) for item in (suggestion.baseline_reasons or ())],
        "suggested_reasons": (
            [str(item) for item in (suggestion.suggested_reasons or ())]
            if suggestion.suggested_reasons is not None
            else None
        ),
    }


def _handle_pokayoke_swap_suggest_heavy(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        reserve_in = _coerce_int(obj.get("reserve_in", 0), "reserve_in")
        reserve_out = _coerce_int(obj.get("reserve_out", 0), "reserve_out")
        amount_in = _coerce_int(obj.get("amount_in", 0), "amount_in")
        fee_bps = _coerce_int(obj.get("fee_bps", 0), "fee_bps")
        pending_same_dir = _coerce_int(
            obj.get("pending_volume_same_direction", 0), "pending_volume_same_direction"
        )
        confidence_bps = _coerce_int(obj.get("confidence_bps", 9500), "confidence_bps")

        user_slippage_bps_raw = obj.get("user_slippage_bps", None)
        if user_slippage_bps_raw is None:
            raise ValueError("user_slippage_bps is required")
        user_slippage_bps = _coerce_int(user_slippage_bps_raw, "user_slippage_bps")

        max_attacker_amount_in = _coerce_int(
            obj.get("max_attacker_amount_in", 2000), "max_attacker_amount_in"
        )
        if max_attacker_amount_in < 0 or max_attacker_amount_in > 50_000:
            raise ValueError("max_attacker_amount_in must be in [0, 50_000]")

        max_evals = _coerce_int(obj.get("max_evals", 16), "max_evals")
        if max_evals <= 0 or max_evals > 64:
            raise ValueError("max_evals must be in [1, 64]")

        rows = suggest_amount_in_exact_in_cpmm(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            amount_in=amount_in,
            pending_volume_same_direction=pending_same_dir,
            confidence_bps=confidence_bps,
            slippage_options_bps=_slippage_options(obj.get("slippage_options_bps"), clamp_to_bps=True),
            max_attacker_amount_in=max_attacker_amount_in,
            user_slippage_bps=user_slippage_bps,
            max_evals=max_evals,
            target_actions=_target_actions(obj.get("target_actions")),
        )
        return 200, {"ok": True, "suggestions": [_heavy_suggestion_payload(row) for row in rows]}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "pokayoke_swap_suggest_heavy_error", "details": "request failed"}


def register_slippage_handlers() -> None:
    _register("/api/dex/slippage_advice", _handle_slippage_advice, default_error_code="slippage_advice_error")
    _register(
        "/api/dex/pokayoke_swap_suggest",
        _handle_pokayoke_swap_suggest,
        default_error_code="pokayoke_swap_suggest_error",
    )
    _register(
        "/api/dex/pokayoke_swap_suggest_heavy",
        _handle_pokayoke_swap_suggest_heavy,
        default_error_code="pokayoke_swap_suggest_heavy_error",
    )


register_slippage_handlers()
