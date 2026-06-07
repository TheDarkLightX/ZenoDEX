from __future__ import annotations

from typing import Callable


WriteJson = Callable[[int, object], None]


def _handle_impact_preview(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        from src.core.price_impact_preview import price_impact_preview  # pylint: disable=import-outside-toplevel

        reserve_in = int(obj.get("reserve_in", 0))
        reserve_out = int(obj.get("reserve_out", 0))
        amount_in = int(obj.get("amount_in", 0))
        fee_bps = int(obj.get("fee_bps", 0))
        pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
        confidence_bps = int(obj.get("confidence_bps", 9500))

        preview = price_impact_preview(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
            pending_volume_same_direction=pending_same_dir,
            confidence_bps=confidence_bps,
        )
        write_json(
            200,
            {
                "ok": True,
                "preview": {
                    "amount_out_isolated": int(preview.amount_out_isolated),
                    "fee_amount": int(preview.fee_amount),
                    "price_impact_bps": int(preview.price_impact_bps),
                    "effective_price_e8": int(preview.effective_price_e8),
                    "spot_price_e8": int(preview.spot_price_e8),
                    "amount_out_best_case": int(preview.amount_out_best_case),
                    "amount_out_worst_case": int(preview.amount_out_worst_case),
                    "recommended_min_out": int(preview.recommended_min_out),
                    "pending_volume_same_direction": int(preview.pending_volume_same_direction),
                    "confidence_bps": int(preview.confidence_bps),
                    "pending_volume_at_confidence": int(preview.pending_volume_at_confidence),
                    "amount_out_at_confidence": int(preview.amount_out_at_confidence),
                },
            },
        )
    except Exception:
        write_json(400, {"ok": False, "error": "impact_preview_error", "details": "request failed"})


def _parse_optional_slippage_bps(obj: dict[str, object]) -> int | None:
    raw = obj.get("user_slippage_bps", None)
    return None if raw is None else int(raw)


def _parse_slippage_options(obj: dict[str, object]) -> list[int] | None:
    raw_options = obj.get("slippage_options_bps")
    if not isinstance(raw_options, list):
        return None
    parsed: list[int] = []
    for item in raw_options:
        try:
            parsed.append(int(item))
        except Exception:
            continue
    return parsed


def _optional_int(value: object) -> int | None:
    return int(value) if value is not None else None


def _build_pokayoke_payload(advice: object, user_slippage_bps: int | None) -> dict[str, object] | None:
    if user_slippage_bps is None:
        return None
    from src.core.pokayoke_swap_guardrails import (  # pylint: disable=import-outside-toplevel
        SwapGuardrailContext,
        decide_swap_guardrails,
    )

    ctx = SwapGuardrailContext(
        price_impact_bps=int(advice.price_impact_bps),
        slippage_advice_status=str(advice.status),
        required_slippage_bps=int(advice.required_slippage_bps),
        recommended_slippage_bps_revert_safe=_optional_int(advice.recommended_slippage_bps_revert_safe),
        recommended_slippage_bps_mev_safe=_optional_int(advice.recommended_slippage_bps_mev_safe),
        recommended_slippage_bps=_optional_int(advice.recommended_slippage_bps),
    )
    decision = decide_swap_guardrails(ctx=ctx, user_slippage_bps=int(user_slippage_bps))
    return {
        "action": str(decision.action),
        "reasons": list(decision.reasons),
        "messages": list(decision.messages),
        "typed_confirm_phrase": decision.typed_confirm_phrase,
    }


def _slippage_option_payload(option: object) -> dict[str, object]:
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


def _slippage_advice_payload(advice: object, pokayoke: dict[str, object] | None) -> dict[str, object]:
    return {
        "best_amount_out": int(advice.best_amount_out),
        "price_impact_bps": int(advice.price_impact_bps),
        "amount_out_at_confidence": int(advice.amount_out_at_confidence),
        "pending_volume_at_confidence": int(advice.pending_volume_at_confidence),
        "confidence_bps": int(advice.confidence_bps),
        "required_slippage_bps": int(advice.required_slippage_bps),
        "recommended_slippage_bps_revert_safe": _optional_int(advice.recommended_slippage_bps_revert_safe),
        "recommended_slippage_bps_mev_safe": _optional_int(advice.recommended_slippage_bps_mev_safe),
        "recommended_slippage_bps": _optional_int(advice.recommended_slippage_bps),
        "status": str(advice.status),
        "pokayoke": pokayoke,
        "options": [_slippage_option_payload(option) for option in advice.options],
    }


def _slippage_advice_from_payload(obj: dict[str, object]) -> object:
    from src.core.slippage_advisor import (  # pylint: disable=import-outside-toplevel
        slippage_advice_exact_in_cpmm,
    )

    return slippage_advice_exact_in_cpmm(
        reserve_in=int(obj.get("reserve_in", 0)),
        reserve_out=int(obj.get("reserve_out", 0)),
        fee_bps=int(obj.get("fee_bps", 0)),
        amount_in=int(obj.get("amount_in", 0)),
        pending_volume_same_direction=int(obj.get("pending_volume_same_direction", 0)),
        confidence_bps=int(obj.get("confidence_bps", 9500)),
        slippage_options_bps=_parse_slippage_options(obj),
        max_attacker_amount_in=int(obj.get("max_attacker_amount_in", 5000)),
    )


def _handle_slippage_advice(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        advice = _slippage_advice_from_payload(obj)
        pokayoke = _build_pokayoke_payload(advice, _parse_optional_slippage_bps(obj))
        write_json(
            200,
            {
                "ok": True,
                "advice": _slippage_advice_payload(advice, pokayoke),
            },
        )
    except Exception:
        write_json(400, {"ok": False, "error": "slippage_advice_error", "details": "request failed"})


def maybe_handle_dex_readonly_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: WriteJson,
) -> bool:
    if path == "/api/dex/impact_preview":
        _handle_impact_preview(obj, write_json)
        return True
    if path == "/api/dex/slippage_advice":
        _handle_slippage_advice(obj, write_json)
        return True
    return False
