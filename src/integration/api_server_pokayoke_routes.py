from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


WriteJson = Callable[[int, object], None]

_POKAYOKE_SWAP_SUGGEST_ENDPOINT = "/api/dex/pokayoke_swap_suggest"
_POKAYOKE_SWAP_SUGGEST_HEAVY_ENDPOINT = "/api/dex/pokayoke_swap_suggest_heavy"


@dataclass(frozen=True)
class _PokayokeInputs:
    reserve_in: int
    reserve_out: int
    amount_in: int
    fee_bps: int
    pending_same_dir: int
    confidence_bps: int


def _common_inputs(obj: dict[str, object]) -> _PokayokeInputs:
    return _PokayokeInputs(
        reserve_in=int(obj.get("reserve_in", 0)),
        reserve_out=int(obj.get("reserve_out", 0)),
        amount_in=int(obj.get("amount_in", 0)),
        fee_bps=int(obj.get("fee_bps", 0)),
        pending_same_dir=int(obj.get("pending_volume_same_direction", 0)),
        confidence_bps=int(obj.get("confidence_bps", 9500)),
    )


def _optional_int(obj: dict[str, object], field: str) -> int | None:
    raw = obj.get(field, None)
    if raw is None:
        return None
    return int(raw)


def _required_int(obj: dict[str, object], field: str) -> int:
    raw = obj.get(field, None)
    if raw is None:
        raise ValueError(f"{field} is required")
    return int(raw)


def _filtered_slippage_options(raw_opts: object) -> list[int]:
    opts: list[int] = []
    if not isinstance(raw_opts, list):
        return opts
    for raw in raw_opts:
        value = _slippage_option(raw)
        if value is not None:
            opts.append(value)
    return opts


def _slippage_option(raw: object) -> int | None:
    try:
        value = int(raw)
    except Exception:
        return None
    if value < 0 or value > 10_000:
        return None
    return int(value)


def _heavy_slippage_options(raw_opts: object) -> list[int] | None:
    if not isinstance(raw_opts, list):
        return None
    return _filtered_slippage_options(raw_opts)


def _max_option(opts: list[int]) -> int | None:
    return max(opts) if opts else None


def _target_actions(raw_targets: object) -> tuple[str, ...]:
    if not isinstance(raw_targets, list):
        return ("confirm", "allow")
    cleaned: list[str] = []
    for raw in raw_targets:
        _append_target_action(cleaned, raw)
    return tuple(cleaned) if cleaned else ("confirm", "allow")


def _append_target_action(cleaned: list[str], raw: object) -> None:
    action = str(raw or "").strip().lower()
    if action in {"confirm", "allow"} and action not in cleaned:
        cleaned.append(action)


def _fast_suggestion_to_dict(sugg: object) -> dict[str, object] | None:
    if sugg is None:
        return None
    return {
        "kind": str(getattr(sugg, "kind")),
        "target_bps": int(getattr(sugg, "target_bps")),
        "suggested_amount_in": (
            int(getattr(sugg, "suggested_amount_in"))
            if getattr(sugg, "suggested_amount_in") is not None
            else None
        ),
        "status": str(getattr(sugg, "status")),
        "eval_count": int(getattr(sugg, "eval_count")),
        "baseline_value_bps": int(getattr(sugg, "baseline_value_bps")),
        "suggested_value_bps": (
            int(getattr(sugg, "suggested_value_bps"))
            if getattr(sugg, "suggested_value_bps") is not None
            else None
        ),
    }


def _heavy_suggestion_to_dict(sugg: object) -> dict[str, object]:
    return {
        "target_action": str(getattr(sugg, "target_action")),
        "suggested_amount_in": _optional_int_attr(sugg, "suggested_amount_in"),
        "status": str(getattr(sugg, "status")),
        "eval_count": int(getattr(sugg, "eval_count")),
        "baseline_action": str(getattr(sugg, "baseline_action")),
        "suggested_action": _optional_str_attr(sugg, "suggested_action"),
        "baseline_reasons": _string_list(getattr(sugg, "baseline_reasons") or ()),
        "suggested_reasons": _optional_string_list_attr(sugg, "suggested_reasons"),
    }


def _optional_int_attr(obj: object, name: str) -> int | None:
    value = getattr(obj, name)
    return int(value) if value is not None else None


def _optional_str_attr(obj: object, name: str) -> str | None:
    value = getattr(obj, name)
    return str(value) if value is not None else None


def _string_list(values: object) -> list[str]:
    return [str(value) for value in values]


def _optional_string_list_attr(obj: object, name: str) -> list[str] | None:
    value = getattr(obj, name)
    if value is None:
        return None
    return _string_list(value)


def _handle_pokayoke_swap_suggest(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        from src.core.pokayoke_swap_suggest import (  # pylint: disable=import-outside-toplevel
            suggest_amount_in_for_impact_lt_bps,
            suggest_amount_in_for_required_slippage_le_bps,
        )

        values = _common_inputs(obj)
        user_slippage_bps = _optional_int(obj, "user_slippage_bps")
        opts = _filtered_slippage_options(obj.get("slippage_options_bps"))
        max_opt = _max_option(opts)

        impact_5 = suggest_amount_in_for_impact_lt_bps(
            reserve_in=values.reserve_in,
            reserve_out=values.reserve_out,
            fee_bps=values.fee_bps,
            amount_in=values.amount_in,
            target_impact_bps=500,
            window=256,
        )
        impact_1 = suggest_amount_in_for_impact_lt_bps(
            reserve_in=values.reserve_in,
            reserve_out=values.reserve_out,
            fee_bps=values.fee_bps,
            amount_in=values.amount_in,
            target_impact_bps=100,
            window=256,
        )
        req_user = _required_slippage_suggestion(
            values=values,
            target_bps=user_slippage_bps,
            suggest=suggest_amount_in_for_required_slippage_le_bps,
        )
        req_max_opt = _required_slippage_suggestion(
            values=values,
            target_bps=max_opt,
            suggest=suggest_amount_in_for_required_slippage_le_bps,
        )
        write_json(200, {"ok": True, "suggestions": _fast_suggestions(impact_5, impact_1, req_user, req_max_opt)})
    except Exception:
        write_json(400, {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"})


def _required_slippage_suggestion(
    *,
    values: _PokayokeInputs,
    target_bps: int | None,
    suggest: Callable[..., object],
) -> object | None:
    if target_bps is None:
        return None
    return suggest(
        reserve_in=values.reserve_in,
        reserve_out=values.reserve_out,
        fee_bps=values.fee_bps,
        amount_in=values.amount_in,
        pending_volume_same_direction=values.pending_same_dir,
        confidence_bps=values.confidence_bps,
        target_required_slippage_bps=int(target_bps),
        window=256,
    )


def _fast_suggestions(
    impact_5: object,
    impact_1: object,
    req_user: object | None,
    req_max_opt: object | None,
) -> dict[str, object]:
    return {
        "impact_lt_500_bps": _fast_suggestion_to_dict(impact_5),
        "impact_lt_100_bps": _fast_suggestion_to_dict(impact_1),
        "required_slippage_le_user_bps": _fast_suggestion_to_dict(req_user),
        "required_slippage_le_max_option_bps": _fast_suggestion_to_dict(req_max_opt),
    }


def _handle_pokayoke_swap_suggest_heavy(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        from src.core.pokayoke_swap_suggest import (  # pylint: disable=import-outside-toplevel
            suggest_amount_in_exact_in_cpmm,
        )

        values = _common_inputs(obj)
        user_slippage_bps = _required_int(obj, "user_slippage_bps")
        opts = _heavy_slippage_options(obj.get("slippage_options_bps"))
        max_attacker_amount_in = _bounded_int(obj, "max_attacker_amount_in", default=2000, low=0, high=50_000)
        max_evals = _bounded_int(obj, "max_evals", default=16, low=1, high=64)
        rows = suggest_amount_in_exact_in_cpmm(
            reserve_in=values.reserve_in,
            reserve_out=values.reserve_out,
            fee_bps=values.fee_bps,
            amount_in=values.amount_in,
            pending_volume_same_direction=values.pending_same_dir,
            confidence_bps=values.confidence_bps,
            slippage_options_bps=opts,
            max_attacker_amount_in=max_attacker_amount_in,
            user_slippage_bps=user_slippage_bps,
            max_evals=max_evals,
            target_actions=_target_actions(obj.get("target_actions")),
        )
        write_json(200, {"ok": True, "suggestions": [_heavy_suggestion_to_dict(row) for row in rows]})
    except Exception:
        write_json(400, {"ok": False, "error": "pokayoke_swap_suggest_heavy_error", "details": "request failed"})


def _bounded_int(obj: dict[str, object], field: str, *, default: int, low: int, high: int) -> int:
    value = int(obj.get(field, default))
    if value < low or value > high:
        raise ValueError(f"{field} must be in [{low}, {high}]")
    return int(value)


def maybe_handle_pokayoke_swap_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: WriteJson,
) -> bool:
    if path == _POKAYOKE_SWAP_SUGGEST_ENDPOINT:
        _handle_pokayoke_swap_suggest(obj, write_json)
        return True
    if path == _POKAYOKE_SWAP_SUGGEST_HEAVY_ENDPOINT:
        _handle_pokayoke_swap_suggest_heavy(obj, write_json)
        return True
    return False
