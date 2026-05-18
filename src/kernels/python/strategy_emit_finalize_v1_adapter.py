from __future__ import annotations

from dataclasses import dataclass


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class StrategyEmitFinalizeResult:
    ok: bool
    emit_requested: bool
    system_compose_ok: bool
    submit_bundle_ok: bool
    error: str | None = None


def check_strategy_emit_finalize(
    *,
    emit_requested: bool,
    system_compose_ok: bool,
    submit_bundle_ok: bool,
) -> StrategyEmitFinalizeResult:
    emit_requested = _require_bool("emit_requested", emit_requested)
    system_compose_ok = _require_bool("system_compose_ok", system_compose_ok)
    submit_bundle_ok = _require_bool("submit_bundle_ok", submit_bundle_ok)

    if not emit_requested:
        return StrategyEmitFinalizeResult(
            ok=True,
            emit_requested=False,
            system_compose_ok=system_compose_ok,
            submit_bundle_ok=submit_bundle_ok,
        )

    if not system_compose_ok:
        error = "emit_finalize_system_compose_rejected"
    elif not submit_bundle_ok:
        error = "emit_finalize_submit_bundle_rejected"
    else:
        error = None
    return StrategyEmitFinalizeResult(
        ok=error is None,
        emit_requested=True,
        system_compose_ok=system_compose_ok,
        submit_bundle_ok=submit_bundle_ok,
        error=error,
    )
