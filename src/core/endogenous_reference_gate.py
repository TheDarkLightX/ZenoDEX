from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from .domain_limits import require_int_range

REFERENCE_SOURCE_TWAP_ACCUMULATOR = "twap_accumulator"

REJECT_OK = "Ok"
REJECT_SOURCE_NOT_TWAP = "EndogenousReferenceRequiresTwap"
REJECT_TWAP_WINDOW_TOO_SHORT = "TwapWindowTooShort"
REJECT_TWAP_ELAPSED_TOO_SHORT = "TwapElapsedTooShort"


@dataclass(frozen=True)
class EndogenousReferenceGateOutcome:
    source_kind: str
    twap_window_blocks: int
    reference_elapsed_blocks: int
    min_twap_window_blocks: int
    min_reference_elapsed_blocks: int
    source_kind_ok: bool
    twap_window_ok: bool
    reference_elapsed_ok: bool
    admission_ok: bool
    reject_code: str
    checks: Mapping[str, bool | int | str]


def evaluate_endogenous_reference_gate(
    *,
    source_kind: Any,
    twap_window_blocks: Any,
    reference_elapsed_blocks: Any,
    min_twap_window_blocks: Any = 1,
    min_reference_elapsed_blocks: Any = 1,
) -> EndogenousReferenceGateOutcome:
    """Require a non-instantaneous TWAP source for endogenous payout references.

    This gate is deliberately small: it does not compute a TWAP. It prevents
    payout state machines from accepting instantaneous AMM spot as the reference
    for an endogenous derivative settlement.
    """

    source = _require_source_kind(source_kind)
    window = require_int_range("twap_window_blocks", twap_window_blocks, minimum=0)
    elapsed = require_int_range("reference_elapsed_blocks", reference_elapsed_blocks, minimum=0)
    min_window = require_int_range("min_twap_window_blocks", min_twap_window_blocks, minimum=1)
    min_elapsed = require_int_range("min_reference_elapsed_blocks", min_reference_elapsed_blocks, minimum=1)

    source_kind_ok = bool(source == REFERENCE_SOURCE_TWAP_ACCUMULATOR)
    twap_window_ok = bool(window >= min_window)
    reference_elapsed_ok = bool(elapsed >= min_elapsed)

    if not source_kind_ok:
        reject_code = REJECT_SOURCE_NOT_TWAP
    elif not twap_window_ok:
        reject_code = REJECT_TWAP_WINDOW_TOO_SHORT
    elif not reference_elapsed_ok:
        reject_code = REJECT_TWAP_ELAPSED_TOO_SHORT
    else:
        reject_code = REJECT_OK

    return EndogenousReferenceGateOutcome(
        source_kind=source,
        twap_window_blocks=window,
        reference_elapsed_blocks=elapsed,
        min_twap_window_blocks=min_window,
        min_reference_elapsed_blocks=min_elapsed,
        source_kind_ok=source_kind_ok,
        twap_window_ok=twap_window_ok,
        reference_elapsed_ok=reference_elapsed_ok,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks={
            "source_kind": source,
            "twap_window_blocks": window,
            "reference_elapsed_blocks": elapsed,
            "min_twap_window_blocks": min_window,
            "min_reference_elapsed_blocks": min_elapsed,
            "source_kind_ok": source_kind_ok,
            "twap_window_ok": twap_window_ok,
            "reference_elapsed_ok": reference_elapsed_ok,
        },
    )


def endogenous_reference_gate_error(outcome: EndogenousReferenceGateOutcome) -> str | None:
    if outcome.reject_code == REJECT_SOURCE_NOT_TWAP:
        return "endogenous payout reference requires twap_accumulator source"
    if outcome.reject_code == REJECT_TWAP_WINDOW_TOO_SHORT:
        return "endogenous payout reference TWAP window is below policy minimum"
    if outcome.reject_code == REJECT_TWAP_ELAPSED_TOO_SHORT:
        return "endogenous payout reference has not elapsed long enough"
    return None


def _require_source_kind(value: Any) -> str:
    if not isinstance(value, str):
        raise TypeError("source_kind must be a string")
    source = value.strip()
    if not source:
        raise ValueError("source_kind must be non-empty")
    return source


__all__ = [
    "REFERENCE_SOURCE_TWAP_ACCUMULATOR",
    "REJECT_OK",
    "REJECT_SOURCE_NOT_TWAP",
    "REJECT_TWAP_ELAPSED_TOO_SHORT",
    "REJECT_TWAP_WINDOW_TOO_SHORT",
    "EndogenousReferenceGateOutcome",
    "endogenous_reference_gate_error",
    "evaluate_endogenous_reference_gate",
]
