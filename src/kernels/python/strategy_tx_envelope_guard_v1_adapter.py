from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

MAX_U32 = 0xFFFFFFFF


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _is_u32(value: object, *, minimum: int = 0) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and minimum <= int(value) <= MAX_U32


def _fee_limit_is_valid(value: object) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return 0 <= int(value) <= MAX_U32
    if not isinstance(value, str):
        return False
    text = value.strip()
    if not text or not text.isdigit():
        return False
    if text != "0" and text.startswith("0"):
        return False
    amount = int(text, 10)
    return 0 <= amount <= MAX_U32


@dataclass(frozen=True)
class StrategyTxEnvelopeGuardResult:
    ok: bool
    tx_requested: bool
    tx_args_paired_ok: bool
    tx_sequence_ok: bool
    tx_expiration_ok: bool
    tx_fee_limit_ok: bool
    tx_stream_scope_ok: bool
    error: str | None = None


def check_strategy_tx_envelope(
    *,
    tx_requested: bool,
    sequence_number: object,
    expiration_time: object,
    fee_limit: object,
    operations: Mapping[str, object],
) -> StrategyTxEnvelopeGuardResult:
    tx_requested = _require_bool("tx_requested", tx_requested)
    if not isinstance(operations, Mapping):
        raise TypeError("operations must be a mapping")

    if not tx_requested:
        return StrategyTxEnvelopeGuardResult(
            ok=True,
            tx_requested=False,
            tx_args_paired_ok=True,
            tx_sequence_ok=True,
            tx_expiration_ok=True,
            tx_fee_limit_ok=True,
            tx_stream_scope_ok=True,
        )

    sequence_present = sequence_number is not None
    expiration_present = expiration_time is not None
    tx_args_paired_ok = sequence_present and expiration_present
    tx_sequence_ok = _is_u32(sequence_number, minimum=0)
    tx_expiration_ok = _is_u32(expiration_time, minimum=1)
    tx_fee_limit_ok = _fee_limit_is_valid(fee_limit)

    keys = list(operations.keys())
    if not all(isinstance(key, str) for key in keys):
        raise TypeError("operations keys must be strings")
    intents_stream = operations.get("2")
    tx_stream_scope_ok = (
        isinstance(intents_stream, list)
        and len(intents_stream) > 0
        and "3" not in operations
        and set(keys) <= {"2"}
    )

    if not tx_args_paired_ok:
        error = "tx_envelope_pairing_rejected"
    elif not tx_sequence_ok:
        error = "tx_envelope_sequence_rejected"
    elif not tx_expiration_ok:
        error = "tx_envelope_expiration_rejected"
    elif not tx_fee_limit_ok:
        error = "tx_envelope_fee_limit_rejected"
    elif not tx_stream_scope_ok:
        error = "tx_envelope_stream_scope_rejected"
    else:
        error = None

    return StrategyTxEnvelopeGuardResult(
        ok=error is None,
        tx_requested=True,
        tx_args_paired_ok=tx_args_paired_ok,
        tx_sequence_ok=tx_sequence_ok,
        tx_expiration_ok=tx_expiration_ok,
        tx_fee_limit_ok=tx_fee_limit_ok,
        tx_stream_scope_ok=tx_stream_scope_ok,
        error=error,
    )
