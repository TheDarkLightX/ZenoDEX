from __future__ import annotations

from dataclasses import dataclass
from typing import Any

_U32_MAX = 0xFFFFFFFF

INTENT_NONCE_SENDER_RESOLUTION_OK = "Ok"
INTENT_NONCE_SENDER_RESOLUTION_DUPLICATE = "DuplicateNonce"
INTENT_NONCE_SENDER_RESOLUTION_SEQUENCE_INVALID = "SequenceInvalid"


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _require_u32(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < 0 or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class IntentNonceSenderResolution:
    sender_ok: bool
    resolved_last_nonce: int
    reject_code: str


def evaluate_intent_nonce_sender_resolution_gate(
    *,
    strict_increasing: Any,
    contiguous_from_last: Any,
    last_used_nonce: Any,
    next_last_nonce: Any,
) -> IntentNonceSenderResolution:
    strict = _require_bool(strict_increasing, name="strict_increasing")
    contiguous = _require_bool(contiguous_from_last, name="contiguous_from_last")
    last = _require_u32(last_used_nonce, name="last_used_nonce")
    next_last = _require_u32(next_last_nonce, name="next_last_nonce")
    if next_last < last:
        raise ValueError("next_last_nonce must not move backwards")

    if not strict:
        return IntentNonceSenderResolution(
            sender_ok=False,
            resolved_last_nonce=last,
            reject_code=INTENT_NONCE_SENDER_RESOLUTION_DUPLICATE,
        )
    if not contiguous:
        return IntentNonceSenderResolution(
            sender_ok=False,
            resolved_last_nonce=last,
            reject_code=INTENT_NONCE_SENDER_RESOLUTION_SEQUENCE_INVALID,
        )
    return IntentNonceSenderResolution(
        sender_ok=True,
        resolved_last_nonce=next_last,
        reject_code=INTENT_NONCE_SENDER_RESOLUTION_OK,
    )


def intent_nonce_sender_resolution_error(resolution: IntentNonceSenderResolution) -> str | None:
    if resolution.reject_code == INTENT_NONCE_SENDER_RESOLUTION_DUPLICATE:
        return "duplicate nonce in batch"
    if resolution.reject_code == INTENT_NONCE_SENDER_RESOLUTION_SEQUENCE_INVALID:
        return "nonce sequence invalid"
    return None
