from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Sequence


_U32_MAX = 0xFFFFFFFF
INTENT_NONCE_SEQUENCE_KERNEL_MAX = 8


def _require_u32(name: str, value: Any, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class IntentNonceSequenceGateOutcome:
    last_used_nonce: int
    nonce_count: int
    strict_increasing: bool
    contiguous_from_last: bool
    sequence_ok: bool
    next_last_nonce: int


def evaluate_sorted_intent_nonce_sequence_gate(
    *,
    last_used_nonce: Any,
    nonce_count: Any,
    nonce_0: Any,
    nonce_1: Any,
    nonce_2: Any,
    nonce_3: Any,
    nonce_4: Any,
    nonce_5: Any,
    nonce_6: Any,
    nonce_7: Any,
) -> IntentNonceSequenceGateOutcome:
    last = _require_u32("last_used_nonce", last_used_nonce)
    count = _require_u32("nonce_count", nonce_count)
    if count > INTENT_NONCE_SEQUENCE_KERNEL_MAX:
        raise ValueError("nonce_count out of range")
    values = (
        _require_u32("nonce_0", nonce_0, minimum=1),
        _require_u32("nonce_1", nonce_1, minimum=1),
        _require_u32("nonce_2", nonce_2, minimum=1),
        _require_u32("nonce_3", nonce_3, minimum=1),
        _require_u32("nonce_4", nonce_4, minimum=1),
        _require_u32("nonce_5", nonce_5, minimum=1),
        _require_u32("nonce_6", nonce_6, minimum=1),
        _require_u32("nonce_7", nonce_7, minimum=1),
    )

    active = values[:count]
    strict_increasing = all(active[idx] < active[idx + 1] for idx in range(len(active) - 1))
    contiguous_from_last = all(nonce == last + idx + 1 for idx, nonce in enumerate(active))
    sequence_ok = bool(strict_increasing and contiguous_from_last)
    next_last = int(last + count) if sequence_ok else int(last)
    return IntentNonceSequenceGateOutcome(
        last_used_nonce=last,
        nonce_count=int(count),
        strict_increasing=bool(strict_increasing),
        contiguous_from_last=bool(contiguous_from_last),
        sequence_ok=sequence_ok,
        next_last_nonce=next_last,
    )


def evaluate_intent_nonce_sequence(
    *,
    last_used_nonce: Any,
    nonce_values: Sequence[Any],
) -> IntentNonceSequenceGateOutcome:
    last = _require_u32("last_used_nonce", last_used_nonce)
    normalized = tuple(
        _require_u32(f"nonce_values[{idx}]", raw, minimum=1) for idx, raw in enumerate(nonce_values)
    )
    sorted_values = tuple(sorted(int(value) for value in normalized))
    count = len(sorted_values)

    if count <= INTENT_NONCE_SEQUENCE_KERNEL_MAX:
        padded = list(sorted_values) + [1] * (INTENT_NONCE_SEQUENCE_KERNEL_MAX - count)
        return evaluate_sorted_intent_nonce_sequence_gate(
            last_used_nonce=last,
            nonce_count=count,
            nonce_0=padded[0],
            nonce_1=padded[1],
            nonce_2=padded[2],
            nonce_3=padded[3],
            nonce_4=padded[4],
            nonce_5=padded[5],
            nonce_6=padded[6],
            nonce_7=padded[7],
        )

    strict_increasing = all(
        sorted_values[idx] < sorted_values[idx + 1] for idx in range(len(sorted_values) - 1)
    )
    contiguous_from_last = all(
        nonce == last + idx + 1 for idx, nonce in enumerate(sorted_values)
    )
    sequence_ok = bool(strict_increasing and contiguous_from_last)
    next_last = int(last + count) if sequence_ok else int(last)
    return IntentNonceSequenceGateOutcome(
        last_used_nonce=last,
        nonce_count=int(count),
        strict_increasing=bool(strict_increasing),
        contiguous_from_last=bool(contiguous_from_last),
        sequence_ok=sequence_ok,
        next_last_nonce=next_last,
    )
