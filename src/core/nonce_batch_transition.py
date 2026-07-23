"""Exact return-new replay-protection transition for one intent batch.

This module preserves the mounted nonce policy and public rejection precedence
while replacing mutable ``NonceTable`` staging with one canonical nonce patch.
Intent ownership remains a PR #478 obligation; this temporary relation reads
the already-validated legacy intent records and never retains them.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast, final

from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.intents import Intent
from ..state.state_snapshot_values import MAX_U32_V1, CommittedNonceTableV1
from ..state.state_transitions import (
    CanonicalNoncePatchV1,
    NonceAdvanceV1,
    NoncePatchApplyOkV1,
    NoncePatchBuildOkV1,
    NoncePatchRejectV1,
    apply_canonical_nonce_patch_v1,
    build_canonical_nonce_patch_v1,
    validate_committed_nonce_state_v1,
)


class IntentNonceBatchCodeV1(Enum):
    """Stable internal reject classes for the mounted nonce policy."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_PRESTATE = "invalid_prestate"
    INVALID_NONCE = "invalid_nonce"
    INVALID_SENDER = "invalid_sender"
    MIXED_NONCE_PRESENCE = "mixed_nonce_presence"
    DUPLICATE_NONCE = "duplicate_nonce"
    INVALID_SEQUENCE = "invalid_sequence"
    PATCH_REJECTED = "patch_rejected"


@final
@dataclass(frozen=True, slots=True)
class IntentNonceBatchRejectV1:
    """Typed no-candidate rejection with the mounted public reason."""

    code: IntentNonceBatchCodeV1
    public_reason: str

    def __post_init__(self) -> None:
        if type(self.code) is not IntentNonceBatchCodeV1:
            raise TypeError("nonce batch rejection code must be exact")
        if type(self.public_reason) is not str or not self.public_reason:
            raise TypeError("nonce batch rejection reason must be an exact nonempty string")


@final
@dataclass(frozen=True, slots=True)
class IntentNonceBatchOkV1:
    """Complete immutable nonce successor and its optional canonical patch."""

    state: CommittedNonceTableV1
    patch: CanonicalNoncePatchV1 | None

    def __post_init__(self) -> None:
        if type(self.state) is not CommittedNonceTableV1:
            raise TypeError("nonce batch state must be exact committed state")
        if self.patch is not None and type(self.patch) is not CanonicalNoncePatchV1:
            raise TypeError("nonce batch patch must be exact or None")


IntentNonceBatchResultV1: TypeAlias = IntentNonceBatchOkV1 | IntentNonceBatchRejectV1


def _reject(
    code: IntentNonceBatchCodeV1,
    public_reason: str,
) -> IntentNonceBatchRejectV1:
    return IntentNonceBatchRejectV1(code, public_reason)


def _patch_reject_reason(reject: NoncePatchRejectV1) -> str:
    path = ".".join(str(part) for part in reject.path)
    detail = reject.code.value if not path else f"{reject.code.value}:{path}"
    return f"nonce policy rejected: {detail}"


def _positive_u32(value: object) -> int | None:
    if type(value) is not int or not 1 <= value <= MAX_U32_V1:
        return None
    return value


def validate_and_apply_intent_nonce_batch_committed_v1(
    *,
    nonces: CommittedNonceTableV1,
    intents: object,
    require_all_nonces: object,
) -> IntentNonceBatchResultV1:
    """Validate current nonce policy and produce one immutable successor.

    Rejection precedence and public messages match
    ``validate_and_apply_intent_nonce_batch`` for its canonical input domain.
    An empty or nonce-free accepted batch reuses the immutable pre-state and
    carries no patch.
    """

    if type(require_all_nonces) is not bool:
        return _reject(
            IntentNonceBatchCodeV1.WRONG_EXACT_TYPE,
            "nonce policy rejected",
        )
    if type(intents) not in {list, tuple}:
        return _reject(
            IntentNonceBatchCodeV1.WRONG_EXACT_TYPE,
            "nonce policy rejected",
        )
    exact_intents = cast(list[Intent] | tuple[Intent, ...], intents)
    exact_require_all_nonces = require_all_nonces

    prestate_reject = validate_committed_nonce_state_v1(nonces)
    if prestate_reject is not None:
        return _reject(
            IntentNonceBatchCodeV1.INVALID_PRESTATE,
            _patch_reject_reason(prestate_reject),
        )
    if not exact_intents:
        return IntentNonceBatchOkV1(nonces, None)

    per_sender: dict[str, list[int]] = {}
    saw_nonce = False
    saw_missing = False

    for intent in exact_intents:
        fields = intent.fields or {}
        nonce_raw = fields.get("nonce") if type(fields) is dict else None
        if nonce_raw is None:
            saw_missing = True
            if exact_require_all_nonces:
                return _reject(
                    IntentNonceBatchCodeV1.INVALID_NONCE,
                    "Missing/invalid nonce",
                )
            continue

        nonce = _positive_u32(nonce_raw)
        if nonce is None:
            return _reject(
                IntentNonceBatchCodeV1.INVALID_NONCE,
                "Missing/invalid nonce",
            )
        try:
            sender = canonical_hex_fixed_allow_0x(
                intent.sender_pubkey,
                nbytes=48,
                name="sender_pubkey",
            )
        except (TypeError, ValueError) as exc:
            return _reject(
                IntentNonceBatchCodeV1.INVALID_SENDER,
                f"invalid sender_pubkey for nonce accounting: {exc}",
            )
        per_sender.setdefault(sender, []).append(nonce)
        saw_nonce = True

    if saw_nonce and saw_missing:
        return _reject(
            IntentNonceBatchCodeV1.MIXED_NONCE_PRESENCE,
            "nonce presence must be consistent across batch",
        )
    if not saw_nonce:
        return IntentNonceBatchOkV1(nonces, None)

    advances: list[NonceAdvanceV1] = []
    for sender, nonce_list in per_sender.items():
        if len(nonce_list) != len(set(nonce_list)):
            return _reject(
                IntentNonceBatchCodeV1.DUPLICATE_NONCE,
                "duplicate nonce in batch",
            )
        nonce_list_sorted = sorted(nonce_list)
        last = nonces.get_last(sender)
        expected = list(range(last + 1, last + 1 + len(nonce_list_sorted)))
        if nonce_list_sorted != expected:
            return _reject(
                IntentNonceBatchCodeV1.INVALID_SEQUENCE,
                "nonce sequence invalid",
            )
        advances.append(NonceAdvanceV1(sender, last, expected[-1]))

    built = build_canonical_nonce_patch_v1(tuple(advances))
    if type(built) is not NoncePatchBuildOkV1:
        return _reject(
            IntentNonceBatchCodeV1.PATCH_REJECTED,
            _patch_reject_reason(built),
        )
    applied = apply_canonical_nonce_patch_v1(nonces, built.patch)
    if type(applied) is not NoncePatchApplyOkV1:
        return _reject(
            IntentNonceBatchCodeV1.PATCH_REJECTED,
            _patch_reject_reason(applied),
        )
    return IntentNonceBatchOkV1(applied.state, applied.patch)


__all__ = [
    "IntentNonceBatchCodeV1",
    "IntentNonceBatchOkV1",
    "IntentNonceBatchRejectV1",
    "IntentNonceBatchResultV1",
    "validate_and_apply_intent_nonce_batch_committed_v1",
]
