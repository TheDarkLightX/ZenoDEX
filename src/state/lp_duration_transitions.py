"""Exact return-new LP position and duration-risk transitions.

The mounted integration path still updates legacy ``LPTable`` metadata after a
settlement.  This module defines the exact FCIS leaf that will replace that
two-phase balance-then-metadata mutation during the atomic ``DexState``
migration. One accepted event determines the balance and metadata replacement
from the same immutable pre-state. Rejection exposes no candidate.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import TypeAlias, cast, final

from .snapshot_combinators import MAX_CANONICAL_BYTES_V1
from .state_snapshot_values import (
    DEX_LP_AMOUNT_MAX,
    MAX_LP_ENTRIES_V1,
    CommittedLPTableV1,
)
from .state_snapshots import StateAdmissionError, snapshot_lp_table
from .state_transitions import (
    CanonicalLPPositionPatchV1,
    LPPositionPatchApplyOkV1,
    LPPositionPatchCodeV1,
    LPPositionPatchRejectV1,
    LPPositionValueV1,
    LPPositionWriteV1,
    apply_canonical_lp_position_patch_v1,
    build_canonical_lp_position_patch_v1,
    validate_lp_position_key_v1,
)

FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True

LPDurationPathPartV1: TypeAlias = str | int
LPDurationPathV1: TypeAlias = tuple[LPDurationPathPartV1, ...]


class LPDurationTransitionCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    OUT_OF_RANGE = "out_of_range"
    BYTE_LIMIT = "byte_limit"
    NONCANONICAL_KEY = "noncanonical_key"
    NONCANONICAL_EVENTS = "noncanonical_events"
    DUPLICATE_EVENT = "duplicate_event"
    SAME_BATCH_ADD_REMOVE = "same_batch_add_remove"
    INVALID_PRESTATE = "invalid_prestate"
    DOMAIN_INVARIANT = "domain_invariant"
    INVALID_CANDIDATE = "invalid_candidate"


@final
@dataclass(frozen=True, slots=True)
class LPDurationTransitionRejectV1:
    code: LPDurationTransitionCodeV1
    path: LPDurationPathV1

    def __post_init__(self) -> None:
        if type(self.code) is not LPDurationTransitionCodeV1:
            raise TypeError("LP duration rejection code must be exact")
        if type(self.path) is not tuple or any(
            type(part) is not str and type(part) is not int for part in self.path
        ):
            raise TypeError("LP duration rejection path must be exact")


@final
@dataclass(frozen=True, slots=True)
class LPDurationRiskPolicyV1:
    """Data-only exact policy context for accepted LP lifecycle events."""

    base_age_seconds: int = 0
    max_age_seconds: int = 0
    churn_window_seconds: int = 0
    decay_seconds: int = 0
    multiplier: int = 2
    max_churn_tier: int = 0

    def __post_init__(self) -> None:
        for field_name in (
            "base_age_seconds",
            "max_age_seconds",
            "churn_window_seconds",
            "decay_seconds",
            "max_churn_tier",
        ):
            value = object.__getattribute__(self, field_name)
            if type(value) is not int:
                raise TypeError(f"{field_name} must be an exact integer")
            if value < 0:
                raise ValueError(f"{field_name} must be an exact nonnegative int")
        if type(self.multiplier) is not int:
            raise TypeError("multiplier must be an exact integer")
        if self.multiplier < 1:
            raise ValueError("multiplier must be an exact int >= 1")
        if self.max_age_seconds and self.base_age_seconds > self.max_age_seconds:
            raise ValueError("base_age_seconds must be <= max_age_seconds")


@final
@dataclass(frozen=True, slots=True)
class LPDurationEventV1:
    """One accepted aggregate LP delta at a canonical position key."""

    key: tuple[str, str]
    delta_add: int
    delta_sub: int

    def __post_init__(self) -> None:
        key_reject = validate_lp_position_key_v1(self.key)
        if key_reject is not None:
            if key_reject.code is LPPositionPatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("LP duration event key must be an exact pair of strings")
            raise ValueError("LP duration event key is not canonical")
        if type(self.delta_add) is not int or type(self.delta_sub) is not int:
            raise TypeError("LP duration event deltas must be exact integers")
        if self.delta_add < 0 or self.delta_sub < 0:
            raise ValueError("LP duration event deltas must be nonnegative")
        if self.delta_add > DEX_LP_AMOUNT_MAX or self.delta_sub > DEX_LP_AMOUNT_MAX:
            raise ValueError("LP duration event deltas exceed the committed domain")
        if self.delta_add == 0 and self.delta_sub == 0:
            raise ValueError("LP duration event must change an LP position")


@final
@dataclass(frozen=True, slots=True)
class LPDurationTransitionOkV1:
    state: CommittedLPTableV1
    patch: CanonicalLPPositionPatchV1 | None

    def __post_init__(self) -> None:
        if type(self.state) is not CommittedLPTableV1:
            raise TypeError("LP duration transition state must be exact")
        if self.patch is not None and type(self.patch) is not CanonicalLPPositionPatchV1:
            raise TypeError("LP duration transition patch must be exact")


LPDurationTransitionResultV1: TypeAlias = LPDurationTransitionOkV1 | LPDurationTransitionRejectV1


@final
@dataclass(frozen=True, slots=True)
class _LPDurationContextV1:
    now: int
    policy: LPDurationRiskPolicyV1 | None


@final
@dataclass(frozen=True, slots=True)
class _LPDurationInputsV1:
    pre: CommittedLPTableV1
    events: tuple[LPDurationEventV1, ...]
    context: _LPDurationContextV1


def _reject(
    code: LPDurationTransitionCodeV1,
    path: LPDurationPathV1,
) -> LPDurationTransitionRejectV1:
    return LPDurationTransitionRejectV1(code, path)


def _policy_reject_v1(policy: object) -> LPDurationTransitionRejectV1 | None:
    if policy is None:
        return None
    if type(policy) is not LPDurationRiskPolicyV1:
        return _reject(LPDurationTransitionCodeV1.WRONG_EXACT_TYPE, ("policy",))
    exact = policy
    fields = (
        exact.base_age_seconds,
        exact.max_age_seconds,
        exact.churn_window_seconds,
        exact.decay_seconds,
        exact.max_churn_tier,
    )
    if any(type(value) is not int for value in fields) or type(exact.multiplier) is not int:
        return _reject(LPDurationTransitionCodeV1.WRONG_EXACT_TYPE, ("policy",))
    if any(value < 0 for value in fields) or exact.multiplier < 1:
        return _reject(LPDurationTransitionCodeV1.OUT_OF_RANGE, ("policy",))
    if exact.max_age_seconds and exact.base_age_seconds > exact.max_age_seconds:
        return _reject(LPDurationTransitionCodeV1.DOMAIN_INVARIANT, ("policy",))
    if (
        sum(max(1, (value.bit_length() + 7) // 8) for value in fields + (exact.multiplier,))
        > MAX_CANONICAL_BYTES_V1
    ):
        return _reject(LPDurationTransitionCodeV1.BYTE_LIMIT, ("policy",))
    return None


def _event_reject_v1(
    event: object,
    index: int,
) -> LPDurationTransitionRejectV1 | None:
    path: LPDurationPathV1 = ("events", index)
    if type(event) is not LPDurationEventV1:
        return _reject(LPDurationTransitionCodeV1.WRONG_EXACT_TYPE, path)
    exact = event
    key_reject = validate_lp_position_key_v1(exact.key)
    if key_reject is not None:
        if key_reject.code is LPPositionPatchCodeV1.WRONG_EXACT_TYPE:
            code = LPDurationTransitionCodeV1.WRONG_EXACT_TYPE
        elif key_reject.code is LPPositionPatchCodeV1.ITEM_LIMIT:
            code = LPDurationTransitionCodeV1.ITEM_LIMIT
        else:
            code = LPDurationTransitionCodeV1.NONCANONICAL_KEY
        return _reject(code, path + ("key",))
    if type(exact.delta_add) is not int or type(exact.delta_sub) is not int:
        return _reject(LPDurationTransitionCodeV1.WRONG_EXACT_TYPE, path)
    if exact.delta_add < 0 or exact.delta_sub < 0:
        return _reject(LPDurationTransitionCodeV1.OUT_OF_RANGE, path)
    if exact.delta_add > DEX_LP_AMOUNT_MAX or exact.delta_sub > DEX_LP_AMOUNT_MAX:
        return _reject(LPDurationTransitionCodeV1.OUT_OF_RANGE, path)
    if exact.delta_add == 0 and exact.delta_sub == 0:
        return _reject(LPDurationTransitionCodeV1.NONCANONICAL_EVENTS, path)
    return None


def _event_work_bytes_v1(event: LPDurationEventV1) -> int:
    return (
        len(event.key[0].encode("utf-8"))
        + len(event.key[1].encode("utf-8"))
        + max(1, (event.delta_add.bit_length() + 7) // 8)
        + max(1, (event.delta_sub.bit_length() + 7) // 8)
    )


def _events_reject_v1(events: object) -> LPDurationTransitionRejectV1 | None:
    if type(events) is not tuple:
        return _reject(LPDurationTransitionCodeV1.WRONG_EXACT_TYPE, ("events",))
    if len(events) > MAX_LP_ENTRIES_V1:
        return _reject(LPDurationTransitionCodeV1.ITEM_LIMIT, ("events",))
    previous_key: tuple[str, str] | None = None
    work_bytes = 0
    for index, event in enumerate(events):
        reject = _event_reject_v1(event, index)
        if reject is not None:
            return reject
        exact = cast(LPDurationEventV1, event)
        work_bytes += _event_work_bytes_v1(exact)
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _reject(LPDurationTransitionCodeV1.BYTE_LIMIT, ("events",))
        if previous_key is not None and exact.key == previous_key:
            return _reject(
                LPDurationTransitionCodeV1.DUPLICATE_EVENT,
                ("events", index, "key"),
            )
        if previous_key is not None and exact.key < previous_key:
            return _reject(
                LPDurationTransitionCodeV1.NONCANONICAL_EVENTS,
                ("events", index, "key"),
            )
        previous_key = exact.key
    return None


def _decayed_tier_v1(
    policy: LPDurationRiskPolicyV1,
    *,
    tier: int,
    last_update_timestamp: int | None,
    now: int,
) -> int:
    """Return the policy-defined tier after deterministic elapsed-time decay."""

    bounded_tier = min(tier, policy.max_churn_tier) if policy.max_churn_tier else tier
    if bounded_tier == 0 or policy.decay_seconds == 0 or last_update_timestamp is None:
        return bounded_tier
    if last_update_timestamp > now:
        raise ValueError("last churn update timestamp cannot be in the future")
    return max(
        0,
        bounded_tier - ((now - last_update_timestamp) // policy.decay_seconds),
    )


def _position_value_v1(
    state: CommittedLPTableV1,
    key: tuple[str, str],
) -> LPPositionValueV1:
    owner, pool_id = key
    return LPPositionValueV1(
        balance=state.get(owner, pool_id),
        last_mint_timestamp=state.get_last_mint_timestamp(owner, pool_id),
        last_remove_timestamp=state.get_last_remove_timestamp(owner, pool_id),
        churn_tier=state.get_churn_tier(owner, pool_id),
        last_churn_update_timestamp=state.get_last_churn_update_timestamp(
            owner,
            pool_id,
        ),
    )


def _recent(
    timestamp: int | None,
    *,
    now: int,
    window: int,
) -> bool:
    return timestamp is not None and timestamp <= now and now - timestamp <= window


def _replacement_v1(
    current: LPPositionValueV1,
    event: LPDurationEventV1,
    *,
    event_index: int,
    context: _LPDurationContextV1,
) -> LPPositionValueV1 | LPDurationTransitionRejectV1:
    now = context.now
    policy = context.policy
    replacement_balance = current.balance + event.delta_add - event.delta_sub
    if not 0 <= replacement_balance <= DEX_LP_AMOUNT_MAX:
        return _reject(
            LPDurationTransitionCodeV1.OUT_OF_RANGE,
            ("events", event_index, "balance"),
        )
    replacement = replace(
        current,
        balance=replacement_balance,
        last_mint_timestamp=(None if replacement_balance == 0 else current.last_mint_timestamp),
    )
    if event.delta_add > 0:
        if replacement.balance == 0:
            return _reject(
                LPDurationTransitionCodeV1.DOMAIN_INVARIANT,
                ("events", event_index, "balance"),
            )
        if policy is not None:
            try:
                tier = _decayed_tier_v1(
                    policy,
                    tier=replacement.churn_tier,
                    last_update_timestamp=replacement.last_churn_update_timestamp,
                    now=now,
                )
            except ValueError:
                return _reject(
                    LPDurationTransitionCodeV1.DOMAIN_INVARIANT,
                    (
                        "events",
                        event_index,
                        "last_churn_update_timestamp",
                    ),
                )
            if _recent(
                replacement.last_remove_timestamp,
                now=now,
                window=policy.churn_window_seconds,
            ) or _recent(
                replacement.last_mint_timestamp,
                now=now,
                window=policy.churn_window_seconds,
            ):
                tier += 1
            if policy.max_churn_tier:
                tier = min(tier, policy.max_churn_tier)
            replacement = replace(
                replacement,
                churn_tier=tier,
                last_churn_update_timestamp=now,
            )
        replacement = replace(replacement, last_mint_timestamp=now)
    if event.delta_sub > 0 and policy is not None:
        replacement = replace(replacement, last_remove_timestamp=now)
    return replacement


def _validated_inputs_v1(
    pre_state: CommittedLPTableV1,
    events: tuple[LPDurationEventV1, ...],
    *,
    now: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> _LPDurationInputsV1 | LPDurationTransitionRejectV1:
    if type(pre_state) is not CommittedLPTableV1:
        return _reject(LPDurationTransitionCodeV1.WRONG_EXACT_TYPE, ("state",))
    try:
        pre = snapshot_lp_table(pre_state)
    except StateAdmissionError:
        return _reject(LPDurationTransitionCodeV1.INVALID_PRESTATE, ("state",))
    event_reject = _events_reject_v1(events)
    if event_reject is not None:
        return event_reject
    if type(now) is not int:
        return _reject(LPDurationTransitionCodeV1.WRONG_EXACT_TYPE, ("now",))
    if now < 0:
        return _reject(LPDurationTransitionCodeV1.OUT_OF_RANGE, ("now",))
    if max(1, (now.bit_length() + 7) // 8) > MAX_CANONICAL_BYTES_V1:
        return _reject(LPDurationTransitionCodeV1.BYTE_LIMIT, ("now",))
    policy_reject = _policy_reject_v1(policy)
    if policy_reject is not None:
        return policy_reject
    if policy is not None:
        first_same_batch_index = next(
            (
                index
                for index, event in enumerate(events)
                if event.delta_add > 0 and event.delta_sub > 0
            ),
            None,
        )
        if first_same_batch_index is not None:
            return _reject(
                LPDurationTransitionCodeV1.SAME_BATCH_ADD_REMOVE,
                ("events", first_same_batch_index),
            )
    return _LPDurationInputsV1(
        pre,
        events,
        _LPDurationContextV1(now, policy),
    )


def _duration_writes_v1(
    inputs: _LPDurationInputsV1,
) -> tuple[LPPositionWriteV1, ...] | LPDurationTransitionRejectV1:
    writes_or_rejects = tuple(
        (
            index,
            event,
            _position_value_v1(inputs.pre, event.key),
        )
        for index, event in enumerate(inputs.events)
    )
    replacement_results = tuple(
        (
            index,
            event,
            current,
            _replacement_v1(
                current,
                event,
                event_index=index,
                context=inputs.context,
            ),
        )
        for index, event, current in writes_or_rejects
    )
    first_reject = next(
        (
            replacement
            for _index, _event, _current, replacement in replacement_results
            if type(replacement) is LPDurationTransitionRejectV1
        ),
        None,
    )
    if first_reject is not None:
        return first_reject
    return tuple(
        LPPositionWriteV1(
            event.key,
            current,
            cast(LPPositionValueV1, replacement),
        )
        for _index, event, current, replacement in replacement_results
        if replacement != current
    )


def _apply_duration_writes_v1(
    pre: CommittedLPTableV1,
    writes: tuple[LPPositionWriteV1, ...],
) -> LPDurationTransitionResultV1:
    if not writes:
        return LPDurationTransitionOkV1(pre, None)
    patch_result = build_canonical_lp_position_patch_v1(writes)
    if type(patch_result) is LPPositionPatchRejectV1:
        return _reject(
            LPDurationTransitionCodeV1.INVALID_CANDIDATE,
            ("patch",) + patch_result.path,
        )
    applied = apply_canonical_lp_position_patch_v1(pre, patch_result.patch)
    if type(applied) is not LPPositionPatchApplyOkV1:
        return _reject(
            LPDurationTransitionCodeV1.INVALID_CANDIDATE,
            ("patch",) + applied.path,
        )
    return LPDurationTransitionOkV1(applied.state, applied.patch)


def apply_lp_position_events_v1(
    pre_state: CommittedLPTableV1,
    events: tuple[LPDurationEventV1, ...],
    *,
    now: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> LPDurationTransitionResultV1:
    """Apply accepted LP balance and metadata events as one exact candidate."""

    inputs = _validated_inputs_v1(
        pre_state,
        events,
        now=now,
        policy=policy,
    )
    if type(inputs) is LPDurationTransitionRejectV1:
        return inputs
    writes = _duration_writes_v1(inputs)
    if type(writes) is LPDurationTransitionRejectV1:
        return writes
    return _apply_duration_writes_v1(inputs.pre, writes)


__all__ = (
    "LPDurationEventV1",
    "LPDurationRiskPolicyV1",
    "LPDurationTransitionCodeV1",
    "LPDurationTransitionOkV1",
    "LPDurationTransitionRejectV1",
    "LPDurationTransitionResultV1",
    "apply_lp_position_events_v1",
)
