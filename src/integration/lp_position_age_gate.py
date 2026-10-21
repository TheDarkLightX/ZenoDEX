"""
Fail-closed LP duration-risk checks for composition-sensitive liquidity flows.

The guard closes the trace shape behind JIT LP extraction:
ADD_LIQUIDITY -> fee-bearing batch activity -> REMOVE_LIQUIDITY before the LP
position has carried time risk. The runtime source of truth is LPTable's tracked
last-mint timestamp. Missing metadata rejects when the lock is enabled.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from ..core.settlement import Settlement
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.lp_duration_policy_context import (
    admit_lp_duration_policy_fields_v1,
    admit_optional_lp_duration_policy_v1,
)
from ..state.lp_duration_policy_schema import LP_DURATION_POLICY_FIELD_NAMES_V1
from ..state.lp_duration_transitions import LPDurationRiskPolicyV1
from ..state.snapshot_combinators import AdmitCode, AdmitOk, AdmitReject


def _strict_non_negative_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


@dataclass(frozen=True)
class LPDurationRiskPolicy:
    """
    Progressive accepted-lifecycle cooldown for aggregate LP position keys.

    Churn escalation is based only on accepted LP add/remove lifecycle events.
    Rejected attempts do not mutate consensus state.
    """

    base_age_seconds: int = 0
    max_age_seconds: int = 0
    churn_window_seconds: int = 0
    decay_seconds: int = 0
    multiplier: int = 2
    max_churn_tier: int = 0

    def __post_init__(self) -> None:
        for name in (
            "base_age_seconds",
            "max_age_seconds",
            "churn_window_seconds",
            "decay_seconds",
            "max_churn_tier",
        ):
            value = getattr(self, name)
            if not _strict_non_negative_int(value):
                raise ValueError(f"{name} must be a non-negative int")
        if (
            not isinstance(self.multiplier, int)
            or isinstance(self.multiplier, bool)
            or self.multiplier < 1
        ):
            raise ValueError("multiplier must be an int >= 1")
        if self.max_age_seconds and self.base_age_seconds > self.max_age_seconds:
            raise ValueError("base_age_seconds must be <= max_age_seconds")

    def decayed_tier(self, tier: int, last_update_timestamp: Optional[int], now: int) -> int:
        if not _strict_non_negative_int(tier):
            raise ValueError("churn tier must be a non-negative int")
        if last_update_timestamp is not None and not _strict_non_negative_int(
            last_update_timestamp
        ):
            raise ValueError("last churn update timestamp must be a non-negative int")
        if not _strict_non_negative_int(now):
            raise ValueError("now must be a non-negative int")
        bounded_tier = (
            min(int(tier), int(self.max_churn_tier)) if self.max_churn_tier else int(tier)
        )
        if bounded_tier == 0 or self.decay_seconds == 0 or last_update_timestamp is None:
            return bounded_tier
        if last_update_timestamp > now:
            raise ValueError("last churn update timestamp cannot be in the future")
        decay_steps = (now - last_update_timestamp) // self.decay_seconds
        return max(0, bounded_tier - int(decay_steps))

    def required_age_seconds_for_tier(self, tier: int) -> int:
        if not _strict_non_negative_int(tier):
            raise ValueError("churn tier must be a non-negative int")
        if self.base_age_seconds == 0:
            return 0
        bounded_tier = (
            min(int(tier), int(self.max_churn_tier)) if self.max_churn_tier else int(tier)
        )
        age = int(self.base_age_seconds)
        for _ in range(bounded_tier):
            age *= int(self.multiplier)
            if self.max_age_seconds and age >= self.max_age_seconds:
                return int(self.max_age_seconds)
        if self.max_age_seconds:
            return min(age, int(self.max_age_seconds))
        return age


def admit_lp_duration_risk_policy_context_v1(
    source: object,
) -> AdmitOk[LPDurationRiskPolicyV1 | None] | AdmitReject:
    """Own the legacy shell policy through the closed context combinator.

    Field projection is deliberately non-semantic.  Range, type, cross-field,
    resource, construction, and canonical-encoding checks remain inside the
    source-bound admission profile.
    """

    if source is None or type(source) is LPDurationRiskPolicyV1:
        return admit_optional_lp_duration_policy_v1(source)
    if type(source) is not LPDurationRiskPolicy:
        return AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())
    try:
        raw_fields = object.__getattribute__(source, "__dict__")
    except AttributeError:
        return AdmitReject(AdmitCode.WRONG_CONTAINER, ())
    if type(raw_fields) is not dict:
        return AdmitReject(AdmitCode.WRONG_CONTAINER, ())
    for observed_name in dict.keys(raw_fields):
        if type(observed_name) is not str or observed_name not in LP_DURATION_POLICY_FIELD_NAMES_V1:
            return AdmitReject(AdmitCode.UNKNOWN_FIELD, ())
    for field_name in LP_DURATION_POLICY_FIELD_NAMES_V1:
        if not dict.__contains__(raw_fields, field_name):
            return AdmitReject(AdmitCode.MISSING_FIELD, (field_name,))
    return admit_lp_duration_policy_fields_v1(
        base_age_seconds=dict.__getitem__(raw_fields, "base_age_seconds"),
        max_age_seconds=dict.__getitem__(raw_fields, "max_age_seconds"),
        churn_window_seconds=dict.__getitem__(raw_fields, "churn_window_seconds"),
        decay_seconds=dict.__getitem__(raw_fields, "decay_seconds"),
        multiplier=dict.__getitem__(raw_fields, "multiplier"),
        max_churn_tier=dict.__getitem__(raw_fields, "max_churn_tier"),
    )


def _pool_id(intent: Intent) -> Optional[str]:
    pool_id = intent.get_field("pool_id")
    if isinstance(pool_id, str) and pool_id:
        return pool_id
    return None


def _lp_recipient(intent: Intent) -> Optional[str]:
    recipient = intent.get_field("recipient", intent.sender_pubkey)
    if isinstance(recipient, str) and recipient:
        return recipient
    return None


def _remove_context_by_key(intents: list[Intent]) -> dict[tuple[str, str], str]:
    contexts: dict[tuple[str, str], str] = {}
    for intent in intents:
        if intent.kind != IntentKind.REMOVE_LIQUIDITY:
            continue
        pool_id = _pool_id(intent)
        if pool_id is None:
            continue
        contexts[(intent.sender_pubkey, pool_id)] = f"intent_id={intent.intent_id}"
    return contexts


def _age_context(contexts: dict[tuple[str, str], str], key: tuple[str, str]) -> str:
    mapped = contexts.get(key)
    if mapped is not None:
        return mapped
    owner, pool_id = key
    return f"lp_delta={owner}:{pool_id}"


def _validate_lp_age_for_key(
    *,
    lp_balances: LPTable,
    owner: str,
    pool_id: str,
    block_timestamp: int,
    min_lp_position_age_seconds: int,
    duration_risk_policy: LPDurationRiskPolicy | None,
    context: str,
) -> Optional[str]:
    last_mint = lp_balances.get_last_mint_timestamp(owner, pool_id)
    if last_mint is None:
        return f"lp_position_age_missing for {context}"
    if not _strict_non_negative_int(last_mint):
        return f"invalid lp_position_mint_timestamp for {context}"
    if last_mint > block_timestamp:
        return f"lp_position_mint_timestamp_in_future for {context}"
    try:
        required_age = effective_lp_position_age_seconds(
            lp_balances=lp_balances,
            owner=owner,
            pool_id=pool_id,
            block_timestamp=block_timestamp,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            duration_risk_policy=duration_risk_policy,
        )
    except ValueError as exc:
        return f"invalid lp_duration_risk_metadata for {context}: {exc}"
    if block_timestamp - last_mint < required_age:
        return f"lp_position_locked for {context}"
    return None


def effective_lp_position_age_seconds(
    *,
    lp_balances: LPTable,
    owner: str,
    pool_id: str,
    block_timestamp: int,
    min_lp_position_age_seconds: int,
    duration_risk_policy: LPDurationRiskPolicy | None,
) -> int:
    """Return the fixed floor plus optional progressive churn cooldown."""
    if not _strict_non_negative_int(min_lp_position_age_seconds):
        raise ValueError("min_lp_position_age_seconds must be a non-negative int")
    if not _strict_non_negative_int(block_timestamp):
        raise ValueError("block_timestamp must be a non-negative int")
    fixed_floor = int(min_lp_position_age_seconds)
    if duration_risk_policy is None:
        return fixed_floor
    tier = duration_risk_policy.decayed_tier(
        lp_balances.get_churn_tier(owner, pool_id),
        lp_balances.get_last_churn_update_timestamp(owner, pool_id),
        int(block_timestamp),
    )
    return max(fixed_floor, duration_risk_policy.required_age_seconds_for_tier(tier))


def validate_lp_position_age_gate(
    *,
    intents: list[Intent],
    lp_balances: object,
    block_timestamp: int,
    min_lp_position_age_seconds: int,
    duration_risk_policy: LPDurationRiskPolicy | None = None,
) -> Optional[str]:
    """
    Validate runtime-bound LP position age before settlement.

    When enabled, REMOVE_LIQUIDITY burns require a tracked LP mint timestamp and
    the position must be at least `min_lp_position_age_seconds` old. Same-batch
    add/remove for the same LP owner and pool is rejected because a single
    aggregate LP balance cannot distinguish old lots from newly minted lots.
    """
    if not _strict_non_negative_int(min_lp_position_age_seconds):
        return "invalid min_lp_position_age_seconds"
    if min_lp_position_age_seconds == 0 and duration_risk_policy is None:
        return None
    if not _strict_non_negative_int(block_timestamp):
        return "invalid block_timestamp for lp_position_age_gate"
    if not isinstance(lp_balances, LPTable):
        return "invalid lp_balances for lp_position_age_gate"

    add_keys: set[tuple[str, str]] = set()
    remove_keys: dict[tuple[str, str], Intent] = {}

    for intent in intents:
        if intent.kind == IntentKind.ADD_LIQUIDITY:
            pool_id = _pool_id(intent)
            owner = _lp_recipient(intent)
            if pool_id is None or owner is None:
                return f"invalid ADD_LIQUIDITY LP age fields for intent_id={intent.intent_id}"
            add_keys.add((owner, pool_id))
            continue

        if intent.kind != IntentKind.REMOVE_LIQUIDITY:
            continue

        pool_id = _pool_id(intent)
        if pool_id is None:
            return f"invalid REMOVE_LIQUIDITY LP age fields for intent_id={intent.intent_id}"
        key = (intent.sender_pubkey, pool_id)
        remove_keys[key] = intent

        err = _validate_lp_age_for_key(
            lp_balances=lp_balances,
            owner=intent.sender_pubkey,
            pool_id=pool_id,
            block_timestamp=block_timestamp,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            duration_risk_policy=duration_risk_policy,
            context=f"intent_id={intent.intent_id}",
        )
        if err is not None:
            return err

    for key in sorted(add_keys.intersection(remove_keys.keys())):
        intent = remove_keys[key]
        return f"same_batch_lp_add_remove_rejected for intent_id={intent.intent_id}"

    return None


def validate_lp_settlement_age_gate(
    *,
    settlement: Settlement,
    intents: list[Intent],
    lp_balances: object,
    block_timestamp: int,
    min_lp_position_age_seconds: int,
    duration_risk_policy: LPDurationRiskPolicy | None = None,
) -> Optional[str]:
    """
    Validate the accepted settlement's LP burns against runtime age metadata.

    This is the authoritative runtime gate because `settlement.lp_deltas` are the
    actual LP state transition that `apply_settlement_pure()` will apply. The
    intent-level gate remains useful as a cheap syntactic checker, but production
    safety must be bound to the accepted delta set.
    """
    if not _strict_non_negative_int(min_lp_position_age_seconds):
        return "invalid min_lp_position_age_seconds"
    if min_lp_position_age_seconds == 0 and duration_risk_policy is None:
        return None
    if not _strict_non_negative_int(block_timestamp):
        return "invalid block_timestamp for lp_position_age_gate"
    if not isinstance(lp_balances, LPTable):
        return "invalid lp_balances for lp_position_age_gate"
    if not isinstance(settlement, Settlement):
        return "invalid settlement for lp_position_age_gate"

    contexts = _remove_context_by_key(intents)
    add_keys: set[tuple[str, str]] = set()
    remove_keys: set[tuple[str, str]] = set()

    for delta in settlement.lp_deltas:
        key = (delta.pubkey, delta.pool_id)
        if not _strict_non_negative_int(delta.delta_add):
            return f"invalid lp_delta_add for {_age_context(contexts, key)}"
        if not _strict_non_negative_int(delta.delta_sub):
            return f"invalid lp_delta_sub for {_age_context(contexts, key)}"
        if int(delta.delta_add) > 0:
            add_keys.add(key)
        if int(delta.delta_sub) > 0:
            remove_keys.add(key)

    for key in sorted(add_keys.intersection(remove_keys)):
        return f"same_batch_lp_add_remove_rejected for {_age_context(contexts, key)}"

    for key in sorted(remove_keys):
        err = _validate_lp_age_for_key(
            lp_balances=lp_balances,
            owner=key[0],
            pool_id=key[1],
            block_timestamp=block_timestamp,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            duration_risk_policy=duration_risk_policy,
            context=_age_context(contexts, key),
        )
        if err is not None:
            return err

    return None


def apply_lp_mint_timestamps_after_settlement(
    *,
    lp_balances: object,
    settlement: Settlement,
    block_timestamp: int,
    duration_risk_policy: LPDurationRiskPolicy | None = None,
) -> Optional[str]:
    """Update committed LP duration-risk metadata after a validated settlement."""
    if not isinstance(lp_balances, LPTable):
        return "invalid lp_balances for lp_mint_timestamp_update"
    if not _strict_non_negative_int(block_timestamp):
        return "invalid block_timestamp for lp_mint_timestamp_update"

    for delta in settlement.lp_deltas:
        try:
            _apply_lp_duration_risk_delta(
                lp_balances=lp_balances,
                owner=delta.pubkey,
                pool_id=delta.pool_id,
                delta_add=int(delta.delta_add),
                delta_sub=int(delta.delta_sub),
                block_timestamp=block_timestamp,
                duration_risk_policy=duration_risk_policy,
            )
        except ValueError as exc:
            return f"lp_duration_risk_update_failed: {exc}"

    return None


def _apply_lp_duration_risk_delta(
    *,
    lp_balances: LPTable,
    owner: str,
    pool_id: str,
    delta_add: int,
    delta_sub: int,
    block_timestamp: int,
    duration_risk_policy: LPDurationRiskPolicy | None,
) -> None:
    if not _strict_non_negative_int(delta_add):
        raise ValueError("delta_add must be a non-negative int")
    if not _strict_non_negative_int(delta_sub):
        raise ValueError("delta_sub must be a non-negative int")
    if delta_add > 0 and duration_risk_policy is not None:
        tier = duration_risk_policy.decayed_tier(
            lp_balances.get_churn_tier(owner, pool_id),
            lp_balances.get_last_churn_update_timestamp(owner, pool_id),
            block_timestamp,
        )
        last_remove = lp_balances.get_last_remove_timestamp(owner, pool_id)
        last_mint = lp_balances.get_last_mint_timestamp(owner, pool_id)
        recent_remove = (
            last_remove is not None
            and last_remove <= block_timestamp
            and block_timestamp - last_remove <= duration_risk_policy.churn_window_seconds
        )
        recent_mint = (
            last_mint is not None
            and last_mint <= block_timestamp
            and block_timestamp - last_mint <= duration_risk_policy.churn_window_seconds
        )
        if recent_remove or recent_mint:
            tier += 1
        if duration_risk_policy.max_churn_tier:
            tier = min(tier, duration_risk_policy.max_churn_tier)
        lp_balances.set_churn_tier(owner, pool_id, tier)
        lp_balances.set_last_churn_update_timestamp(owner, pool_id, block_timestamp)

    if delta_sub > 0 and duration_risk_policy is not None:
        lp_balances.set_last_remove_timestamp(owner, pool_id, block_timestamp)

    if delta_add > 0:
        lp_balances.set_last_mint_timestamp(owner, pool_id, block_timestamp)
    if lp_balances.get(owner, pool_id) == 0:
        lp_balances.clear_last_mint_timestamp(owner, pool_id)
