"""
Fail-closed LP duration-risk checks for composition-sensitive liquidity flows.

The guard closes the trace shape behind JIT LP extraction:
ADD_LIQUIDITY -> fee-bearing batch activity -> REMOVE_LIQUIDITY before the LP
position has carried time risk. The runtime source of truth is LPTable's tracked
last-mint timestamp. Missing metadata rejects when the lock is enabled.
"""

from __future__ import annotations

from typing import Optional

from ..core.settlement import Settlement
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable


def _strict_non_negative_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


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


def validate_lp_position_age_gate(
    *,
    intents: list[Intent],
    lp_balances: object,
    block_timestamp: int,
    min_lp_position_age_seconds: int,
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
    if min_lp_position_age_seconds == 0:
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

        last_mint = lp_balances.get_last_mint_timestamp(intent.sender_pubkey, pool_id)
        if last_mint is None:
            return f"lp_position_age_missing for intent_id={intent.intent_id}"
        if not _strict_non_negative_int(last_mint):
            return f"invalid lp_position_mint_timestamp for intent_id={intent.intent_id}"
        if last_mint > block_timestamp:
            return f"lp_position_mint_timestamp_in_future for intent_id={intent.intent_id}"
        if block_timestamp - last_mint < min_lp_position_age_seconds:
            return f"lp_position_locked for intent_id={intent.intent_id}"

    for key in sorted(add_keys.intersection(remove_keys.keys())):
        intent = remove_keys[key]
        return f"same_batch_lp_add_remove_rejected for intent_id={intent.intent_id}"

    return None


def apply_lp_mint_timestamps_after_settlement(
    *,
    lp_balances: object,
    settlement: Settlement,
    block_timestamp: int,
) -> Optional[str]:
    """Update LP mint timestamps after a validated settlement has been applied."""
    if not isinstance(lp_balances, LPTable):
        return "invalid lp_balances for lp_mint_timestamp_update"
    if not _strict_non_negative_int(block_timestamp):
        return "invalid block_timestamp for lp_mint_timestamp_update"

    for delta in settlement.lp_deltas:
        if int(delta.delta_add) > 0:
            try:
                lp_balances.set_last_mint_timestamp(delta.pubkey, delta.pool_id, block_timestamp)
            except ValueError as exc:
                return f"lp_mint_timestamp_update_failed: {exc}"
        if lp_balances.get(delta.pubkey, delta.pool_id) == 0:
            lp_balances.clear_last_mint_timestamp(delta.pubkey, delta.pool_id)

    return None
