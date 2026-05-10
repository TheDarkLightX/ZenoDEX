from __future__ import annotations

from src.core.dex import DexState
from src.core.settlement import LPDelta, Settlement
from src.integration.dex_snapshot import (
    DEX_SNAPSHOT_VERSION,
    snapshot_from_state,
    state_from_snapshot,
)
from src.integration.lp_position_age_gate import (
    apply_lp_mint_timestamps_after_settlement,
    validate_lp_position_age_gate,
    validate_lp_settlement_age_gate,
)
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.state_root import compute_state_root
from src.state.support_root import compute_support_state_root_for_batch


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pk(byte: str = "11") -> str:
    return "0x" + byte * 48


def _pool(byte: str = "aa") -> str:
    return "0x" + byte * 32


def _liquidity_intent(
    *,
    kind: IntentKind,
    intent_id: str,
    sender: str,
    pool_id: str,
    fields: dict[str, object] | None = None,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=intent_id,
        sender_pubkey=sender,
        deadline=1_000,
        fields={"pool_id": pool_id, **(fields or {})},
    )


def test_lp_position_age_gate_is_inactive_when_min_age_is_zero() -> None:
    intent = _liquidity_intent(
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(1),
        sender=_pk(),
        pool_id=_pool(),
        fields={"lp_amount": 1},
    )

    err = validate_lp_position_age_gate(
        intents=[intent],
        lp_balances=LPTable(),
        block_timestamp=10,
        min_lp_position_age_seconds=0,
    )

    assert err is None


def test_lp_position_age_gate_rejects_missing_runtime_mint_timestamp() -> None:
    sender = _pk()
    pool_id = _pool()
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    intent = _liquidity_intent(
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(2),
        sender=sender,
        pool_id=pool_id,
        fields={"lp_amount": 1},
    )

    err = validate_lp_position_age_gate(
        intents=[intent],
        lp_balances=lp,
        block_timestamp=10,
        min_lp_position_age_seconds=2,
    )

    assert err == f"lp_position_age_missing for intent_id={intent.intent_id}"


def test_lp_position_age_gate_rejects_too_young_and_accepts_old_position() -> None:
    sender = _pk()
    pool_id = _pool()
    intent = _liquidity_intent(
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(3),
        sender=sender,
        pool_id=pool_id,
        fields={"lp_amount": 1},
    )
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    lp.set_last_mint_timestamp(sender, pool_id, 9)

    err = validate_lp_position_age_gate(
        intents=[intent],
        lp_balances=lp,
        block_timestamp=10,
        min_lp_position_age_seconds=2,
    )
    assert err == f"lp_position_locked for intent_id={intent.intent_id}"

    lp.set_last_mint_timestamp(sender, pool_id, 8)
    err = validate_lp_position_age_gate(
        intents=[intent],
        lp_balances=lp,
        block_timestamp=10,
        min_lp_position_age_seconds=2,
    )
    assert err is None


def test_lp_position_age_gate_rejects_same_batch_add_remove_for_same_owner_pool() -> None:
    sender = _pk()
    pool_id = _pool()
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    lp.set_last_mint_timestamp(sender, pool_id, 1)
    add = _liquidity_intent(
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(4),
        sender=sender,
        pool_id=pool_id,
        fields={"amount0_desired": 1, "amount1_desired": 1},
    )
    remove = _liquidity_intent(
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(5),
        sender=sender,
        pool_id=pool_id,
        fields={"lp_amount": 1},
    )

    err = validate_lp_position_age_gate(
        intents=[add, remove],
        lp_balances=lp,
        block_timestamp=10,
        min_lp_position_age_seconds=2,
    )

    assert err == f"same_batch_lp_add_remove_rejected for intent_id={remove.intent_id}"


def test_lp_settlement_age_gate_rejects_external_burn_without_remove_intent() -> None:
    sender = _pk()
    pool_id = _pool()
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=1)],
    )

    err = validate_lp_settlement_age_gate(
        settlement=settlement,
        intents=[],
        lp_balances=lp,
        block_timestamp=10,
        min_lp_position_age_seconds=2,
    )

    assert err == f"lp_position_age_missing for lp_delta={sender}:{pool_id}"


def test_lp_settlement_age_gate_rejects_recipient_directed_same_batch_add_remove() -> None:
    alice = _pk("11")
    bob = _pk("22")
    pool_id = _pool()
    lp = LPTable()
    lp.set(bob, pool_id, 10)
    lp.set_last_mint_timestamp(bob, pool_id, 1)
    add = _liquidity_intent(
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(7),
        sender=alice,
        pool_id=pool_id,
        fields={"recipient": bob, "amount0_desired": 1, "amount1_desired": 1},
    )
    remove = _liquidity_intent(
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(8),
        sender=bob,
        pool_id=pool_id,
        fields={"lp_amount": 1},
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=bob, pool_id=pool_id, delta_add=1, delta_sub=1)],
    )

    err = validate_lp_settlement_age_gate(
        settlement=settlement,
        intents=[add, remove],
        lp_balances=lp,
        block_timestamp=10,
        min_lp_position_age_seconds=2,
    )

    assert err == f"same_batch_lp_add_remove_rejected for intent_id={remove.intent_id}"


def test_lp_settlement_age_gate_accepts_old_effective_burn() -> None:
    sender = _pk()
    pool_id = _pool()
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    lp.set_last_mint_timestamp(sender, pool_id, 1)
    remove = _liquidity_intent(
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(9),
        sender=sender,
        pool_id=pool_id,
        fields={"lp_amount": 1},
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=1)],
    )

    err = validate_lp_settlement_age_gate(
        settlement=settlement,
        intents=[remove],
        lp_balances=lp,
        block_timestamp=10,
        min_lp_position_age_seconds=2,
    )

    assert err is None


def test_lp_mint_timestamp_update_and_state_root_binding() -> None:
    sender = _pk()
    pool_id = _pool()
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    before = compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=sender, pool_id=pool_id, delta_add=10, delta_sub=0)],
    )

    err = apply_lp_mint_timestamps_after_settlement(
        lp_balances=lp,
        settlement=settlement,
        block_timestamp=42,
    )

    assert err is None
    assert lp.get_last_mint_timestamp(sender, pool_id) == 42
    after = compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)
    assert after != before


def test_lp_mint_timestamp_support_root_binding() -> None:
    sender = _pk()
    pool_id = _pool()
    intent = _liquidity_intent(
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(6),
        sender=sender,
        pool_id=pool_id,
        fields={"lp_amount": 1},
    )
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    before = compute_support_state_root_for_batch(
        intents=[intent],
        balances=BalanceTable(),
        pools={},
        lp_balances=lp,
    )
    lp.set_last_mint_timestamp(sender, pool_id, 42)

    after = compute_support_state_root_for_batch(
        intents=[intent],
        balances=BalanceTable(),
        pools={},
        lp_balances=lp,
    )

    assert after != before


def test_lp_mint_timestamp_snapshot_roundtrip() -> None:
    sender = _pk()
    pool_id = _pool()
    lp = LPTable()
    lp.set(sender, pool_id, 10)
    lp.set_last_mint_timestamp(sender, pool_id, 42)
    snapshot = snapshot_from_state(DexState(balances=BalanceTable(), pools={}, lp_balances=lp)).data

    assert snapshot["version"] == DEX_SNAPSHOT_VERSION == 3
    assert "lp_mint_timestamps" in snapshot
    restored = state_from_snapshot(snapshot)

    assert restored.lp_balances.get(sender, pool_id) == 10
    assert restored.lp_balances.get_last_mint_timestamp(sender, pool_id) == 42


def test_snapshot_v3_requires_explicit_lp_mint_timestamp_section() -> None:
    snapshot = snapshot_from_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())).data
    snapshot.pop("lp_mint_timestamps")

    try:
        state_from_snapshot(snapshot)
    except ValueError as exc:
        assert str(exc) == "snapshot.lp_mint_timestamps is required for snapshot v3"
    else:  # pragma: no cover
        raise AssertionError("expected v3 snapshot without lp_mint_timestamps to reject")


def test_snapshot_strict_lp_age_migration_rejects_legacy_positive_lp_without_timestamp() -> None:
    sender = _pk()
    pool_id = _pool()
    snapshot = {
        "version": 2,
        "balances": [],
        "pools": [],
        "lp_balances": [{"pubkey": sender, "pool_id": pool_id, "amount": 10}],
        "nonces": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
        "perps": None,
    }

    restored = state_from_snapshot(snapshot)
    assert restored.lp_balances.get(sender, pool_id) == 10
    assert restored.lp_balances.get_last_mint_timestamp(sender, pool_id) is None

    try:
        state_from_snapshot(snapshot, require_lp_mint_timestamps=True)
    except ValueError as exc:
        assert str(exc) == f"missing lp_mint_timestamps entry for positive LP balance: {sender}:{pool_id}"
    else:  # pragma: no cover
        raise AssertionError("expected strict LP age migration check to reject")
