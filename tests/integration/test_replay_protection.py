# [TESTER] v1

from __future__ import annotations

from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _create_pool_intent(
    *,
    intent_id: str,
    sender: str,
    nonce: int | None,
    asset0: str,
    asset1: str,
    amount0: int,
    amount1: int,
    created_at: int,
) -> dict:
    d = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": int(amount0),
        "amount1": int(amount1),
        "created_at": int(created_at),
    }
    if nonce is not None:
        d["nonce"] = int(nonce)
    return d


def test_replay_protection_rejects_reused_nonce() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state0 = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_id1 = "0x" + "01" * 32
    intent_id2 = "0x" + "02" * 32

    intent1 = _create_pool_intent(
        intent_id=intent_id1,
        sender=sender,
        nonce=1,
        asset0=asset0,
        asset1=asset1,
        amount0=1000,
        amount1=2000,
        created_at=1,
    )
    res1 = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state0,
        operations={"2": [intent1]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res1.ok, res1.error
    assert res1.state is not None
    assert res1.state.nonces.get_last(sender) == 1

    # Replay with the same nonce should fail (even if intent_id differs).
    intent2 = _create_pool_intent(
        intent_id=intent_id2,
        sender=sender,
        nonce=1,
        asset0=asset0,
        asset1=asset1,
        amount0=1000,
        amount1=2000,
        created_at=2,
    )
    res2 = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=res1.state,
        operations={"2": [intent2]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res2.ok
    assert res2.error is not None
    assert "nonce sequence invalid" in res2.error or "nonce" in res2.error


def test_replay_protection_accepts_out_of_order_batch_nonces_and_advances() -> None:
    sender = "0x" + "aa" * 48
    a0 = "0x" + "11" * 32
    a1 = "0x" + "22" * 32
    a2 = "0x" + "33" * 32
    a3 = "0x" + "44" * 32

    balances = BalanceTable()
    for asset in (a0, a1, a2, a3):
        balances.set(sender, asset, 10_000)
    state0 = DexState(balances=balances, pools={}, lp_balances=LPTable())

    # Nonces are 2 then 1 (input order), but should validate as {1,2}.
    intent1 = _create_pool_intent(
        intent_id="0x" + "01" * 32,
        sender=sender,
        nonce=2,
        asset0=a0,
        asset1=a1,
        amount0=1000,
        amount1=1000,
        created_at=1,
    )
    intent2 = _create_pool_intent(
        intent_id="0x" + "02" * 32,
        sender=sender,
        nonce=1,
        asset0=a2,
        asset1=a3,
        amount0=1000,
        amount1=1000,
        created_at=2,
    )

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state0,
        operations={"2": [intent1, intent2]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error
    assert res.state is not None
    assert res.state.nonces.get_last(sender) == 2


def test_replay_protection_rejects_duplicate_nonce_in_batch() -> None:
    sender = "0x" + "aa" * 48
    a0 = "0x" + "11" * 32
    a1 = "0x" + "22" * 32
    a2 = "0x" + "33" * 32
    a3 = "0x" + "44" * 32

    balances = BalanceTable()
    for asset in (a0, a1, a2, a3):
        balances.set(sender, asset, 10_000)
    state0 = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent1 = _create_pool_intent(
        intent_id="0x" + "01" * 32,
        sender=sender,
        nonce=1,
        asset0=a0,
        asset1=a1,
        amount0=1000,
        amount1=1000,
        created_at=1,
    )
    intent2 = _create_pool_intent(
        intent_id="0x" + "02" * 32,
        sender=sender,
        nonce=1,
        asset0=a2,
        asset1=a3,
        amount0=1000,
        amount1=1000,
        created_at=2,
    )

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state0,
        operations={"2": [intent1, intent2]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "duplicate nonce" in res.error or "nonce" in res.error


def test_replay_protection_rejects_gap_nonce_in_batch() -> None:
    sender = "0x" + "aa" * 48
    a0 = "0x" + "11" * 32
    a1 = "0x" + "22" * 32
    a2 = "0x" + "33" * 32
    a3 = "0x" + "44" * 32

    balances = BalanceTable()
    for asset in (a0, a1, a2, a3):
        balances.set(sender, asset, 10_000)
    state0 = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent1 = _create_pool_intent(
        intent_id="0x" + "01" * 32,
        sender=sender,
        nonce=1,
        asset0=a0,
        asset1=a1,
        amount0=1000,
        amount1=1000,
        created_at=1,
    )
    intent2 = _create_pool_intent(
        intent_id="0x" + "02" * 32,
        sender=sender,
        nonce=3,
        asset0=a2,
        asset1=a3,
        amount0=1000,
        amount1=1000,
        created_at=2,
    )

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state0,
        operations={"2": [intent1, intent2]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "nonce sequence invalid" in res.error or "nonce" in res.error


def test_replay_protection_rejects_missing_nonce_field() -> None:
    sender = "0x" + "aa" * 48
    a0 = "0x" + "11" * 32
    a1 = "0x" + "22" * 32

    balances = BalanceTable()
    balances.set(sender, min(a0, a1), 10_000)
    balances.set(sender, max(a0, a1), 10_000)
    state0 = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent1 = _create_pool_intent(
        intent_id="0x" + "01" * 32,
        sender=sender,
        nonce=None,
        asset0=a0,
        asset1=a1,
        amount0=1000,
        amount1=1000,
        created_at=1,
    )
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state0,
        operations={"2": [intent1]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "Missing/invalid nonce" in res.error or "nonce" in res.error


def test_sender_pubkey_is_canonicalized_for_nonce_accounting() -> None:
    sender_raw = "0x" + "AA" * 48
    sender = sender_raw.lower()
    a0 = "0x" + "11" * 32
    a1 = "0x" + "22" * 32

    balances = BalanceTable()
    balances.set(sender, min(a0, a1), 10_000)
    balances.set(sender, max(a0, a1), 10_000)
    state0 = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent1 = _create_pool_intent(
        intent_id="0x" + "01" * 32,
        sender=sender_raw,
        nonce=1,
        asset0=a0,
        asset1=a1,
        amount0=1000,
        amount1=1000,
        created_at=1,
    )
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state0,
        operations={"2": [intent1]},
        block_timestamp=0,
        tx_sender_pubkey=sender_raw,
    )
    assert res.ok, res.error
    assert res.state is not None
    assert res.state.nonces.get_last(sender) == 1
    # Case/prefix variants should hit the same nonce stream.
    assert res.state.nonces.get_last(sender_raw) == 1
