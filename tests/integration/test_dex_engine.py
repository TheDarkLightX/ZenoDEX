# [TESTER] v1

from __future__ import annotations

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.liquidity import create_pool
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _create_pool_intent_dict(*, intent_id: str, sender: str, asset0: str, asset1: str) -> dict:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }


def test_engine_computes_settlement_when_missing() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "01" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)

    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    ops = {"2": [_create_pool_intent_dict(intent_id=intent_id, sender=sender, asset0=asset0, asset1=asset1)]}
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error
    assert res.state is not None
    assert len(res.state.pools) == 1

    # Pool id is deterministic; spot-check reserves.
    pool_id, _pool_state, lp_minted = create_pool(
        asset0=min(asset0, asset1),
        asset1=max(asset0, asset1),
        amount0=1000,
        amount1=2000,
        fee_bps=30,
        creator_pubkey=sender,
        created_at=1,
    )
    assert pool_id in res.state.pools
    assert res.state.pools[pool_id].reserve0 == 1000
    assert res.state.pools[pool_id].reserve1 == 2000

    # Creator paid deposits.
    assert res.state.balances.get(sender, min(asset0, asset1)) == 0
    assert res.state.balances.get(sender, max(asset0, asset1)) == 0

    # Creator received LP (excluding MIN_LP_LOCK).
    assert res.state.lp_balances.get(sender, pool_id) == lp_minted


def test_engine_accepts_proof_fields_when_verifier_disabled() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = _create_pool_intent_dict(intent_id=intent_id, sender=sender, asset0=asset0, asset1=asset1)
    from src.integration.operations import parse_intents

    intents = parse_intents({"2": [intent_dict]})
    settlement = compute_settlement(intents=intents, pools={}, balances=balances, lp_balances=state.lp_balances)

    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["proof"] = {"scheme": "dummy", "note": "ignored when verifier disabled"}

    ops = {"2": [intent_dict], "3": settlement_op}
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=False, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_engine_rejects_large_raw_intent_before_parsing() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "ff" * 32

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    intent_dict = _create_pool_intent_dict(intent_id=intent_id, sender=sender, asset0=asset0, asset1=asset1)
    intent_dict["note"] = "A" * 2000

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            max_intent_entry_bytes=256,
            max_total_intent_entry_bytes=256,
        ),
        state=state,
        operations={"2": [intent_dict]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "intent operation too large" in res.error


def test_engine_unsigned_mode_rejects_tx_sender_mismatch() -> None:
    sender_intent = "0x" + "11" * 48
    sender_tx = "0x" + "22" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "ee" * 32

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    ops = {"2": [_create_pool_intent_dict(intent_id=intent_id, sender=sender_intent, asset0=asset0, asset1=asset1)]}
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender_tx,
    )
    assert not res.ok
    assert res.error is not None
    assert "intent sender mismatch" in res.error


def test_engine_is_noop_on_empty_ops_even_in_unsigned_mode() -> None:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),
        state=state,
        operations={},
        block_timestamp=0,
        tx_sender_pubkey=None,
    )
    assert res.ok, res.error
    assert res.state is state
    assert res.settlement is None


def test_engine_is_noop_on_explicit_empty_intents_even_in_unsigned_mode() -> None:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),
        state=state,
        operations={"2": []},
        block_timestamp=0,
        tx_sender_pubkey=None,
    )
    assert res.ok, res.error
    assert res.state is state
    assert res.settlement is None


def test_engine_rejects_conservation_only_malicious_settlement() -> None:
    alice = "0x" + "11" * 48
    bob = "0x" + "22" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "ab" * 32

    balances = BalanceTable()
    balances.set(bob, asset0, 100)

    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    # Intent references an unknown pool, so a locally computed settlement will reject it.
    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": intent_id,
        "sender_pubkey": alice,
        "deadline": 9999999999,
        "pool_id": "0x" + "ff" * 32,
        "asset_in": asset0,
        "asset_out": asset1,
        "amount_in": 1,
        "min_amount_out": 0,
    }

    # Malicious settlement that passes conservation/non-negativity but steals from Bob.
    settlement_op = {
        "module": "TauSwap",
        "version": "0.1",
        "included_intents": [[intent_id, "FILL"]],
        "fills": [{"intent_id": intent_id, "action": "FILL"}],
        "balance_deltas": [
            {"pubkey": bob, "asset": asset0, "delta_add": 0, "delta_sub": 10},
            {"pubkey": alice, "asset": asset0, "delta_add": 10, "delta_sub": 0},
        ],
        "reserve_deltas": [],
        "lp_deltas": [],
    }

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=False, require_intent_signatures=False),
        state=state,
        operations={"2": [intent_dict], "3": settlement_op},
        block_timestamp=0,
        tx_sender_pubkey=alice,
    )
    assert not res.ok
    assert res.error is not None
    assert "settlement mismatch" in res.error


def test_engine_rejects_settlement_without_intents() -> None:
    alice = "0x" + "11" * 48
    bob = "0x" + "22" * 48
    asset0 = "0x" + "11" * 32

    balances = BalanceTable()
    balances.set(bob, asset0, 100)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    settlement_op = {
        "module": "TauSwap",
        "version": "0.1",
        "included_intents": [],
        "fills": [],
        "balance_deltas": [
            {"pubkey": bob, "asset": asset0, "delta_add": 0, "delta_sub": 10},
            {"pubkey": alice, "asset": asset0, "delta_add": 10, "delta_sub": 0},
        ],
        "reserve_deltas": [],
        "lp_deltas": [],
    }

    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),
        state=state,
        operations={"3": settlement_op},
        block_timestamp=0,
        tx_sender_pubkey=None,
    )
    assert not res.ok
    assert res.error is not None
    assert "without intents" in res.error
