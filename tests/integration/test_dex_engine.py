# [TESTER] v1

from __future__ import annotations

import pytest

from src.agents.intent_signer import (
    create_swap_intent_from_quote_receipt,
    create_swap_intents_from_quote_receipt,
    sign_intent,
)
from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.liquidity import create_pool
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.core.settlement import LPDelta, Settlement
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import (
    SignedIntentEnvelope,
    create_settlement_operation,
    create_signed_intent_operation,
    parse_intents,
)
from src.integration.proof_verifier import ProofVerifierConfig
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus


def _create_pool_intent_dict(*, intent_id: str, sender: str, asset0: str, asset1: str) -> dict:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }


def test_engine_config_default_swap_ordering_is_explicitly_greedy_ab_refined() -> None:
    cfg = DexEngineConfig()
    assert cfg.swap_ordering == "greedy_ab_refined"


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
    assert res.state.lp_balances.get_last_mint_timestamp(sender, pool_id) == 0


def test_engine_rejects_remove_liquidity_before_runtime_lp_age_lock_expires() -> None:
    sender = "0x" + "ab" * 48
    asset0 = "0x" + "13" * 32
    asset1 = "0x" + "14" * 32
    pool_id = "0x" + "15" * 32
    lp = LPTable()
    lp.set(sender, pool_id, 100)
    lp.set_last_mint_timestamp(sender, pool_id, 10)
    state = DexState(
        balances=BalanceTable(),
        pools={
            pool_id: PoolState(
                pool_id=pool_id,
                asset0=asset0,
                asset1=asset1,
                reserve0=1_000,
                reserve1=1_000,
                fee_bps=30,
                lp_supply=1_000,
                status=PoolStatus.ACTIVE,
                created_at=0,
                curve_tag="CPMM",
                curve_params="",
            )
        },
        lp_balances=lp,
    )
    ops = {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "REMOVE_LIQUIDITY",
                "intent_id": "0x" + "16" * 32,
                "sender_pubkey": sender,
                "deadline": 100,
                "nonce": 1,
                "pool_id": pool_id,
                "lp_amount": 10,
                "amount0_min": 0,
                "amount1_min": 0,
            }
        ]
    }

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            min_lp_position_age_seconds=20,
        ),
        state=state,
        operations=ops,
        block_timestamp=15,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error == "lp_position_locked for intent_id=" + "0x" + "16" * 32
    assert state.lp_balances.get(sender, pool_id) == 100


def test_engine_accepts_remove_liquidity_after_runtime_lp_age_lock_expires() -> None:
    sender = "0x" + "ac" * 48
    asset0 = "0x" + "17" * 32
    asset1 = "0x" + "18" * 32
    pool_id = "0x" + "19" * 32
    lp = LPTable()
    lp.set(sender, pool_id, 100)
    lp.set_last_mint_timestamp(sender, pool_id, 10)
    state = DexState(
        balances=BalanceTable(),
        pools={
            pool_id: PoolState(
                pool_id=pool_id,
                asset0=asset0,
                asset1=asset1,
                reserve0=1_000,
                reserve1=1_000,
                fee_bps=30,
                lp_supply=1_000,
                status=PoolStatus.ACTIVE,
                created_at=0,
                curve_tag="CPMM",
                curve_params="",
            )
        },
        lp_balances=lp,
    )
    intent_id = "0x" + "1a" * 32
    ops = {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "REMOVE_LIQUIDITY",
                "intent_id": intent_id,
                "sender_pubkey": sender,
                "deadline": 100,
                "nonce": 1,
                "pool_id": pool_id,
                "lp_amount": 10,
                "amount0_min": 0,
                "amount1_min": 0,
            }
        ]
    }

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            min_lp_position_age_seconds=20,
        ),
        state=state,
        operations=ops,
        block_timestamp=30,
        tx_sender_pubkey=sender,
    )

    assert res.ok, res.error
    assert res.state is not None
    assert res.state.lp_balances.get(sender, pool_id) == 90
    assert res.state.lp_balances.get_last_mint_timestamp(sender, pool_id) == 10


def test_engine_rejects_same_batch_lp_add_remove_under_age_gate() -> None:
    sender = "0x" + "ad" * 48
    asset0 = "0x" + "1b" * 32
    asset1 = "0x" + "1c" * 32
    pool_id = "0x" + "1d" * 32
    balances = BalanceTable()
    balances.set(sender, asset0, 1_000)
    balances.set(sender, asset1, 1_000)
    lp = LPTable()
    lp.set(sender, pool_id, 100)
    lp.set_last_mint_timestamp(sender, pool_id, 1)
    state = DexState(
        balances=balances,
        pools={
            pool_id: PoolState(
                pool_id=pool_id,
                asset0=asset0,
                asset1=asset1,
                reserve0=1_000,
                reserve1=1_000,
                fee_bps=30,
                lp_supply=1_000,
                status=PoolStatus.ACTIVE,
                created_at=0,
                curve_tag="CPMM",
                curve_params="",
            )
        },
        lp_balances=lp,
    )
    remove_id = "0x" + "1f" * 32
    ops = {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "ADD_LIQUIDITY",
                "intent_id": "0x" + "1e" * 32,
                "sender_pubkey": sender,
                "deadline": 100,
                "nonce": 1,
                "pool_id": pool_id,
                "amount0_desired": 100,
                "amount1_desired": 100,
                "amount0_min": 0,
                "amount1_min": 0,
            },
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "REMOVE_LIQUIDITY",
                "intent_id": remove_id,
                "sender_pubkey": sender,
                "deadline": 100,
                "nonce": 2,
                "pool_id": pool_id,
                "lp_amount": 10,
                "amount0_min": 0,
                "amount1_min": 0,
            },
        ]
    }

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            min_lp_position_age_seconds=1,
        ),
        state=state,
        operations=ops,
        block_timestamp=30,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error == f"same_batch_lp_add_remove_rejected for intent_id={remove_id}"


def test_engine_rejects_supplied_settlement_lp_burn_when_settlement_match_disabled() -> None:
    sender = "0x" + "ae" * 48
    asset0 = "0x" + "21" * 32
    asset1 = "0x" + "22" * 32
    pool_id = "0x" + "20" * 32
    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1_000)
    balances.set(sender, max(asset0, asset1), 1_000)
    lp = LPTable()
    lp.set(sender, pool_id, 100)
    lp.set_last_mint_timestamp(sender, pool_id, 10)
    state = DexState(balances=balances, pools={}, lp_balances=lp)
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="external",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=10)],
    )
    ops = {
        "2": [
            _create_pool_intent_dict(
                intent_id="0x" + "23" * 32,
                sender=sender,
                asset0=asset0,
                asset1=asset1,
            )
        ],
        **create_settlement_operation(settlement),
    }

    res = apply_ops(
        config=DexEngineConfig(
            require_settlement_match=False,
            require_intent_signatures=False,
            min_lp_position_age_seconds=20,
        ),
        state=state,
        operations=ops,
        block_timestamp=15,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error == f"lp_position_locked for lp_delta={sender}:{pool_id}"
    assert state.lp_balances.get(sender, pool_id) == 100


def test_engine_rejects_signature_valid_cross_batch_nonce_replay_without_mutation() -> None:
    pytest.importorskip("py_ecc")

    privkey = 7
    sender = "0x" + bls_pubkey_hex_from_privkey(privkey)
    asset0 = "0x" + "31" * 32
    asset1 = "0x" + "32" * 32
    intent_id = "0x" + "36" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    nonces = NonceTable()
    nonces.set_last(sender, 1)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable(), nonces=nonces)

    intent = parse_intents(
        {
            "2": [
                _create_pool_intent_dict(
                    intent_id=intent_id,
                    sender=sender,
                    asset0=asset0,
                    asset1=asset1,
                )
            ]
        }
    )[0]
    signed = sign_intent(intent, privkey, chain_id="tau-net-alpha")
    ops = create_signed_intent_operation(
        [SignedIntentEnvelope(intent=signed.intent, signature=signed.signature)]
    )

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=False,
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=None,
    )

    assert not res.ok
    assert res.error == "nonce sequence invalid"
    assert res.state is None
    assert res.settlement is None
    assert state.nonces.get_last(sender) == 1
    assert state.pools == {}
    assert state.balances.get(sender, min(asset0, asset1)) == 1000
    assert state.balances.get(sender, max(asset0, asset1)) == 2000


def test_engine_rejects_unsigned_live_admission_nonce_replay_without_mutation() -> None:
    sender = "0x" + "39" * 48
    asset0 = "0x" + "33" * 32
    asset1 = "0x" + "34" * 32
    intent_id = "0x" + "39" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    nonces = NonceTable()
    nonces.set_last(sender, 1)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable(), nonces=nonces)
    ops = {
        "2": [
            _create_pool_intent_dict(
                intent_id=intent_id,
                sender=sender,
                asset0=asset0,
                asset1=asset1,
            )
        ]
    }

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=True,
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error == "nonce sequence invalid"
    assert res.state is None
    assert res.settlement is None
    assert state.nonces.get_last(sender) == 1
    assert state.pools == {}
    assert state.balances.get(sender, min(asset0, asset1)) == 1000
    assert state.balances.get(sender, max(asset0, asset1)) == 2000


def test_engine_rejects_signed_intent_rebound_to_wrong_sender_without_nonce_mutation() -> None:
    pytest.importorskip("py_ecc")

    signing_privkey = 40
    signer = "0x" + bls_pubkey_hex_from_privkey(signing_privkey)
    rebound_sender = "0x" + bls_pubkey_hex_from_privkey(41)
    asset0 = "0x" + "40" * 32
    asset1 = "0x" + "41" * 32
    intent_id = "0x" + "40" * 32

    signed_intent_dict = _create_pool_intent_dict(
        intent_id=intent_id,
        sender=signer,
        asset0=asset0,
        asset1=asset1,
    )
    intent = parse_intents({"2": [signed_intent_dict]})[0]
    signed = sign_intent(intent, signing_privkey, chain_id="tau-net-alpha")
    rebound_intent_dict = dict(signed_intent_dict, sender_pubkey=rebound_sender, signature=signed.signature)

    balances = BalanceTable()
    balances.set(rebound_sender, min(asset0, asset1), 1000)
    balances.set(rebound_sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable(), nonces=NonceTable())

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=False,
        ),
        state=state,
        operations={"2": [rebound_intent_dict]},
        block_timestamp=0,
        tx_sender_pubkey=None,
    )

    assert not res.ok
    assert res.error == f"intent signature invalid: {intent_id}: invalid intent signature"
    assert res.state is None
    assert res.settlement is None
    assert state.nonces.get_last(signer) == 0
    assert state.nonces.get_last(rebound_sender) == 0
    assert state.pools == {}
    assert state.balances.get(rebound_sender, min(asset0, asset1)) == 1000
    assert state.balances.get(rebound_sender, max(asset0, asset1)) == 2000


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
    assert res.proof_mining_context is None


def test_engine_accepts_provided_swap_settlement_with_reserve_witness_roundtrip() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id = "0x" + "33" * 32
    intent_id = "0x" + "05" * 32

    balances = BalanceTable()
    balances.set(sender, asset0, 10_000)
    balances.set(sender, asset1, 0)
    state = DexState(
        balances=balances,
        pools={
            pool_id: PoolState(
                pool_id=pool_id,
                asset0=asset0,
                asset1=asset1,
                reserve0=5_000,
                reserve1=5_000,
                fee_bps=30,
                lp_supply=1,
                status=PoolStatus.ACTIVE,
                created_at=0,
                curve_tag="CPMM",
                curve_params="",
            )
        },
        lp_balances=LPTable(),
    )

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "pool_id": pool_id,
        "asset_in": asset0,
        "asset_out": asset1,
        "amount_in": 100,
        "min_amount_out": 1,
    }
    from src.integration.operations import parse_intents

    intents = parse_intents({"2": [intent_dict]})
    settlement = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=balances,
        lp_balances=state.lp_balances,
    )
    assert settlement.fills
    assert settlement.fills[0].reserve_in_before is not None
    assert settlement.fills[0].reserve_out_before is not None

    settlement_op = create_settlement_operation(settlement)["3"]
    assert settlement_op["fills"][0]["reserve_in_before"] == settlement.fills[0].reserve_in_before
    assert settlement_op["fills"][0]["reserve_out_before"] == settlement.fills[0].reserve_out_before

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
        ),
        state=state,
        operations={"2": [intent_dict], "3": settlement_op},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_engine_accepts_matching_attached_quote_receipt_witness() -> None:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent.set_field("nonce", 1)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_engine_accepts_complete_split_quote_receipt_batch() -> None:
    sender = "0x" + "ab" * 48
    pools = {
        "p1": PoolState(
            pool_id="p1",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
        "p2": PoolState(
            pool_id="p2",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert q is not None
    assert len(q.legs) >= 2
    assert all(len(leg.hops) == 1 for leg in q.legs)
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=1,
    )
    ops = create_signed_intent_operation(
        [SignedIntentEnvelope(intent=intent, quote_receipt=receipt) for intent in intents]
    )

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_engine_rejects_attached_quote_receipt_hash_mismatch() -> None:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent.set_field("nonce", 1)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    ops["2"][0]["quote_receipt_hash"] = "0xdeadbeef"

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "quote receipt hash mismatch" in res.error
    assert f"intent_id='{intent.intent_id}'" in res.error
    assert "quote_hash='0xdeadbeef'" in res.error
    assert f"witness_hash='{receipt['receipt_hash']}'" in res.error


def test_engine_rejects_quote_bound_intent_without_leg_index() -> None:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent.set_field("nonce", 1)
    intent.fields.pop("quote_receipt_leg_index", None)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "missing quote_receipt_leg_index" in res.error
    assert f"intent_id='{intent.intent_id}'" in res.error
    assert "direct quote-bound intents must bind exactly one receipt leg" in res.error


def test_engine_rejects_quote_bound_intent_without_attached_receipt_witness() -> None:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent.set_field("nonce", 1)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent)])

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "missing quote receipt witness" in res.error
    assert f"intent_id='{intent.intent_id}'" in res.error


def test_engine_rejects_duplicate_split_quote_receipt_leg_binding() -> None:
    sender = "0x" + "ac" * 48
    pools = {
        "p1": PoolState(
            pool_id="p1",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
        "p2": PoolState(
            pool_id="p2",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=1,
    )
    ops = create_signed_intent_operation(
        [SignedIntentEnvelope(intent=intent, quote_receipt=receipt) for intent in intents]
    )
    duplicate = dict(ops["2"][0])
    duplicate["intent_id"] = "0x" + "de" * 32
    duplicate["nonce"] = 99
    ops["2"].append(duplicate)

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "duplicate quote receipt leg binding" in res.error
    assert f"quote_hash='{receipt['receipt_hash']}'" in res.error
    assert "duplicate_leg_indices=[0]" in res.error


def test_engine_rejects_bool_quote_receipt_leg_index() -> None:
    sender = "0x" + "ad" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent.set_field("nonce", 1)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    ops["2"][0]["quote_receipt_leg_index"] = True

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "intent.quote_receipt_leg_index must be an int" in res.error


def test_engine_rejects_incomplete_split_quote_receipt_leg_coverage() -> None:
    sender = "0x" + "ae" * 48
    pools = {
        "p1": PoolState(
            pool_id="p1",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
        "p2": PoolState(
            pool_id="p2",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=1,
    )
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intents[0], quote_receipt=receipt)])

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "incomplete quote receipt leg coverage" in res.error
    assert "expected_leg_indices=[0, 1]" in res.error
    assert "observed_leg_indices=[0]" in res.error


def test_engine_prefers_duplicate_quote_receipt_error_before_incomplete_coverage() -> None:
    sender = "0x" + "af" * 48
    pools = {
        "p1": PoolState(
            pool_id="p1",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
        "p2": PoolState(
            pool_id="p2",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=1,
    )
    duplicate = SignedIntentEnvelope(intent=intents[0], quote_receipt=receipt)
    ops = create_signed_intent_operation(
        [SignedIntentEnvelope(intent=intents[0], quote_receipt=receipt), duplicate]
    )
    ops["2"][1]["intent_id"] = "0x" + "ef" * 32
    ops["2"][1]["nonce"] = 99

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "duplicate quote receipt leg binding" in res.error
    assert "incomplete quote receipt leg coverage" not in res.error


def test_engine_scopes_quote_receipt_leg_indices_per_receipt_hash() -> None:
    sender = "0x" + "b0" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=5_000,
            reserve1=5_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    quote_a = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    quote_b = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=124)
    assert quote_a is not None
    assert quote_b is not None
    receipt_a = make_route_quote_receipt(kind="exact_in", quote=quote_a, pools_by_id=pools)
    receipt_b = make_route_quote_receipt(kind="exact_in", quote=quote_b, pools_by_id=pools)
    intent_a = create_swap_intent_from_quote_receipt(
        receipt=receipt_a,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent_b = create_swap_intent_from_quote_receipt(
        receipt=receipt_b,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent_a.set_field("nonce", 1)
    intent_b.set_field("nonce", 2)
    ops = create_signed_intent_operation(
        [
            SignedIntentEnvelope(intent=intent_a, quote_receipt=receipt_a),
            SignedIntentEnvelope(intent=intent_b, quote_receipt=receipt_b),
        ]
    )

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
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


def test_engine_rejects_total_raw_intent_bytes_before_parsing() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    intent_a = _create_pool_intent_dict(
        intent_id="0x" + "01" * 32,
        sender=sender,
        asset0=asset0,
        asset1=asset1,
    )
    intent_b = _create_pool_intent_dict(
        intent_id="0x" + "02" * 32,
        sender=sender,
        asset0=asset0,
        asset1=asset1,
    )
    intent_a["note"] = "A" * 300
    intent_b["note"] = "B" * 300

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            max_intent_entry_bytes=1024,
            max_total_intent_entry_bytes=700,
        ),
        state=state,
        operations={"2": [intent_a, intent_b]},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "total intent operation too large" in res.error


def test_engine_rejects_too_many_settlement_fills_before_parsing() -> None:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    settlement_op = {
        "module": "TauSwap",
        "version": "0.1",
        "fills": [{}, {}],
    }

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            max_settlement_fills=1,
        ),
        state=state,
        operations={"3": settlement_op},
        block_timestamp=0,
        tx_sender_pubkey=None,
    )
    assert not res.ok
    assert res.error is not None
    assert "too many settlement fills" in res.error


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
        "nonce": 1,
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


def test_engine_accepts_semantically_equivalent_settlement_when_match_required() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "03" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = _create_pool_intent_dict(intent_id=intent_id, sender=sender, asset0=asset0, asset1=asset1)
    from src.integration.operations import parse_intents

    intents = parse_intents({"2": [intent_dict]})
    settlement = compute_settlement(intents=intents, pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_op = create_settlement_operation(settlement)["3"]

    # Reorder and split one delta entry into duplicates; this should remain
    # semantically equivalent after normalization.
    settlement_op["included_intents"] = list(reversed(settlement_op.get("included_intents", [])))
    settlement_op["fills"] = list(reversed(settlement_op.get("fills", [])))
    settlement_op["balance_deltas"] = list(reversed(settlement_op.get("balance_deltas", [])))
    settlement_op["reserve_deltas"] = list(reversed(settlement_op.get("reserve_deltas", [])))
    settlement_op["lp_deltas"] = list(reversed(settlement_op.get("lp_deltas", [])))

    if settlement_op["balance_deltas"]:
        first = dict(settlement_op["balance_deltas"].pop(0))
        add_total = int(first.get("delta_add", 0))
        sub_total = int(first.get("delta_sub", 0))
        left = dict(first)
        right = dict(first)
        left["delta_add"] = add_total // 2
        right["delta_add"] = add_total - left["delta_add"]
        left["delta_sub"] = sub_total // 2
        right["delta_sub"] = sub_total - left["delta_sub"]
        settlement_op["balance_deltas"].extend([left, right])

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_settlement_match=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations={"2": [intent_dict], "3": settlement_op},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_engine_rejects_oversized_proof_payload_before_verifier() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "04" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = _create_pool_intent_dict(intent_id=intent_id, sender=sender, asset0=asset0, asset1=asset1)
    from src.integration.operations import parse_intents

    intents = parse_intents({"2": [intent_dict]})
    settlement = compute_settlement(intents=intents, pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["proof"] = {"scheme": "dummy", "blob": "x" * 512}

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            proof_config=ProofVerifierConfig(max_proof_bytes=128),
        ),
        state=state,
        operations={"2": [intent_dict], "3": settlement_op},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "proof payload too large" in res.error


# ---------------------------------------------------------------------------
# Characterization (golden) tests for apply_ops orchestration.
#
# apply_ops is a single ~118-complexity validate -> compute -> apply pipeline.
# These tests pin its CURRENT externally observable behavior so a
# behavior-preserving complexity refactor can be verified bit-identically:
#   * a successful multi-op application (resulting state + event/effect order),
#   * one rejecting case per extracted block with the EXACT reject string,
#   * the documented reject PRECEDENCE between guards,
#   * an unknown / malformed op,
#   * no-op-on-reject (a rejected batch leaves state byte-for-byte unchanged).
#
# The uniform-batch fixtures below are deliberately self-contained replicas of
# the ones in test_dex_engine_uniform_batch_certificate.py so this file is its
# own oracle for the uniform-batch + cross-check + settlement-match blocks.
# ---------------------------------------------------------------------------

from hashlib import sha256 as _gold_sha256

_GOLD_SENDER = "0x" + "aa" * 48


def _gold_intent_id(label: str) -> str:
    return "0x" + _gold_sha256(label.encode("utf-8")).hexdigest()


def _gold_pool() -> PoolState:
    return PoolState(
        pool_id="pool_ab",
        asset0="A",
        asset1="B",
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _gold_state() -> DexState:
    balances = BalanceTable()
    balances.set(_GOLD_SENDER, "A", 1_000)
    balances.set(_GOLD_SENDER, "B", 1_000)
    return DexState(balances=balances, pools={"pool_ab": _gold_pool()}, lp_balances=LPTable())


def _gold_swap_dict(*, label: str, asset_in: str, asset_out: str, nonce: int) -> dict:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": _gold_intent_id(label),
        "sender_pubkey": _GOLD_SENDER,
        "deadline": 999_999_999,
        "nonce": nonce,
        "pool_id": "pool_ab",
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": 100,
        "min_amount_out": 90,
    }


def _gold_intent(*, label: str, asset_in: str, asset_out: str, nonce: int):
    from src.state.intents import Intent, IntentKind

    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_gold_intent_id(label),
        sender_pubkey=_GOLD_SENDER,
        deadline=999_999_999,
        fields={
            "nonce": nonce,
            "pool_id": "pool_ab",
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": 100,
            "min_amount_out": 90,
        },
    )


def _gold_intents() -> list:
    return [
        _gold_intent(label="a-to-b", asset_in="A", asset_out="B", nonce=1),
        _gold_intent(label="b-to-a", asset_in="B", asset_out="A", nonce=2),
    ]


def _gold_intent_ops() -> list:
    return [
        _gold_swap_dict(label="a-to-b", asset_in="A", asset_out="B", nonce=1),
        _gold_swap_dict(label="b-to-a", asset_in="B", asset_out="A", nonce=2),
    ]


def _gold_certificate(intents: list):
    from src.core.uniform_batch_clearing import (
        UniformBatchCertificateV1,
        UniformBatchFillV1,
        uniform_batch_intent_set_hash,
        uniform_batch_pool_state_hash,
    )

    return UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=uniform_batch_pool_state_hash(_gold_pool()),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=1,
        price_den=1,
        fills=tuple(
            UniformBatchFillV1(intent_id=i.intent_id, executed_in=100, executed_out=100)
            for i in sorted(intents, key=lambda item: item.intent_id)
        ),
    )


def _gold_ops_with_uniform_certificate(*, tamper_settlement: bool = False) -> dict:
    from src.core.uniform_batch_clearing import build_uniform_batch_settlement_v1

    state = _gold_state()
    intents = _gold_intents()
    cert = _gold_certificate(intents)
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    if tamper_settlement:
        settlement.fills[0].amount_out_filled = 99
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = cert.to_dict()
    return {"2": _gold_intent_ops(), "3": settlement_op}


def _state_fingerprint(state: DexState) -> tuple:
    """Cheap deterministic snapshot of mutable DexState used for no-op checks."""
    bal = state.balances
    return (
        bal.get(_GOLD_SENDER, "A"),
        bal.get(_GOLD_SENDER, "B"),
        state.nonces.get_last(_GOLD_SENDER),
        tuple(
            (pid, p.reserve0, p.reserve1, p.lp_supply)
            for pid, p in sorted(state.pools.items())
        ),
    )


# --- GOLDEN: successful multi-op application (state + event ordering) -------


def test_golden_apply_ops_accepts_plain_two_swap_batch_state_and_events() -> None:
    state = _gold_state()
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations={"2": _gold_intent_ops()},
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok, res.error
    assert res.state is not None
    # Pin the EXACT current greedy-AB settlement outcome for this two-swap batch
    # (sender nets +8 A / -10 B; this is the characterized behavior, not identity).
    assert res.state.balances.get(_GOLD_SENDER, "A") == 1_008
    assert res.state.balances.get(_GOLD_SENDER, "B") == 990
    assert res.state.pools["pool_ab"].reserve0 == 992
    assert res.state.pools["pool_ab"].reserve1 == 1_010
    # Both nonces consumed, in order.
    assert res.state.nonces.get_last(_GOLD_SENDER) == 2
    assert res.settlement is not None
    # Plain compute path emits no events; fill ordering is deterministic (by id).
    assert res.settlement.events is None
    fill_ids = [f.intent_id for f in res.settlement.fills]
    assert fill_ids == sorted(fill_ids)


def test_golden_apply_ops_accepts_uniform_batch_certificate_state_and_event_order() -> None:
    from src.core.uniform_batch_clearing import (
        UNIFORM_BATCH_POLICY_ID,
        UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
    )

    state = _gold_state()
    res = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=_gold_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok, res.error
    assert res.state is not None
    assert res.state.balances.get(_GOLD_SENDER, "A") == 1_000
    assert res.state.balances.get(_GOLD_SENDER, "B") == 1_000
    assert res.state.nonces.get_last(_GOLD_SENDER) == 2
    assert res.settlement is not None
    # Exact event payload + ordering pinned (single clearing event).
    assert res.settlement.events == [
        {
            "type": "UNIFORM_BATCH_CLEARING_V1",
            "pool_id": "pool_ab",
            "policy_id": UNIFORM_BATCH_POLICY_ID,
            "price_objective_id": UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
            "certificate_hash": _gold_certificate(_gold_intents()).hash(),
        }
    ]


# --- GOLDEN: one reject per extracted block (exact strings) ------------------


def test_golden_reject_uniform_batch_certificate_not_enabled() -> None:
    # Entry guard of the uniform-batch settlement block (extracted helper).
    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),
        state=_gold_state(),
        operations=_gold_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "uniform batch certificate not enabled"


def test_golden_reject_uniform_batch_settlement_match_mismatch() -> None:
    # require_settlement_match path inside the uniform-batch block.
    res = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_gold_state(),
        operations=_gold_ops_with_uniform_certificate(tamper_settlement=True),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "settlement mismatch"


def test_golden_reject_proof_payload_too_large_before_commitment_block() -> None:
    # Proof size guard fires at parse time (before the commitment block).
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    del ops["3"]["uniform_batch_certificate"]
    intents = parse_intents({"2": _gold_intent_ops()})
    settlement = compute_settlement(
        intents=intents, pools=state.pools, balances=state.balances, lp_balances=state.lp_balances
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["proof"] = {"scheme": "dummy", "blob": "x" * 512}
    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            proof_config=ProofVerifierConfig(max_proof_bytes=128),
        ),
        state=state,
        operations={"2": _gold_intent_ops(), "3": settlement_op},
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error is not None
    assert "proof payload too large" in res.error


# --- GOLDEN: cross-check (evidence-consistency) rejects, incl. missing cov ---


def test_golden_reject_optimality_certificate_requires_uniform_batch_certificate() -> None:
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    # Optimality evidence present but no uniform batch certificate.
    del ops["3"]["uniform_batch_certificate"]
    ops["3"]["uniform_batch_optimality_certificate"] = {"winner_id": "0x00"}
    res = apply_ops(
        config=DexEngineConfig(allow_uniform_batch_certificate=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "uniform batch optimality certificate requires uniform batch certificate"


def test_golden_reject_v2_bounded_grid_requires_uniform_batch_certificate() -> None:
    # Pins line 1314 (v2 bounded-grid evidence without uniform batch certificate).
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    del ops["3"]["uniform_batch_certificate"]
    ops["3"]["uniform_batch_v2_bounded_grid"] = {"max_price_num": 1, "max_price_den": 1, "fill_vectors": []}
    res = apply_ops(
        config=DexEngineConfig(allow_uniform_batch_certificate=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "uniform batch v2 bounded-grid evidence requires uniform batch certificate"


def test_golden_reject_v3_exact_out_grid_requires_uniform_batch_certificate() -> None:
    # Pins line 1319 (v3 exact-out grid evidence without uniform batch certificate).
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    del ops["3"]["uniform_batch_certificate"]
    ops["3"]["uniform_batch_v3_exact_out_grid"] = {"max_price_num": 1, "max_price_den": 1}
    res = apply_ops(
        config=DexEngineConfig(allow_uniform_batch_certificate=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "uniform batch v3 exact-out grid evidence requires uniform batch certificate"


def test_golden_reject_v2_bounded_grid_requires_optimality_certificate() -> None:
    # Pins line 1324 (v2 bounded-grid evidence with cert but no optimality cert).
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    ops["3"]["uniform_batch_v2_bounded_grid"] = {"max_price_num": 1, "max_price_den": 1, "fill_vectors": []}
    res = apply_ops(
        config=DexEngineConfig(allow_uniform_batch_certificate=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "uniform batch v2 bounded-grid evidence requires optimality certificate"


def test_golden_reject_v3_exact_out_grid_requires_optimality_certificate() -> None:
    # Pins line 1329 (v3 exact-out grid evidence with cert but no optimality cert).
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    ops["3"]["uniform_batch_v3_exact_out_grid"] = {"max_price_num": 1, "max_price_den": 1}
    res = apply_ops(
        config=DexEngineConfig(allow_uniform_batch_certificate=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "uniform batch v3 exact-out grid evidence requires optimality certificate"


def test_golden_reject_bounded_grid_evidence_provided_twice() -> None:
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    ops["3"]["uniform_batch_optimality_certificate"] = {"winner_id": "0x00"}
    ops["3"]["uniform_batch_v2_bounded_grid"] = {"max_price_num": 1, "max_price_den": 1, "fill_vectors": []}
    ops["3"]["uniform_batch_v3_exact_out_grid"] = {"max_price_num": 1, "max_price_den": 1}
    res = apply_ops(
        config=DexEngineConfig(allow_uniform_batch_certificate=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "uniform batch bounded-grid evidence provided twice"


# --- GOLDEN: unknown / malformed op ------------------------------------------


def test_golden_unknown_op_keys_are_ignored_not_applied() -> None:
    # Only "2"/"3" are recognized. Unknown numeric keys must not change behavior.
    state = _gold_state()
    ops = {"2": _gold_intent_ops(), "7": [{"junk": True}], "totally_unknown": 1}
    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    # Behaves exactly like the plain two-swap batch (unknown keys are inert).
    assert res.ok, res.error
    assert res.state is not None
    assert res.state.nonces.get_last(_GOLD_SENDER) == 2


def test_golden_malformed_intent_op_rejects_with_invalid_intents() -> None:
    state = _gold_state()
    before = _state_fingerprint(state)
    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),
        state=state,
        operations={"2": "not-a-list"},
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error is not None
    assert res.error.startswith("invalid intents")
    # No-op on reject.
    assert _state_fingerprint(state) == before


# --- GOLDEN: no-op-on-reject -------------------------------------------------


def test_golden_no_op_on_reject_uniform_batch_not_enabled() -> None:
    state = _gold_state()
    before = _state_fingerprint(state)
    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),
        state=state,
        operations=_gold_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    # Rejected batch leaves the input state byte-for-byte unchanged.
    assert _state_fingerprint(state) == before


def test_golden_no_op_on_reject_settlement_mismatch() -> None:
    state = _gold_state()
    before = _state_fingerprint(state)
    res = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=_gold_ops_with_uniform_certificate(tamper_settlement=True),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert _state_fingerprint(state) == before


# --- TEETH: mutation-style tests that fail if a guard/precedence regresses ---


def test_teeth_reject_precedence_optimality_consistency_before_entry_guard() -> None:
    # MUTATION CAUGHT: reordering the evidence-consistency cross-checks AFTER the
    # uniform-batch entry "not enabled" guard. Here UPBA is disabled AND optimality
    # evidence is present without a uniform certificate. The consistency cross-check
    # (earlier in apply_ops) must win over the "not enabled" entry guard.
    state = _gold_state()
    ops = _gold_ops_with_uniform_certificate()
    del ops["3"]["uniform_batch_certificate"]
    ops["3"]["uniform_batch_optimality_certificate"] = {"winner_id": "0x00"}
    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),  # UPBA NOT enabled
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    # Cross-check precedence: this exact string (not "uniform batch certificate not enabled").
    assert res.error == "uniform batch optimality certificate requires uniform batch certificate"


def test_teeth_nonce_replay_reject_precedes_settlement_compute() -> None:
    # MUTATION CAUGHT: dropping/moving the nonce guard so a replayed batch reaches
    # settlement compute/apply. A pre-consumed nonce must reject (no-op) regardless
    # of an otherwise-valid uniform-batch certificate.
    state = _gold_state()
    state.nonces.set_last(_GOLD_SENDER, 5)  # both intent nonces (1,2) are stale
    before = _state_fingerprint(state)
    res = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=_gold_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error is not None
    # Nonce policy reject, and state untouched (no settlement applied).
    assert _state_fingerprint(state) == before


def test_teeth_uniform_batch_dispatch_entry_guard_present() -> None:
    # MUTATION CAUGHT: removing the uniform-batch settlement compute branch entirely
    # (so a cert-bearing op silently falls through to the plain compute path). With
    # UPBA enabled, a cert-bearing batch produces the UNIFORM_BATCH_CLEARING_V1 event;
    # a plain compute_settlement would NOT emit that event type.
    state = _gold_state()
    res = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=_gold_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok, res.error
    assert res.settlement is not None
    assert res.settlement.events is not None
    assert res.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V1"


def test_teeth_settlement_match_guard_present() -> None:
    # MUTATION CAUGHT: dropping the require_settlement_match comparison (so a tampered
    # settlement is accepted). A settlement whose fill output was altered must reject.
    state = _gold_state()
    res = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=_gold_ops_with_uniform_certificate(tamper_settlement=True),
        block_timestamp=0,
        tx_sender_pubkey=_GOLD_SENDER,
    )
    assert res.ok is False
    assert res.error == "settlement mismatch"
