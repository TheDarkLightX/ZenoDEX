from __future__ import annotations

from dataclasses import replace
from hashlib import sha256

from src.core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
)
from src.core.uniform_batch_price_grid_table import build_uniform_batch_price_grid_table_v1
from src.core.zenohypergraph_upba import (
    uniform_batch_hypergraph_root_v1,
    verify_uniform_batch_hypergraph_root_v1,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus


def _intent_id(label: str) -> str:
    return "0x" + sha256(label.encode("utf-8")).hexdigest()


def _pool() -> PoolState:
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


def _balances() -> BalanceTable:
    balances = BalanceTable()
    balances.set("alice", "A", 1_000)
    balances.set("alice", "B", 0)
    balances.set("bob", "A", 0)
    balances.set("bob", "B", 1_000)
    return balances


def _swap(label: str, sender: str, asset_in: str, asset_out: str) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_intent_id(label),
        sender_pubkey=sender,
        deadline=999,
        fields={
            "pool_id": "pool_ab",
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": 100,
            "min_amount_out": 90,
        },
    )


def _intents() -> list[Intent]:
    return [
        _swap("alice-a-to-b", "alice", "A", "B"),
        _swap("bob-b-to-a", "bob", "B", "A"),
    ]


def _certificate_for(intents: list[Intent]) -> UniformBatchCertificateV1:
    pool = _pool()
    return UniformBatchCertificateV1(
        pool_id=pool.pool_id,
        base_asset=pool.asset0,
        quote_asset=pool.asset1,
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=1,
        price_den=1,
        fills=tuple(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=100,
                executed_out=100,
            )
            for intent in sorted(intents, key=lambda item: item.intent_id)
        ),
    )


def _artifacts():
    pool = _pool()
    balances = _balances()
    intents = _intents()
    certificate = _certificate_for(intents)
    config, rows, witness = build_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        settlement_id="settlement-zenohypergraph",
        max_price_num=2,
        max_price_den=2,
    )
    return intents, pool, balances, certificate, config, rows, witness


def test_zenohypergraph_root_is_order_permutation_invariant() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()

    root_a = uniform_batch_hypergraph_root_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        price_grid_config=config,
        price_grid_rows=rows,
        price_grid_witness=witness,
    )
    root_b = uniform_batch_hypergraph_root_v1(
        intents=list(reversed(intents)),
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        price_grid_config=config,
        price_grid_rows=rows,
        price_grid_witness=witness,
    )

    assert root_a == root_b


def test_zenohypergraph_root_is_price_row_permutation_invariant() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()

    root_a = uniform_batch_hypergraph_root_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        price_grid_config=config,
        price_grid_rows=rows,
        price_grid_witness=witness,
    )
    root_b = uniform_batch_hypergraph_root_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        price_grid_config=config,
        price_grid_rows=tuple(reversed(rows)),
        price_grid_witness=witness,
    )

    assert root_a == root_b


def test_zenohypergraph_root_rejects_mismatch() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    root = uniform_batch_hypergraph_root_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        price_grid_config=config,
        price_grid_rows=rows,
        price_grid_witness=witness,
    )

    result = verify_uniform_batch_hypergraph_root_v1(
        expected_root="0x" + "00" * 32,
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        price_grid_config=config,
        price_grid_rows=rows,
        price_grid_witness=witness,
    )

    assert result.ok is False
    assert result.error == "zenohypergraph root mismatch"
    assert result.hypergraph_root == root


def test_zenohypergraph_root_rejects_tampered_price_grid() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    tampered = replace(rows[0], volume=rows[0].volume + 1)

    result = verify_uniform_batch_hypergraph_root_v1(
        expected_root="0x" + "00" * 32,
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        price_grid_config=config,
        price_grid_rows=(tampered,) + rows[1:],
        price_grid_witness=witness,
    )

    assert result.ok is False
    assert result.error is not None
    assert "candidate_table_root mismatch" in result.error
