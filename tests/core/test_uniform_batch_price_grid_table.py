from __future__ import annotations

from dataclasses import replace
from hashlib import sha256

from src.core.uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_POLICY_V2_ID,
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    uniform_batch_certificate_hash,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
)
from src.core.uniform_batch_price_grid_table import (
    UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
    UniformBatchPriceGridConfigV1,
    UniformBatchPriceGridRowV1,
    UniformBatchPriceGridWitnessV1,
    build_uniform_batch_price_grid_table_v1,
    uniform_batch_price_grid_candidate_id,
    uniform_batch_price_grid_table_root,
    verify_uniform_batch_price_grid_table_v1,
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


def _swap(
    label: str,
    sender: str,
    asset_in: str,
    asset_out: str,
    amount_in: int = 100,
    min_amount_out: int = 90,
) -> Intent:
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
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def _balances() -> BalanceTable:
    balances = BalanceTable()
    balances.set("alice", "A", 1_000)
    balances.set("alice", "B", 0)
    balances.set("bob", "A", 0)
    balances.set("bob", "B", 1_000)
    return balances


def _balanced_intents() -> list[Intent]:
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


def _artifacts() -> tuple[
    list[Intent],
    PoolState,
    BalanceTable,
    UniformBatchCertificateV1,
    UniformBatchPriceGridConfigV1,
    tuple[UniformBatchPriceGridRowV1, ...],
    UniformBatchPriceGridWitnessV1,
]:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    config, rows, witness = build_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        settlement_id="settlement-1",
        max_price_num=2,
        max_price_den=2,
    )
    return intents, pool, balances, certificate, config, rows, witness


def _with_root(
    config: UniformBatchPriceGridConfigV1,
    rows: tuple[UniformBatchPriceGridRowV1, ...],
    witness: UniformBatchPriceGridWitnessV1,
) -> tuple[UniformBatchPriceGridConfigV1, UniformBatchPriceGridWitnessV1]:
    root = uniform_batch_price_grid_table_root(
        settlement_id=config.settlement_id,
        max_price_num=config.max_price_num,
        max_price_den=config.max_price_den,
        score_function_id=config.score_function_id,
        rows=rows,
    )
    return (
        replace(config, candidate_table_root=root),
        replace(witness, candidate_table_root=root),
    )


def _candidate_id_for_row(config: UniformBatchPriceGridConfigV1, row: UniformBatchPriceGridRowV1) -> str:
    return uniform_batch_price_grid_candidate_id(
        settlement_id=config.settlement_id,
        score_function_id=config.score_function_id,
        price_num=row.price_num,
        price_den=row.price_den,
        valid_price_ok=row.valid_price_ok,
        volume=row.volume,
        surplus=row.surplus,
    )


def test_price_grid_table_accepts_complete_recomputed_grid() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=rows,
        witness=witness,
    )

    assert result.ok is True
    assert result.error is None
    assert result.candidate_table_root == config.candidate_table_root
    assert result.winner_candidate_id == witness.winner_candidate_id
    assert result.tau_facts is not None
    assert all(result.tau_facts.values())


def test_price_grid_table_rejects_missing_grid_key() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    rows_without_key = rows[:-1]

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=rows_without_key,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "price grid row count mismatch"


def test_price_grid_table_rejects_duplicate_grid_key() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    duplicate_rows = rows[:-1] + (rows[0],)
    config, witness = _with_root(config, duplicate_rows, witness)

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=duplicate_rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "duplicate price grid row key"


def test_price_grid_table_rejects_out_of_bounds_grid_key() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    row = rows[0]
    out_of_bounds = replace(
        row,
        price_num=config.max_price_num + 1,
        candidate_id=_candidate_id_for_row(config, row),
    )
    mutated_rows = (out_of_bounds,) + rows[1:]
    config, witness = _with_root(config, mutated_rows, witness)

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=mutated_rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "price grid row key outside configured bounds"


def test_price_grid_table_rejects_score_mismatch() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    row = rows[0]
    mutated_row = replace(row, volume=row.volume + 1)
    mutated_rows = (mutated_row,) + rows[1:]
    config, witness = _with_root(config, mutated_rows, witness)

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=mutated_rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "price grid row volume mismatch"


def test_price_grid_table_rejects_table_root_mismatch() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    bad_root = "0x" + "0" * 64
    config = replace(config, candidate_table_root=bad_root)
    witness = replace(witness, candidate_table_root=bad_root)

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "price grid candidate_table_root mismatch"


def test_price_grid_table_rejects_missing_winner_row() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    mutated_rows = tuple(replace(row, winner_row_ok=False) for row in rows)
    config, witness = _with_root(config, mutated_rows, witness)

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=mutated_rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "price grid requires exactly one winner row"


def test_price_grid_table_rejects_dominance_flag_mismatch() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    target = next(row for row in rows if not row.winner_row_ok)
    mutated_target = replace(target, dominated_by_winner_ok=not target.dominated_by_winner_ok)
    mutated_rows = tuple(mutated_target if row == target else row for row in rows)
    config, witness = _with_root(config, mutated_rows, witness)

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=mutated_rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "price grid row dominated_by_winner_ok mismatch"


def test_price_grid_table_rejects_invalid_boolean_shape() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    row = rows[0].to_dict()
    row["score_recomputed_ok"] = 1
    row_dicts = [row] + [entry.to_dict() for entry in rows[1:]]

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=row_dicts,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "row.score_recomputed_ok must be a bool"


def test_price_grid_table_rejects_malformed_dataclass_boolean_shape() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    malformed_row = replace(rows[0], score_recomputed_ok=1)  # type: ignore[arg-type]
    malformed_rows = (malformed_row,) + rows[1:]

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=certificate,
        config=config,
        rows=malformed_rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == "row.score_recomputed_ok must be a bool"


def test_price_grid_table_rejects_invalid_uniform_batch_certificate_fills() -> None:
    intents, pool, balances, certificate, config, rows, witness = _artifacts()
    invalid_certificate = replace(
        certificate,
        fills=tuple(
            replace(fill, executed_out=fill.executed_out + 1)
            if index == 0
            else fill
            for index, fill in enumerate(certificate.fills)
        ),
    )
    witness = replace(
        witness,
        uniform_batch_certificate_hash=uniform_batch_certificate_hash(invalid_certificate),
    )

    result = verify_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        uniform_batch_certificate=invalid_certificate,
        config=config,
        rows=rows,
        witness=witness,
    )

    assert result.ok is False
    assert result.error == (
        "price grid uniform batch certificate invalid: "
        "certificate fill output does not match uniform price"
    )


def test_price_grid_builder_rejects_v2_partial_fill_certificate() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = replace(
        _certificate_for(intents),
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
        policy_id=UNIFORM_BATCH_POLICY_V2_ID,
    )

    try:
        build_uniform_batch_price_grid_table_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            uniform_batch_certificate=certificate,
            settlement_id="settlement-v2",
            max_price_num=2,
            max_price_den=2,
        )
    except ValueError as exc:
        assert str(exc) == "price grid verifier supports UPBA v1 certificate schema only"
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected v2 certificate rejection")


def test_price_grid_candidate_id_changes_with_score() -> None:
    candidate_a = uniform_batch_price_grid_candidate_id(
        settlement_id="settlement",
        score_function_id=UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
        price_num=1,
        price_den=1,
        valid_price_ok=True,
        volume=100,
        surplus=1,
    )
    candidate_b = uniform_batch_price_grid_candidate_id(
        settlement_id="settlement",
        score_function_id=UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
        price_num=1,
        price_den=1,
        valid_price_ok=True,
        volume=100,
        surplus=2,
    )

    assert candidate_a != candidate_b
