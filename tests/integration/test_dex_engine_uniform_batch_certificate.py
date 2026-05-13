from __future__ import annotations

from hashlib import sha256

from src.core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    build_uniform_batch_settlement_v1,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
)
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation, parse_intents
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus
from src.core.dex import DexState


SENDER = "0x" + "aa" * 48


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


def _state() -> DexState:
    balances = BalanceTable()
    balances.set(SENDER, "A", 1_000)
    balances.set(SENDER, "B", 1_000)
    return DexState(
        balances=balances,
        pools={"pool_ab": _pool()},
        lp_balances=LPTable(),
    )


def _swap_dict(
    *,
    label: str,
    asset_in: str,
    asset_out: str,
    nonce: int,
) -> dict[str, object]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": _intent_id(label),
        "sender_pubkey": SENDER,
        "deadline": 999_999_999,
        "nonce": nonce,
        "pool_id": "pool_ab",
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": 100,
        "min_amount_out": 90,
    }


def _intent(
    *,
    label: str,
    asset_in: str,
    asset_out: str,
    nonce: int,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_intent_id(label),
        sender_pubkey=SENDER,
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


def _intents() -> list[Intent]:
    return [
        _intent(label="a-to-b", asset_in="A", asset_out="B", nonce=1),
        _intent(label="b-to-a", asset_in="B", asset_out="A", nonce=2),
    ]


def _intent_ops() -> list[dict[str, object]]:
    return [
        _swap_dict(label="a-to-b", asset_in="A", asset_out="B", nonce=1),
        _swap_dict(label="b-to-a", asset_in="B", asset_out="A", nonce=2),
    ]


def _certificate(intents: list[Intent]) -> UniformBatchCertificateV1:
    return UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=uniform_batch_pool_state_hash(_pool()),
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


def _ops_with_uniform_certificate(*, tamper_settlement: bool = False) -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
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
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_missing_uniform_fill() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    missing_fill_cert = UniformBatchCertificateV1(
        pool_id=cert.pool_id,
        base_asset=cert.base_asset,
        quote_asset=cert.quote_asset,
        pool_state_hash=cert.pool_state_hash,
        intent_set_hash=cert.intent_set_hash,
        price_num=cert.price_num,
        price_den=cert.price_den,
        fills=cert.fills[:1],
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = missing_fill_cert.to_dict()
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_partial_uniform_fill() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    first = cert.fills[0]
    partial_cert = UniformBatchCertificateV1(
        pool_id=cert.pool_id,
        base_asset=cert.base_asset,
        quote_asset=cert.quote_asset,
        pool_state_hash=cert.pool_state_hash,
        intent_set_hash=cert.intent_set_hash,
        price_num=cert.price_num,
        price_den=cert.price_den,
        fills=(
            UniformBatchFillV1(
                intent_id=first.intent_id,
                executed_in=99,
                executed_out=99,
            ),
            cert.fills[1],
        ),
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = partial_cert.to_dict()
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_pool_snapshot_mismatch() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    mismatched_cert = UniformBatchCertificateV1(
        pool_id=cert.pool_id,
        base_asset=cert.base_asset,
        quote_asset=cert.quote_asset,
        pool_state_hash="0x" + "ff" * 32,
        intent_set_hash=cert.intent_set_hash,
        price_num=cert.price_num,
        price_den=cert.price_den,
        fills=cert.fills,
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = mismatched_cert.to_dict()
    return {"2": _intent_ops(), "3": settlement_op}


def test_engine_accepts_uniform_batch_certificate_when_enabled() -> None:
    state = _state()
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.state is not None
    assert result.state.balances.get(SENDER, "A") == 1_000
    assert result.state.balances.get(SENDER, "B") == 1_000
    assert result.state.nonces.get_last(SENDER) == 2
    assert result.settlement is not None
    assert result.settlement.events == [
        {
            "type": "UNIFORM_BATCH_CLEARING_V1",
            "pool_id": "pool_ab",
            "certificate_hash": _certificate(_intents()).hash(),
        }
    ]


def test_engine_rejects_uniform_batch_certificate_unless_enabled() -> None:
    result = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False),
        state=_state(),
        operations=_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate not enabled"


def test_engine_rejects_tampered_uniform_batch_settlement() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate(tamper_settlement=True),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "settlement mismatch"


def test_engine_rejects_tampered_uniform_batch_settlement_without_match_gate() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
            require_settlement_match=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate(tamper_settlement=True),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch settlement mismatch"


def test_engine_rejects_uniform_batch_certificate_missing_admitted_fill() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_missing_uniform_fill(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate rejected: certificate must fill every admitted intent"


def test_engine_rejects_uniform_batch_certificate_pool_snapshot_mismatch() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_pool_snapshot_mismatch(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate rejected: certificate pool_state_hash mismatch"


def test_engine_rejects_uniform_batch_certificate_partial_fill() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_partial_uniform_fill(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate rejected: certificate fill must consume full intent amount_in"


def test_validation_accepts_uniform_batch_certificate_without_sequential_replay() -> None:
    state = _state()
    ops = _ops_with_uniform_certificate()
    intents = parse_intents(ops)
    settlement_op = ops["3"]
    assert isinstance(settlement_op, dict)
    cert_obj = settlement_op["uniform_batch_certificate"]
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert_obj,
    )

    from src.integration.validation import validate_operations

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        block_timestamp=0,
        uniform_batch_certificate=cert_obj,
    )

    assert ok, err
