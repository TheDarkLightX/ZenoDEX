from __future__ import annotations

from hashlib import sha256

from src.core.batch_clearing import validate_settlement
from src.core.settlement import FillAction
from src.core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    build_uniform_batch_settlement_v1,
    uniform_batch_intent_set_hash,
    validate_uniform_batch_settlement_v1,
    verify_uniform_batch_certificate_v1,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
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


def _fee_pool() -> PoolState:
    pool = _pool()
    pool.fee_bps = 100
    return pool


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
    return UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
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


def test_uniform_batch_certificate_builds_conservative_settlement() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.settlement is not None
    assert result.certificate_hash == certificate.hash()
    assert [fill.action for fill in result.settlement.fills] == [FillAction.FILL, FillAction.FILL]
    assert result.settlement.reserve_deltas == []
    valid, err = validate_settlement(result.settlement, balances, {"pool_ab": pool}, LPTable())
    assert valid, err


def test_uniform_batch_certificate_is_permutation_invariant() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)

    settlement_a = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )
    settlement_b = build_uniform_batch_settlement_v1(
        intents=list(reversed(intents)),
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert settlement_a.included_intents == settlement_b.included_intents
    assert settlement_a.fills == settlement_b.fills
    assert settlement_a.balance_deltas == settlement_b.balance_deltas
    assert settlement_a.reserve_deltas == settlement_b.reserve_deltas


def test_uniform_batch_intent_set_hash_is_permutation_invariant() -> None:
    intents = _balanced_intents()

    assert uniform_batch_intent_set_hash(intents) == uniform_batch_intent_set_hash(list(reversed(intents)))


def test_uniform_batch_certificate_handles_fee_adjusted_uniform_outputs() -> None:
    pool = _fee_pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=1,
        price_den=1,
        fills=tuple(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=100,
                executed_out=99,
            )
            for intent in sorted(intents, key=lambda item: item.intent_id)
        ),
    )

    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert [fill.fee_paid for fill in settlement.fills] == [1, 1]
    assert sorted(
        (delta.asset, delta.delta_add, delta.delta_sub) for delta in settlement.reserve_deltas
    ) == [("A", 1, 0), ("B", 1, 0)]


def test_uniform_batch_certificate_rejects_aggregate_k_decrease() -> None:
    pool = _pool()
    balances = _balances()
    intents = [_swap("alice-a-to-b", "alice", "A", "B")]
    certificate = _certificate_for(intents)

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "uniform batch violates aggregate CPMM invariant"


def test_uniform_batch_certificate_rejects_limit_violation() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _swap("alice-a-to-b", "alice", "A", "B", min_amount_out=101),
        _swap("bob-b-to-a", "bob", "B", "A"),
    ]
    certificate = _certificate_for(intents)

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate fill violates intent limit price"


def test_uniform_batch_certificate_rejects_noncanonical_fill_order() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        intent_set_hash=certificate.intent_set_hash,
        price_num=certificate.price_num,
        price_den=certificate.price_den,
        fills=tuple(reversed(certificate.fills)),
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate fills must be sorted by intent_id"


def test_uniform_batch_certificate_rejects_missing_admitted_intent_fill() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        intent_set_hash=certificate.intent_set_hash,
        price_num=certificate.price_num,
        price_den=certificate.price_den,
        fills=certificate.fills[:1],
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate must fill every admitted intent"


def test_uniform_batch_certificate_rejects_invalid_direct_dataclass_shape() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        intent_set_hash=certificate.intent_set_hash,
        price_num=0,
        price_den=certificate.price_den,
        fills=certificate.fills,
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate.price_num must be positive"


def test_uniform_batch_certificate_rejects_intent_set_hash_mismatch() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    tampered = _swap("alice-a-to-b", "alice", "A", "B", min_amount_out=1)
    tampered.intent_id = intents[0].intent_id
    changed_intents = [tampered, intents[1]]

    result = verify_uniform_batch_certificate_v1(
        intents=changed_intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate intent_set_hash mismatch"


def test_uniform_batch_settlement_validator_rejects_tampering() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )
    settlement.fills[0].amount_out_filled = 99

    ok, err = validate_uniform_batch_settlement_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
        settlement=settlement,
    )

    assert ok is False
    assert err == "uniform batch settlement mismatch"
