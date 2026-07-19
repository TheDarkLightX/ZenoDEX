from __future__ import annotations

from dataclasses import replace
from hashlib import sha256
from math import gcd
from random import Random

from src.core.batch_clearing import validate_settlement
from src.core.cpmm import compute_fee_total
from src.core.settlement import FillAction
from src.core.uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
    UNIFORM_BATCH_MAX_FILLS,
    UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
    UNIFORM_BATCH_POLICY_ID,
    UNIFORM_BATCH_POLICY_V2_ID,
    UNIFORM_BATCH_POLICY_V3_ID,
    UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
    UNIFORM_BATCH_PRICE_RATIO_MAX,
    UNIFORM_BATCH_UNFILLED_REASON,
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    build_uniform_batch_settlement_v1,
    uniform_batch_certificate_hash,
    uniform_batch_exact_out_gross_in_for_price,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
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


def _high_fee_pool() -> PoolState:
    pool = _pool()
    pool.fee_bps = 1_000
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


def _exact_out_swap(
    label: str,
    sender: str,
    asset_in: str,
    asset_out: str,
    amount_out: int = 100,
    max_amount_in: int = 100,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_intent_id(label),
        sender_pubkey=sender,
        deadline=999,
        fields={
            "pool_id": "pool_ab",
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_out": amount_out,
            "max_amount_in": max_amount_in,
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


def _reduce_ratio(numerator: int, denominator: int) -> tuple[int, int]:
    divisor = gcd(numerator, denominator)
    return numerator // divisor, denominator // divisor


def _v2_certificate_for(
    *,
    intents: list[Intent],
    pool: PoolState,
    executed_in_by_id: dict[str, int],
) -> UniformBatchCertificateV1:
    base_to_quote_net = 0
    quote_to_base_net = 0
    for intent in intents:
        executed_in = int(executed_in_by_id[intent.intent_id])
        if executed_in == 0:
            continue
        net_in = executed_in - compute_fee_total(executed_in, pool.fee_bps)
        if str(intent.get_field("asset_in")) == pool.asset0:
            base_to_quote_net += net_in
        else:
            quote_to_base_net += net_in
    if base_to_quote_net > 0 and quote_to_base_net > 0:
        price_num, price_den = _reduce_ratio(quote_to_base_net, base_to_quote_net)
    else:
        price_num, price_den = _reduce_ratio(pool.reserve1, pool.reserve0)

    fills: list[UniformBatchFillV1] = []
    for intent in sorted(intents, key=lambda item: item.intent_id):
        executed_in = int(executed_in_by_id[intent.intent_id])
        if executed_in == 0:
            executed_out = 0
        else:
            net_in = executed_in - compute_fee_total(executed_in, pool.fee_bps)
            if str(intent.get_field("asset_in")) == pool.asset0:
                executed_out = (net_in * price_num) // price_den
            else:
                executed_out = (net_in * price_den) // price_num
        fills.append(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=executed_in,
                executed_out=executed_out,
            )
        )
    return UniformBatchCertificateV1(
        pool_id=pool.pool_id,
        base_asset=pool.asset0,
        quote_asset=pool.asset1,
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=price_num,
        price_den=price_den,
        fills=tuple(fills),
        policy_id=UNIFORM_BATCH_POLICY_V2_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    )


def _v3_exact_out_certificate_for(
    *,
    intents: list[Intent],
    pool: PoolState,
    executed_in_by_id: dict[str, int],
) -> UniformBatchCertificateV1:
    base_to_quote_net = 0
    quote_to_base_net = 0
    for intent in intents:
        executed_in = int(executed_in_by_id[intent.intent_id])
        net_in = executed_in - compute_fee_total(executed_in, pool.fee_bps)
        if str(intent.get_field("asset_in")) == pool.asset0:
            base_to_quote_net += net_in
        else:
            quote_to_base_net += net_in
    if base_to_quote_net > 0 and quote_to_base_net > 0:
        price_num, price_den = _reduce_ratio(quote_to_base_net, base_to_quote_net)
    else:
        price_num, price_den = _reduce_ratio(pool.reserve1, pool.reserve0)

    fills = tuple(
        UniformBatchFillV1(
            intent_id=intent.intent_id,
            executed_in=int(executed_in_by_id[intent.intent_id]),
            executed_out=int(intent.get_field("amount_out")),
        )
        for intent in sorted(intents, key=lambda item: item.intent_id)
    )
    return UniformBatchCertificateV1(
        pool_id=pool.pool_id,
        base_asset=pool.asset0,
        quote_asset=pool.asset1,
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=price_num,
        price_den=price_den,
        fills=fills,
        policy_id=UNIFORM_BATCH_POLICY_V3_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
    )


def _certificate_for(intents: list[Intent]) -> UniformBatchCertificateV1:
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
    assert certificate.to_dict()["policy_id"] == UNIFORM_BATCH_POLICY_ID
    assert certificate.to_dict()["price_objective_id"] == UNIFORM_BATCH_PRICE_OBJECTIVE_ID
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


def test_uniform_batch_intent_set_hash_rejects_too_many_intents() -> None:
    intents = [
        _swap(f"many-{i}", "alice", "A", "B", min_amount_out=1)
        for i in range(UNIFORM_BATCH_MAX_FILLS + 1)
    ]

    try:
        uniform_batch_intent_set_hash(intents)
    except ValueError as exc:
        assert str(exc) == f"uniform batch intent count exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}"
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected oversized intent-set hash rejection")


def test_uniform_batch_pool_state_hash_changes_with_reserves() -> None:
    pool_a = _pool()
    pool_b = _pool()
    pool_b.reserve0 += 1

    assert uniform_batch_pool_state_hash(pool_a) != uniform_batch_pool_state_hash(pool_b)


def test_uniform_batch_certificate_hash_rejects_unknown_mapping_key() -> None:
    certificate_obj = _certificate_for(_balanced_intents()).to_dict()
    certificate_obj["future_policy_knob"] = True

    try:
        uniform_batch_certificate_hash(certificate_obj)
    except ValueError as exc:
        assert str(exc) == "certificate contains unsupported keys: future_policy_knob"
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected unsupported certificate key rejection")


def test_uniform_batch_certificate_hash_rejects_unknown_fill_mapping_key() -> None:
    certificate_obj = _certificate_for(_balanced_intents()).to_dict()
    certificate_obj["fills"][0]["future_fill_knob"] = True

    try:
        uniform_batch_certificate_hash(certificate_obj)
    except ValueError as exc:
        assert str(exc) == "certificate.fill contains unsupported keys: future_fill_knob"
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected unsupported fill key rejection")


def test_uniform_batch_certificate_hash_accepts_canonical_mapping() -> None:
    certificate = _certificate_for(_balanced_intents())

    assert uniform_batch_certificate_hash(certificate.to_dict()) == certificate.hash()


def test_uniform_batch_certificate_hash_rejects_invalid_direct_dataclass() -> None:
    certificate = _certificate_for(_balanced_intents())
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
        intent_set_hash=certificate.intent_set_hash,
        price_num=2,
        price_den=2,
        fills=certificate.fills,
    )

    try:
        certificate.hash()
    except ValueError as exc:
        assert str(exc) == "certificate price ratio must be reduced"
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected direct dataclass hash rejection")


def test_uniform_batch_certificate_hash_rejects_invalid_mapping_shape() -> None:
    certificate_obj = _certificate_for(_balanced_intents()).to_dict()
    certificate_obj["price_num"] = 2
    certificate_obj["price_den"] = 2

    try:
        uniform_batch_certificate_hash(certificate_obj)
    except ValueError as exc:
        assert str(exc) == "certificate price ratio must be reduced"
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected parsed mapping hash rejection")


def test_uniform_batch_v2_certificate_accepts_partial_fills() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _swap("alice-a-to-b", "alice", "A", "B", amount_in=100, min_amount_out=1),
        _swap("bob-b-to-a", "bob", "B", "A", amount_in=200, min_amount_out=1),
    ]
    certificate = _v2_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 100,
            intents[1].intent_id: 100,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.settlement is not None
    assert certificate.to_dict()["schema"] == UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2
    assert certificate.to_dict()["policy_id"] == UNIFORM_BATCH_POLICY_V2_ID
    assert result.settlement.events == [
        {
            "type": "UNIFORM_BATCH_CLEARING_V2",
            "pool_id": "pool_ab",
            "policy_id": UNIFORM_BATCH_POLICY_V2_ID,
            "price_objective_id": UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
            "certificate_hash": certificate.hash(),
        }
    ]
    assert [fill.action for fill in result.settlement.fills] == [FillAction.FILL, FillAction.FILL]
    assert [fill.amount_in_filled for fill in result.settlement.fills] == [100, 100]
    assert sorted(
        (delta.pubkey, delta.asset, delta.delta_add, delta.delta_sub)
        for delta in result.settlement.balance_deltas
    ) == [
        ("alice", "A", 0, 100),
        ("alice", "B", 100, 0),
        ("bob", "A", 100, 0),
        ("bob", "B", 0, 100),
    ]


def test_uniform_batch_v2_certificate_accepts_zero_fill_rejected_member() -> None:
    pool = _high_fee_pool()
    balances = _balances()
    intents = [
        _swap("alice-a-to-b", "alice", "A", "B", amount_in=100, min_amount_out=1),
        _swap("bob-b-to-a", "bob", "B", "A", amount_in=200, min_amount_out=1),
    ]
    certificate = _v2_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 100,
            intents[1].intent_id: 0,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.settlement is not None
    actions_by_id = dict(result.settlement.included_intents)
    assert actions_by_id[intents[0].intent_id] == FillAction.FILL
    assert actions_by_id[intents[1].intent_id] == FillAction.REJECT
    rejected = [fill for fill in result.settlement.fills if fill.action == FillAction.REJECT]
    assert len(rejected) == 1
    assert rejected[0].intent_id == intents[1].intent_id
    assert rejected[0].reason == UNIFORM_BATCH_UNFILLED_REASON


def test_uniform_batch_v2_certificate_rejects_fill_above_intent_amount() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _v2_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 101,
            intents[1].intent_id: 100,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate fill exceeds intent amount_in"


def test_uniform_batch_v2_certificate_rejects_all_zero_fills() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _v2_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 0,
            intents[1].intent_id: 0,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "uniform batch v2 requires at least one positive fill"


def test_uniform_batch_v2_certificate_rejects_schema_policy_mismatch() -> None:
    pool = _pool()
    intents = _balanced_intents()
    certificate_obj = _v2_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={intent.intent_id: 100 for intent in intents},
    ).to_dict()
    certificate_obj["schema"] = "zenodex/uniform_batch_clearing_certificate/v1"

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=_balances(),
        certificate=certificate_obj,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate schema does not match policy_id"


def test_uniform_batch_v2_adapter_property_permutation_invariance_over_partial_fills() -> None:
    rng = Random(20260513)
    for case_index in range(50):
        pool = _pool()
        pool.reserve0 = rng.randint(1_000, 10_000)
        pool.reserve1 = rng.randint(1_000, 10_000)
        pool.fee_bps = rng.randint(0, 300)
        balances = BalanceTable()
        balances.set("alice", "A", 1_000_000)
        balances.set("alice", "B", 0)
        balances.set("bob", "A", 0)
        balances.set("bob", "B", 1_000_000)
        amount_a = rng.randint(10, 500)
        amount_b = rng.randint(10, 500)
        intents = [
            _swap(
                f"case-{case_index}-alice",
                "alice",
                "A",
                "B",
                amount_in=amount_a,
                min_amount_out=0,
            ),
            _swap(
                f"case-{case_index}-bob",
                "bob",
                "B",
                "A",
                amount_in=amount_b,
                min_amount_out=0,
            ),
        ]
        executed_a = rng.randint(1, amount_a)
        executed_b = rng.randint(1, amount_b)
        certificate = _v2_certificate_for(
            intents=intents,
            pool=pool,
            executed_in_by_id={
                intents[0].intent_id: executed_a,
                intents[1].intent_id: executed_b,
            },
        )

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


def test_uniform_batch_v3_certificate_accepts_full_exact_out_fills() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _exact_out_swap("alice-a-to-b", "alice", "A", "B", amount_out=100, max_amount_in=100),
        _exact_out_swap("bob-b-to-a", "bob", "B", "A", amount_out=100, max_amount_in=100),
    ]
    certificate = _v3_exact_out_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 100,
            intents[1].intent_id: 100,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.settlement is not None
    assert certificate.to_dict()["schema"] == UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3
    assert certificate.to_dict()["policy_id"] == UNIFORM_BATCH_POLICY_V3_ID
    assert result.settlement.events == [
        {
            "type": "UNIFORM_BATCH_CLEARING_V3",
            "pool_id": "pool_ab",
            "policy_id": UNIFORM_BATCH_POLICY_V3_ID,
            "price_objective_id": UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
            "certificate_hash": certificate.hash(),
        }
    ]
    assert [fill.action for fill in result.settlement.fills] == [FillAction.FILL, FillAction.FILL]
    assert [fill.amount_in_filled for fill in result.settlement.fills] == [100, 100]
    assert [fill.amount_out_filled for fill in result.settlement.fills] == [100, 100]
    assert result.settlement.reserve_deltas == []


def test_uniform_batch_v3_exact_out_accepts_rounding_overdelivery_gap_in_pool() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _exact_out_swap("alice-a-to-b", "alice", "A", "B", amount_out=2, max_amount_in=2),
        _exact_out_swap("bob-b-to-a", "bob", "B", "A", amount_out=2, max_amount_in=3),
    ]
    certificate = _v3_exact_out_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 2,
            intents[1].intent_id: 3,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.settlement is not None
    assert (certificate.price_num, certificate.price_den) == (3, 2)
    fills_by_id = {fill.intent_id: fill for fill in result.settlement.fills}
    assert fills_by_id[intents[0].intent_id].amount_in_filled == 2
    assert fills_by_id[intents[0].intent_id].amount_out_filled == 2
    assert fills_by_id[intents[1].intent_id].amount_in_filled == 3
    assert fills_by_id[intents[1].intent_id].amount_out_filled == 2
    assert [(delta.asset, delta.delta_add, delta.delta_sub) for delta in result.settlement.reserve_deltas] == [
        ("B", 1, 0)
    ]


def test_uniform_batch_v3_certificate_rejects_mixed_exact_in_exact_out_intents() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _swap("alice-a-to-b", "alice", "A", "B", amount_in=100, min_amount_out=90),
        _exact_out_swap("bob-b-to-a", "bob", "B", "A", amount_out=100, max_amount_in=100),
    ]
    certificate = UniformBatchCertificateV1(
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
        policy_id=UNIFORM_BATCH_POLICY_V3_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "uniform batch v3 supports SWAP_EXACT_OUT only"


def test_uniform_batch_v3_certificate_rejects_exact_out_max_input_violation() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _exact_out_swap("alice-a-to-b", "alice", "A", "B", amount_out=100, max_amount_in=99),
        _exact_out_swap("bob-b-to-a", "bob", "B", "A", amount_out=100, max_amount_in=100),
    ]
    certificate = _v3_exact_out_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 100,
            intents[1].intent_id: 100,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate fill exceeds intent max_amount_in"


def test_uniform_batch_v3_certificate_rejects_nonminimal_exact_out_input() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _exact_out_swap("alice-a-to-b", "alice", "A", "B", amount_out=100, max_amount_in=200),
        _exact_out_swap("bob-b-to-a", "bob", "B", "A", amount_out=100, max_amount_in=200),
    ]
    certificate = _v3_exact_out_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 101,
            intents[1].intent_id: 101,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate exact-out input is not minimal at uniform price"


def test_uniform_batch_v3_certificate_rejects_underfunded_exact_out_input() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _exact_out_swap("alice-a-to-b", "alice", "A", "B", amount_out=100, max_amount_in=200),
        _exact_out_swap("bob-b-to-a", "bob", "B", "A", amount_out=100, max_amount_in=200),
    ]
    certificate = _v3_exact_out_certificate_for(
        intents=intents,
        pool=pool,
        executed_in_by_id={
            intents[0].intent_id: 99,
            intents[1].intent_id: 99,
        },
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate exact-out input does not satisfy uniform price"


def test_uniform_batch_exact_out_gross_in_helper_rejects_invalid_boundary_values() -> None:
    assert (
        uniform_batch_exact_out_gross_in_for_price(
            amount_out=1,
            direction="base_to_quote",
            price_num=1,
            price_den=1,
            fee_bps=9_999,
        )
        == 10_000
    )

    invalid_cases = [
        {"amount_out": 0, "direction": "base_to_quote", "price_num": 1, "price_den": 1, "fee_bps": 0},
        {"amount_out": 1, "direction": "base_to_quote", "price_num": 0, "price_den": 1, "fee_bps": 0},
        {"amount_out": 1, "direction": "base_to_quote", "price_num": 1, "price_den": 0, "fee_bps": 0},
        {"amount_out": 1, "direction": "base_to_quote", "price_num": 1, "price_den": 1, "fee_bps": 10_000},
    ]
    for case in invalid_cases:
        try:
            uniform_batch_exact_out_gross_in_for_price(**case)
        except (TypeError, ValueError):
            pass
        else:  # pragma: no cover - explicit failure branch for assertion clarity
            raise AssertionError(f"expected invalid exact-out boundary case to fail: {case}")


def test_uniform_batch_certificate_handles_fee_adjusted_uniform_outputs() -> None:
    pool = _fee_pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=uniform_batch_pool_state_hash(pool),
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


def test_uniform_batch_certificate_accepts_canonical_net_flow_ratio() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _swap("alice-a-to-b", "alice", "A", "B", amount_in=100, min_amount_out=90),
        _swap("bob-b-to-a", "bob", "B", "A", amount_in=200, min_amount_out=90),
    ]
    certificate = UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=2,
        price_den=1,
        fills=tuple(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=int(intent.get_field("amount_in")),
                executed_out=200 if str(intent.get_field("asset_in")) == "A" else 100,
            )
            for intent in sorted(intents, key=lambda item: item.intent_id)
        ),
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.settlement is not None
    assert result.settlement.reserve_deltas == []


def test_uniform_batch_certificate_rejects_noncanonical_safe_one_sided_price() -> None:
    pool = _pool()
    balances = _balances()
    intents = [_swap("alice-a-to-b", "alice", "A", "B", amount_in=100, min_amount_out=1)]
    certificate = UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=1,
        price_den=2,
        fills=(
            UniformBatchFillV1(
                intent_id=intents[0].intent_id,
                executed_in=100,
                executed_out=50,
            ),
        ),
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate price does not match canonical UPBA objective"


def test_uniform_batch_certificate_rejects_noncanonical_safe_net_flow_price() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _swap("alice-a-to-b", "alice", "A", "B", amount_in=100, min_amount_out=1),
        _swap("bob-b-to-a", "bob", "B", "A", amount_in=200, min_amount_out=1),
    ]
    certificate = UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=3,
        price_den=2,
        fills=tuple(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=int(intent.get_field("amount_in")),
                executed_out=150 if str(intent.get_field("asset_in")) == "A" else 133,
            )
            for intent in sorted(intents, key=lambda item: item.intent_id)
        ),
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate price does not match canonical UPBA objective"


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
        pool_state_hash=certificate.pool_state_hash,
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


def test_uniform_batch_certificate_rejects_pool_snapshot_mismatch() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash="0x" + "ff" * 32,
        intent_set_hash=certificate.intent_set_hash,
        price_num=certificate.price_num,
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
    assert result.error == "certificate pool_state_hash mismatch"


def test_uniform_batch_certificate_rejects_nonreduced_price_ratio() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
        intent_set_hash=certificate.intent_set_hash,
        price_num=2,
        price_den=2,
        fills=certificate.fills,
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate price ratio must be reduced"


def test_uniform_batch_certificate_rejects_price_ratio_above_domain() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
        intent_set_hash=certificate.intent_set_hash,
        price_num=UNIFORM_BATCH_PRICE_RATIO_MAX + 1,
        price_den=1,
        fills=certificate.fills,
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate.price_num exceeds maximum"


def test_uniform_batch_certificate_rejects_fill_output_above_domain() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate_obj = _certificate_for(intents).to_dict()
    certificate_obj["fills"][0]["executed_out"] = UNIFORM_BATCH_OUTPUT_AMOUNT_MAX + 1

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate_obj,
    )

    assert result.ok is False
    assert result.error == "fill.executed_out exceeds maximum"


def test_uniform_batch_certificate_rejects_min_amount_out_above_domain() -> None:
    pool = _pool()
    balances = _balances()
    intents = [
        _swap(
            "alice-a-to-b",
            "alice",
            "A",
            "B",
            min_amount_out=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX + 1,
        ),
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
    assert result.error == "intent.min_amount_out exceeds maximum"


def test_uniform_batch_certificate_rejects_too_many_fills() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate_obj = _certificate_for(intents).to_dict()
    certificate_obj["fills"] = [certificate_obj["fills"][0]] * (UNIFORM_BATCH_MAX_FILLS + 1)

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate_obj,
    )

    assert result.ok is False
    assert result.error == f"certificate.fills exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}"


def test_uniform_batch_certificate_rejects_too_many_intents_before_hashing() -> None:
    pool = _pool()
    balances = _balances()
    certificate = _certificate_for(_balanced_intents())
    intents = [
        _swap(f"many-{i}", "alice", "A", "B", min_amount_out=1)
        for i in range(UNIFORM_BATCH_MAX_FILLS + 1)
    ]

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == f"uniform batch intent count exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}"


def test_uniform_batch_certificate_rejects_unsupported_policy_id() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
        intent_set_hash=certificate.intent_set_hash,
        price_num=certificate.price_num,
        price_den=certificate.price_den,
        fills=certificate.fills,
        policy_id="zenodex/upba_v1/partial_fill_experiment",
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "unsupported uniform batch policy_id"


def test_uniform_batch_certificate_rejects_unsupported_price_objective_id() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
        intent_set_hash=certificate.intent_set_hash,
        price_num=certificate.price_num,
        price_den=certificate.price_den,
        fills=certificate.fills,
        price_objective_id="zenodex/upba_v1/solver_supplied_price",
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "unsupported uniform batch price_objective_id"


def test_uniform_batch_certificate_rejects_unknown_certificate_key() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate_obj = _certificate_for(intents).to_dict()
    certificate_obj["future_policy_knob"] = True

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate_obj,
    )

    assert result.ok is False
    assert result.error == "certificate contains unsupported keys: future_policy_knob"


def test_uniform_batch_certificate_rejects_unknown_fill_key() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate_obj = _certificate_for(intents).to_dict()
    certificate_obj["fills"][0]["future_fill_knob"] = True

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate_obj,
    )

    assert result.ok is False
    assert result.error == "certificate.fill contains unsupported keys: future_fill_knob"


def test_uniform_batch_certificate_rejects_missing_admitted_intent_fill() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
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


def test_uniform_batch_certificate_rejects_partial_fill() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    first = certificate.fills[0]
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
        intent_set_hash=certificate.intent_set_hash,
        price_num=certificate.price_num,
        price_den=certificate.price_den,
        fills=(
            UniformBatchFillV1(
                intent_id=first.intent_id,
                executed_in=99,
                executed_out=99,
            ),
            certificate.fills[1],
        ),
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate fill must consume full intent amount_in"


def test_uniform_batch_certificate_rejects_invalid_direct_dataclass_shape() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
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


def test_uniform_batch_certificate_rejects_zero_price_den() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    certificate = UniformBatchCertificateV1(
        pool_id=certificate.pool_id,
        base_asset=certificate.base_asset,
        quote_asset=certificate.quote_asset,
        pool_state_hash=certificate.pool_state_hash,
        intent_set_hash=certificate.intent_set_hash,
        price_num=certificate.price_num,
        price_den=0,
        fills=certificate.fills,
    )

    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "certificate.price_den must be positive"


def test_uniform_batch_certificate_rejects_intent_set_hash_mismatch() -> None:
    pool = _pool()
    balances = _balances()
    intents = _balanced_intents()
    certificate = _certificate_for(intents)
    tampered = replace(
        _swap("alice-a-to-b", "alice", "A", "B", min_amount_out=1),
        intent_id=intents[0].intent_id,
    )
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
    tampered_fill = replace(settlement.fills[0], amount_out_filled=99)
    tampered_settlement = replace(
        settlement,
        fills=[tampered_fill, *settlement.fills[1:]],
    )

    ok, err = validate_uniform_batch_settlement_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
        settlement=tampered_settlement,
    )

    assert ok is False
    assert err == "uniform batch settlement mismatch"
