from __future__ import annotations

from hashlib import sha256

from src.core.batch_clearing import validate_settlement
from src.core.settlement import FillAction
from src.core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    UNIFORM_BATCH_MAX_FILLS,
    UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
    UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
    UNIFORM_BATCH_POLICY_ID,
    UNIFORM_BATCH_PRICE_RATIO_MAX,
    build_uniform_batch_settlement_v1,
    uniform_batch_certificate_hash,
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
