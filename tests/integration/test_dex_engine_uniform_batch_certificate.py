from __future__ import annotations

from hashlib import sha256
from math import gcd

from src.core.cpmm import compute_fee_total
from src.core.batch_clearing import compute_settlement
from src.core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_MAX_FILLS,
    UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
    UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
    UNIFORM_BATCH_POLICY_ID,
    UNIFORM_BATCH_POLICY_V2_ID,
    UNIFORM_BATCH_PRICE_RATIO_MAX,
    UNIFORM_BATCH_UNFILLED_REASON,
    build_uniform_batch_settlement_v1,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
)
from src.core.uniform_batch_optimality import (
    UniformBatchAuditCandidateV1,
    UniformBatchOptimalityCertificateV1,
    uniform_batch_candidate_id_for_certificate,
    uniform_batch_optimality_candidate_set_hash,
)
from src.core.uniform_batch_price_grid_table import build_uniform_batch_price_grid_table_v1
from src.core.settlement import FillAction
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation, parse_intents
from src.integration.upba_production_config import make_upba_v1_bounded_price_grid_engine_config
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus
from src.core.dex import DexState


SENDER = "0x" + "aa" * 48


def _intent_id(label: str) -> str:
    return "0x" + sha256(label.encode("utf-8")).hexdigest()


def _audit_candidate_id(label: str) -> str:
    return "0x" + sha256(f"audit:{label}".encode("utf-8")).hexdigest()


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


def _high_fee_pool() -> PoolState:
    pool = _pool()
    pool.fee_bps = 1_000
    return pool


def _state() -> DexState:
    balances = BalanceTable()
    balances.set(SENDER, "A", 1_000)
    balances.set(SENDER, "B", 1_000)
    return DexState(
        balances=balances,
        pools={"pool_ab": _pool()},
        lp_balances=LPTable(),
    )


def _high_fee_state() -> DexState:
    balances = BalanceTable()
    balances.set(SENDER, "A", 1_000)
    balances.set(SENDER, "B", 1_000)
    return DexState(
        balances=balances,
        pools={"pool_ab": _high_fee_pool()},
        lp_balances=LPTable(),
    )


def _swap_dict(
    *,
    label: str,
    asset_in: str,
    asset_out: str,
    nonce: int,
    amount_in: int = 100,
    min_amount_out: int = 90,
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
        "amount_in": amount_in,
        "min_amount_out": min_amount_out,
    }


def _intent(
    *,
    label: str,
    asset_in: str,
    asset_out: str,
    nonce: int,
    amount_in: int = 100,
    min_amount_out: int = 90,
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
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
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
    fills = []
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


def _ratio_intents() -> list[Intent]:
    return [
        _intent(
            label="a-to-b",
            asset_in="A",
            asset_out="B",
            nonce=1,
            amount_in=100,
            min_amount_out=1,
        ),
        _intent(
            label="b-to-a",
            asset_in="B",
            asset_out="A",
            nonce=2,
            amount_in=200,
            min_amount_out=1,
        ),
    ]


def _ratio_intent_ops() -> list[dict[str, object]]:
    return [
        _swap_dict(
            label="a-to-b",
            asset_in="A",
            asset_out="B",
            nonce=1,
            amount_in=100,
            min_amount_out=1,
        ),
        _swap_dict(
            label="b-to-a",
            asset_in="B",
            asset_out="A",
            nonce=2,
            amount_in=200,
            min_amount_out=1,
        ),
    ]


def _certificate_with_price(
    intents: list[Intent],
    *,
    price_num: int,
    price_den: int,
) -> UniformBatchCertificateV1:
    return UniformBatchCertificateV1(
        pool_id="pool_ab",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=uniform_batch_pool_state_hash(_pool()),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=price_num,
        price_den=price_den,
        fills=tuple(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=int(intent.get_field("amount_in")),
                executed_out=(
                    (int(intent.get_field("amount_in")) * price_num) // price_den
                    if str(intent.get_field("asset_in")) == "A"
                    else (int(intent.get_field("amount_in")) * price_den) // price_num
                ),
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


def _ops_with_sequential_settlement() -> dict[str, object]:
    state = _state()
    settlement = compute_settlement(
        intents=_intents(),
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )
    return {"2": _intent_ops(), "3": create_settlement_operation(settlement)["3"]}


def _optimality_certificate_for_uniform_certificate(
    cert: UniformBatchCertificateV1,
    *,
    winner_id: str | None = None,
) -> UniformBatchOptimalityCertificateV1:
    declared_winner_id = winner_id or uniform_batch_candidate_id_for_certificate(cert)
    candidates = tuple(
        sorted(
            (
                UniformBatchAuditCandidateV1(
                    candidate_id=_audit_candidate_id("lower-volume"),
                    volume=199,
                    surplus=50,
                ),
                UniformBatchAuditCandidateV1(
                    candidate_id=declared_winner_id,
                    volume=200,
                    surplus=40,
                ),
            ),
            key=lambda item: item.candidate_id,
        )
    )
    return UniformBatchOptimalityCertificateV1(
        candidate_set_hash=uniform_batch_optimality_candidate_set_hash(candidates),
        winner_id=declared_winner_id,
        volume_upper=200,
        surplus_upper_at_winner_volume=40,
        candidates=candidates,
    )


def _ops_with_uniform_certificate_and_optimality(
    *,
    winner_id: str | None = None,
) -> dict[str, object]:
    ops = _ops_with_uniform_certificate()
    cert = UniformBatchCertificateV1.from_obj(ops["3"]["uniform_batch_certificate"])
    optimality = _optimality_certificate_for_uniform_certificate(cert, winner_id=winner_id)
    ops["3"]["uniform_batch_optimality_certificate"] = optimality.to_dict()
    return ops


def _ops_with_uniform_certificate_and_price_grid() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    ops = _ops_with_uniform_certificate()
    config, rows, witness = build_uniform_batch_price_grid_table_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        uniform_batch_certificate=cert,
        settlement_id="settlement-engine-price-grid",
        max_price_num=2,
        max_price_den=2,
    )
    ops["3"]["uniform_batch_price_grid_config"] = config.to_dict()
    ops["3"]["uniform_batch_price_grid_rows"] = [row.to_dict() for row in rows]
    ops["3"]["uniform_batch_price_grid_witness"] = witness.to_dict()
    return ops


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


def _ops_with_nonreduced_price_ratio() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    nonreduced_cert = UniformBatchCertificateV1(
        pool_id=cert.pool_id,
        base_asset=cert.base_asset,
        quote_asset=cert.quote_asset,
        pool_state_hash=cert.pool_state_hash,
        intent_set_hash=cert.intent_set_hash,
        price_num=2,
        price_den=2,
        fills=cert.fills,
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = nonreduced_cert.to_dict()
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_unsupported_policy_id() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    unsupported_cert = UniformBatchCertificateV1(
        pool_id=cert.pool_id,
        base_asset=cert.base_asset,
        quote_asset=cert.quote_asset,
        pool_state_hash=cert.pool_state_hash,
        intent_set_hash=cert.intent_set_hash,
        price_num=cert.price_num,
        price_den=cert.price_den,
        fills=cert.fills,
        policy_id="zenodex/upba_v1/partial_fill_experiment",
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = unsupported_cert.to_dict()
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_price_ratio_above_domain() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    out_of_domain_cert = UniformBatchCertificateV1(
        pool_id=cert.pool_id,
        base_asset=cert.base_asset,
        quote_asset=cert.quote_asset,
        pool_state_hash=cert.pool_state_hash,
        intent_set_hash=cert.intent_set_hash,
        price_num=UNIFORM_BATCH_PRICE_RATIO_MAX + 1,
        price_den=1,
        fills=cert.fills,
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = out_of_domain_cert.to_dict()
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_fill_output_above_domain() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    certificate_obj = cert.to_dict()
    certificate_obj["fills"][0]["executed_out"] = UNIFORM_BATCH_OUTPUT_AMOUNT_MAX + 1
    settlement_op["uniform_batch_certificate"] = certificate_obj
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_too_many_uniform_fills() -> dict[str, object]:
    state = _state()
    intents = _intents()
    cert = _certificate(intents)
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    certificate_obj = cert.to_dict()
    certificate_obj["fills"] = [certificate_obj["fills"][0]] * (UNIFORM_BATCH_MAX_FILLS + 1)
    settlement_op["uniform_batch_certificate"] = certificate_obj
    return {"2": _intent_ops(), "3": settlement_op}


def _ops_with_noncanonical_price_objective() -> dict[str, object]:
    state = _state()
    intents = _ratio_intents()
    canonical_cert = _certificate_with_price(intents, price_num=2, price_den=1)
    noncanonical_cert = _certificate_with_price(intents, price_num=3, price_den=2)
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=canonical_cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = noncanonical_cert.to_dict()
    return {"2": _ratio_intent_ops(), "3": settlement_op}


def _ops_with_v2_partial_certificate() -> dict[str, object]:
    state = _state()
    intents = _ratio_intents()
    cert = _v2_certificate_for(
        intents=intents,
        pool=state.pools["pool_ab"],
        executed_in_by_id={
            intents[0].intent_id: 100,
            intents[1].intent_id: 100,
        },
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = cert.to_dict()
    return {"2": _ratio_intent_ops(), "3": settlement_op}


def _ops_with_v2_zero_fill_certificate() -> dict[str, object]:
    state = _high_fee_state()
    intents = _ratio_intents()
    cert = _v2_certificate_for(
        intents=intents,
        pool=state.pools["pool_ab"],
        executed_in_by_id={
            intents[0].intent_id: 100,
            intents[1].intent_id: 0,
        },
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = cert.to_dict()
    return {"2": _ratio_intent_ops(), "3": settlement_op}


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
            "policy_id": UNIFORM_BATCH_POLICY_ID,
            "price_objective_id": UNIFORM_BATCH_PRICE_OBJECTIVE_ID,
            "certificate_hash": _certificate(_intents()).hash(),
        }
    ]


def test_engine_accepts_uniform_batch_optimality_certificate_when_bound() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate_and_optimality(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V1"


def test_engine_accepts_uniform_batch_price_grid_evidence_when_bound() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate_and_price_grid(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V1"


def test_engine_accepts_uniform_batch_price_grid_evidence_when_required() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_price_grid_evidence=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate_and_price_grid(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V1"


def test_engine_rejects_uniform_batch_certificate_without_price_grid_when_required() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_price_grid_evidence=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch price grid evidence required"


def test_engine_config_rejects_required_price_grid_without_uniform_batch_bridge() -> None:
    try:
        DexEngineConfig(require_uniform_batch_price_grid_evidence=True)
    except ValueError as exc:
        assert str(exc) == (
            "require_uniform_batch_price_grid_evidence=True "
            "requires allow_uniform_batch_certificate=True"
        )
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected price-grid requirement config rejection")


def test_engine_config_rejects_required_uniform_batch_without_bridge() -> None:
    try:
        DexEngineConfig(require_uniform_batch_certificate=True)
    except ValueError as exc:
        assert str(exc) == (
            "require_uniform_batch_certificate=True requires allow_uniform_batch_certificate=True"
        )
    else:  # pragma: no cover - explicit failure branch for assertion clarity
        raise AssertionError("expected uniform-batch requirement config rejection")


def test_upba_bounded_price_grid_engine_config_forces_strict_posture() -> None:
    cfg = make_upba_v1_bounded_price_grid_engine_config(
        DexEngineConfig(
            allow_missing_settlement=True,
            require_settlement_match=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            allow_unsigned_intents_if_tx_sender_matches=False,
        )
    )

    assert cfg.allow_missing_settlement is False
    assert cfg.require_settlement_match is True
    assert cfg.require_intent_signatures is True
    assert cfg.allow_unsigned_intents_if_tx_sender_matches is False
    assert cfg.allow_external_tools is False
    assert cfg.consensus_mode is True
    assert cfg.allow_uniform_batch_certificate is True
    assert cfg.require_uniform_batch_certificate is True
    assert cfg.require_uniform_batch_price_grid_evidence is True
    assert cfg.enable_test_fault_injection is False
    assert cfg.fault_injection is None


def test_engine_rejects_swap_batch_without_uniform_certificate_when_required() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_sequential_settlement(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate required"


def test_upba_bounded_price_grid_engine_config_accepts_bound_certificate() -> None:
    result = apply_ops(
        config=make_upba_v1_bounded_price_grid_engine_config(
            DexEngineConfig(require_intent_signatures=False)
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate_and_price_grid(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V1"


def test_engine_rejects_uniform_batch_price_grid_without_uniform_certificate() -> None:
    ops = _ops_with_uniform_certificate_and_price_grid()
    del ops["3"]["uniform_batch_certificate"]

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch price grid evidence requires uniform batch certificate"


def test_engine_rejects_partial_uniform_batch_price_grid_evidence() -> None:
    ops = _ops_with_uniform_certificate_and_price_grid()
    del ops["3"]["uniform_batch_price_grid_rows"]

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch price grid evidence requires config, rows, and witness"


def test_engine_rejects_uniform_batch_price_grid_non_list_rows() -> None:
    ops = _ops_with_uniform_certificate_and_price_grid()
    ops["3"]["uniform_batch_price_grid_rows"] = "bad"

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "invalid settlement: settlement uniform_batch_price_grid_rows must be a list"


def test_engine_rejects_tampered_uniform_batch_price_grid_evidence() -> None:
    ops = _ops_with_uniform_certificate_and_price_grid()
    rows = ops["3"]["uniform_batch_price_grid_rows"]
    assert isinstance(rows, list)
    rows[0]["volume"] = int(rows[0]["volume"]) + 1

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == (
        "uniform batch price grid evidence rejected: "
        "price grid candidate_table_root mismatch"
    )


def test_engine_rejects_uniform_batch_optimality_without_uniform_certificate() -> None:
    ops = _ops_with_uniform_certificate_and_optimality()
    del ops["3"]["uniform_batch_certificate"]

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch optimality certificate requires uniform batch certificate"


def test_engine_rejects_uniform_batch_optimality_certificate_mismatched_winner() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate_and_optimality(
            winner_id=_audit_candidate_id("mismatch"),
        ),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert (
        result.error
        == "uniform batch optimality certificate rejected: "
        "optimality certificate winner_id does not match uniform batch certificate"
    )


def test_engine_rejects_uniform_batch_optimality_certificate_non_object() -> None:
    ops = _ops_with_uniform_certificate()
    ops["3"]["uniform_batch_optimality_certificate"] = "bad"

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == (
        "invalid settlement: settlement uniform_batch_optimality_certificate must be an object"
    )


def test_engine_accepts_uniform_batch_v2_partial_certificate_when_enabled() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_v2_partial_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V2"
    assert result.settlement.events[0]["policy_id"] == UNIFORM_BATCH_POLICY_V2_ID
    assert [fill.action for fill in result.settlement.fills] == [FillAction.FILL, FillAction.FILL]
    assert [fill.amount_in_filled for fill in result.settlement.fills] == [100, 100]


def test_engine_accepts_uniform_batch_v2_zero_fill_rejected_member() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_high_fee_state(),
        operations=_ops_with_v2_zero_fill_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V2"
    assert FillAction.REJECT in [fill.action for fill in result.settlement.fills]
    rejected = [fill for fill in result.settlement.fills if fill.action == FillAction.REJECT]
    assert rejected[0].reason == UNIFORM_BATCH_UNFILLED_REASON


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


def test_engine_rejects_uniform_batch_certificate_nonreduced_price_ratio() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_nonreduced_price_ratio(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate rejected: certificate price ratio must be reduced"


def test_engine_rejects_uniform_batch_certificate_unsupported_policy_id() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_unsupported_policy_id(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate rejected: unsupported uniform batch policy_id"


def test_engine_rejects_uniform_batch_certificate_price_ratio_above_domain() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_price_ratio_above_domain(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate rejected: certificate.price_num exceeds maximum"


def test_engine_rejects_uniform_batch_certificate_fill_output_above_domain() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_fill_output_above_domain(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate rejected: fill.executed_out exceeds maximum"


def test_engine_rejects_uniform_batch_certificate_too_many_fills() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_too_many_uniform_fills(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert (
        result.error
        == f"uniform batch certificate rejected: certificate.fills exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}"
    )


def test_engine_rejects_uniform_batch_certificate_noncanonical_price_objective() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_noncanonical_price_objective(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert (
        result.error
        == "uniform batch certificate rejected: certificate price does not match canonical UPBA objective"
    )


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
