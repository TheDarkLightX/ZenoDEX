from __future__ import annotations

from hashlib import sha256
from math import gcd

from src.core.cpmm import compute_fee_total
from src.core.dex import DexConfig, DexState
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
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
)
from src.core.uniform_batch_optimality import (
    UniformBatchAuditCandidateV1,
    UniformBatchOptimalityCertificateV1,
    build_uniform_batch_exact_out_grid_audit_candidates_v1,
    build_uniform_batch_optimality_certificate_v1,
    build_uniform_batch_v2_bounded_grid_audit_candidates_v1,
    build_uniform_batch_v2_bounded_grid_optimality_table_v1,
    uniform_batch_candidate_id_for_certificate,
    uniform_batch_optimality_candidate_set_hash,
    uniform_batch_v2_bounded_grid_optimality_table_root,
)
from src.integration.dex_engine import DexEngineConfig, apply_ops, make_strict_upba_engine_config
from src.integration.operations import create_settlement_operation, parse_intents
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

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


def _exact_out_swap_dict(
    *,
    label: str,
    asset_in: str,
    asset_out: str,
    nonce: int,
    amount_out: int = 100,
    max_amount_in: int = 100,
) -> dict[str, object]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_OUT",
        "intent_id": _intent_id(label),
        "sender_pubkey": SENDER,
        "deadline": 999_999_999,
        "nonce": nonce,
        "pool_id": "pool_ab",
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_out": amount_out,
        "max_amount_in": max_amount_in,
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


def _exact_out_intent(
    *,
    label: str,
    asset_in: str,
    asset_out: str,
    nonce: int,
    amount_out: int = 100,
    max_amount_in: int = 100,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_intent_id(label),
        sender_pubkey=SENDER,
        deadline=999_999_999,
        fields={
            "nonce": nonce,
            "pool_id": "pool_ab",
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_out": amount_out,
            "max_amount_in": max_amount_in,
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
    return UniformBatchCertificateV1(
        pool_id=pool.pool_id,
        base_asset=pool.asset0,
        quote_asset=pool.asset1,
        pool_state_hash=uniform_batch_pool_state_hash(pool),
        intent_set_hash=uniform_batch_intent_set_hash(intents),
        price_num=price_num,
        price_den=price_den,
        fills=tuple(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=int(executed_in_by_id[intent.intent_id]),
                executed_out=int(intent.get_field("amount_out")),
            )
            for intent in sorted(intents, key=lambda item: item.intent_id)
        ),
        policy_id=UNIFORM_BATCH_POLICY_V3_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
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


def _exact_out_intents() -> list[Intent]:
    return [
        _exact_out_intent(label="a-to-b-exact-out", asset_in="A", asset_out="B", nonce=1),
        _exact_out_intent(label="b-to-a-exact-out", asset_in="B", asset_out="A", nonce=2),
    ]


def _exact_out_intent_ops() -> list[dict[str, object]]:
    return [
        _exact_out_swap_dict(label="a-to-b-exact-out", asset_in="A", asset_out="B", nonce=1),
        _exact_out_swap_dict(label="b-to-a-exact-out", asset_in="B", asset_out="A", nonce=2),
    ]


def _ops_with_uniform_exact_out_certificate() -> dict[str, object]:
    state = _state()
    intents = _exact_out_intents()
    cert = _v3_exact_out_certificate_for(
        intents=intents,
        pool=state.pools["pool_ab"],
        executed_in_by_id={intent.intent_id: 100 for intent in intents},
    )
    settlement = build_uniform_batch_settlement_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        certificate=cert,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["uniform_batch_certificate"] = cert.to_dict()
    return {"2": _exact_out_intent_ops(), "3": settlement_op}


def _ops_with_uniform_exact_out_certificate_and_optimality() -> dict[str, object]:
    ops = _ops_with_uniform_exact_out_certificate()
    cert = UniformBatchCertificateV1.from_obj(ops["3"]["uniform_batch_certificate"])
    optimality = _optimality_certificate_for_uniform_certificate(cert)
    ops["3"]["uniform_batch_optimality_certificate"] = optimality.to_dict()
    return ops


def _ops_with_uniform_exact_out_certificate_and_grid_optimality(
    *,
    max_price_num: int = 1,
    max_price_den: int = 1,
) -> dict[str, object]:
    ops = _ops_with_uniform_exact_out_certificate()
    state = _state()
    intents = _exact_out_intents()
    scored_candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        max_price_num=max_price_num,
        max_price_den=max_price_den,
    )
    optimality = build_uniform_batch_optimality_certificate_v1(
        tuple(item.audit_candidate for item in scored_candidates)
    )
    ops["3"]["uniform_batch_optimality_certificate"] = optimality.to_dict()
    ops["3"]["uniform_batch_v3_exact_out_grid"] = {
        "max_price_num": max_price_num,
        "max_price_den": max_price_den,
    }
    return ops


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


def _ops_with_v2_partial_certificate_and_bounded_grid(
    *,
    table_root: str | None = None,
) -> dict[str, object]:
    ops = _ops_with_v2_partial_certificate()
    state = _state()
    intents = _ratio_intents()
    winner_cert = UniformBatchCertificateV1.from_obj(ops["3"]["uniform_batch_certificate"])
    lower_cert = _v2_certificate_for(
        intents=intents,
        pool=state.pools["pool_ab"],
        executed_in_by_id={
            intents[0].intent_id: 50,
            intents[1].intent_id: 50,
        },
    )
    fill_vectors = (lower_cert.fills, winner_cert.fills)
    scored_candidates = build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
        intents=intents,
        pool=state.pools["pool_ab"],
        balances=state.balances,
        max_price_num=1,
        max_price_den=1,
        fill_vectors=fill_vectors,
    )
    optimality = build_uniform_batch_optimality_certificate_v1(
        tuple(item.audit_candidate for item in scored_candidates)
    )
    rows = build_uniform_batch_v2_bounded_grid_optimality_table_v1(scored_candidates)
    ops["3"]["uniform_batch_optimality_certificate"] = optimality.to_dict()
    ops["3"]["uniform_batch_v2_bounded_grid"] = {
        "max_price_num": 1,
        "max_price_den": 1,
        "fill_vectors": [
            [fill.to_dict() for fill in fill_vector]
            for fill_vector in fill_vectors
        ],
        "table_root": table_root or uniform_batch_v2_bounded_grid_optimality_table_root(rows),
    }
    return ops


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


def test_engine_accepts_uniform_batch_v3_exact_out_certificate_when_enabled() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_exact_out_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V3"
    assert result.settlement.events[0]["policy_id"] == UNIFORM_BATCH_POLICY_V3_ID


def test_engine_strict_upba_posture_rejects_supported_swaps_without_certificate() -> None:
    ops = _ops_with_uniform_certificate()
    del ops["3"]["uniform_batch_certificate"]

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate required for supported swaps"


def test_engine_strict_upba_posture_rejects_supported_exact_out_without_certificate() -> None:
    ops = _ops_with_uniform_exact_out_certificate()
    del ops["3"]["uniform_batch_certificate"]

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate required for supported swaps"


def test_engine_strict_upba_posture_rejects_certificate_without_optimality() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_uniform_batch_optimality_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch optimality certificate required"


def test_engine_strict_upba_posture_accepts_certificate_with_bound_optimality() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_uniform_batch_optimality_certificate=True,
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


def test_engine_strict_upba_posture_accepts_exact_out_certificate_with_bound_optimality() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_uniform_batch_optimality_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_exact_out_certificate_and_optimality(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V3"


def test_engine_strict_upba_posture_rejects_v3_exact_out_without_grid_evidence() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_uniform_batch_optimality_certificate=True,
            require_uniform_batch_v3_exact_out_grid_optimality=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_exact_out_certificate_and_optimality(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch v3 exact-out grid evidence required"


def test_engine_strict_upba_posture_accepts_v3_exact_out_with_grid_evidence() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_uniform_batch_optimality_certificate=True,
            require_uniform_batch_v3_exact_out_grid_optimality=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_uniform_exact_out_certificate_and_grid_optimality(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V3"


def test_engine_rejects_uniform_batch_v3_exact_out_grid_candidate_set_mismatch() -> None:
    ops = _ops_with_uniform_exact_out_certificate_and_grid_optimality()
    ops["3"]["uniform_batch_optimality_certificate"]["candidate_set_hash"] = "different"

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
        "uniform batch optimality certificate rejected: "
        "v3 exact-out grid candidate_set_hash mismatch"
    )


def test_engine_rejects_uniform_batch_v3_exact_out_grid_without_optimality() -> None:
    ops = _ops_with_uniform_exact_out_certificate()
    ops["3"]["uniform_batch_v3_exact_out_grid"] = {
        "max_price_num": 1,
        "max_price_den": 1,
    }

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
    assert result.error == "uniform batch v3 exact-out grid evidence requires optimality certificate"


def test_engine_rejects_uniform_batch_v3_exact_out_grid_on_v2_certificate() -> None:
    ops = _ops_with_v2_partial_certificate_and_bounded_grid()
    ops["3"]["uniform_batch_v3_exact_out_grid"] = {
        "max_price_num": 1,
        "max_price_den": 1,
    }
    del ops["3"]["uniform_batch_v2_bounded_grid"]

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
    assert result.error == "uniform batch v3 exact-out grid evidence requires v3 uniform batch certificate"


def test_engine_rejects_uniform_batch_bounded_grid_evidence_provided_twice() -> None:
    ops = _ops_with_v2_partial_certificate_and_bounded_grid()
    ops["3"]["uniform_batch_v3_exact_out_grid"] = {
        "max_price_num": 1,
        "max_price_den": 1,
    }

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
    assert result.error == "uniform batch bounded-grid evidence provided twice"


def test_engine_rejects_uniform_batch_v3_exact_out_grid_non_object() -> None:
    ops = _ops_with_uniform_exact_out_certificate_and_optimality()
    ops["3"]["uniform_batch_v3_exact_out_grid"] = "bad"

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
        "invalid settlement: settlement uniform_batch_v3_exact_out_grid must be an object"
    )


def test_engine_rejects_uniform_batch_v3_exact_out_grid_missing_bound() -> None:
    ops = _ops_with_uniform_exact_out_certificate_and_grid_optimality()
    del ops["3"]["uniform_batch_v3_exact_out_grid"]["max_price_den"]

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
        "uniform batch optimality certificate rejected: "
        "uniform batch v3 exact-out grid evidence missing max_price_den"
    )


def test_engine_rejects_uniform_batch_v3_exact_out_grid_unknown_field() -> None:
    ops = _ops_with_uniform_exact_out_certificate_and_grid_optimality()
    ops["3"]["uniform_batch_v3_exact_out_grid"]["table_root"] = "0x" + "0" * 64

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
        "uniform batch optimality certificate rejected: "
        "uniform batch v3 exact-out grid evidence has unknown field table_root"
    )


def test_engine_rejects_uniform_batch_v3_exact_out_grid_bool_bound() -> None:
    ops = _ops_with_uniform_exact_out_certificate_and_grid_optimality()
    ops["3"]["uniform_batch_v3_exact_out_grid"]["max_price_num"] = True

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
        "uniform batch optimality certificate rejected: "
        "uniform batch v3 exact-out grid max_price_num must be an int"
    )


def test_engine_strict_upba_config_requires_upba_enabled() -> None:
    try:
        DexEngineConfig(require_uniform_batch_certificate_for_supported_swaps=True)
    except ValueError as exc:
        assert str(exc) == "strict UPBA requirements require allow_uniform_batch_certificate=True"
    else:
        raise AssertionError("expected strict UPBA config rejection without allow_uniform_batch_certificate")


def test_strict_upba_engine_config_factory_enables_required_flags() -> None:
    config = make_strict_upba_engine_config()

    assert config.allow_uniform_batch_certificate is True
    assert config.require_uniform_batch_certificate_for_supported_swaps is True
    assert config.require_uniform_batch_optimality_certificate is True
    assert config.require_uniform_batch_v2_bounded_grid_optimality is True
    assert config.require_uniform_batch_v3_exact_out_grid_optimality is True


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


def test_engine_strict_upba_posture_rejects_v2_certificate_without_bounded_grid_evidence() -> None:
    ops = _ops_with_v2_partial_certificate_and_bounded_grid()
    del ops["3"]["uniform_batch_v2_bounded_grid"]

    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_uniform_batch_optimality_certificate=True,
            require_uniform_batch_v2_bounded_grid_optimality=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch v2 bounded-grid evidence required"


def test_engine_strict_upba_posture_accepts_v2_certificate_with_bounded_grid_evidence() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_uniform_batch_certificate_for_supported_swaps=True,
            require_uniform_batch_optimality_certificate=True,
            require_uniform_batch_v2_bounded_grid_optimality=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_v2_partial_certificate_and_bounded_grid(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok, result.error
    assert result.settlement is not None
    assert result.settlement.events is not None
    assert result.settlement.events[0]["type"] == "UNIFORM_BATCH_CLEARING_V2"


def test_engine_rejects_uniform_batch_v2_bounded_grid_table_root_mismatch() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
        ),
        state=_state(),
        operations=_ops_with_v2_partial_certificate_and_bounded_grid(table_root="0x" + "0" * 64),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == (
        "uniform batch optimality certificate rejected: v2 bounded-grid table_root mismatch"
    )


def test_engine_rejects_uniform_batch_v2_zero_fill_rejected_member_by_default() -> None:
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

    assert result.ok is False
    assert result.error is not None
    assert "settlement contains rejected intent at public DEX boundary" in result.error


def test_engine_accepts_uniform_batch_v2_zero_fill_rejected_member_when_boundary_opted_out() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
            dex_config=DexConfig(reject_settlements_with_rejected_intents=False),
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


def test_engine_rejects_uniform_batch_certificate_when_protocol_fees_enabled() -> None:
    result = apply_ops(
        config=DexEngineConfig(
            allow_uniform_batch_certificate=True,
            require_intent_signatures=False,
            dex_config=DexConfig(
                protocol_fee_share_bps=5_000,
                protocol_fee_recipient_pubkey=SENDER,
            ),
        ),
        state=_state(),
        operations=_ops_with_uniform_certificate(),
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert result.ok is False
    assert result.error == "uniform batch certificate cannot be used when protocol fees are enabled"


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
