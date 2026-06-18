from __future__ import annotations

from math import gcd

import pytest

from src.core.uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
    UNIFORM_BATCH_POLICY_V2_ID,
    UNIFORM_BATCH_POLICY_V3_ID,
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    uniform_batch_exact_out_gross_in_for_price,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
    verify_uniform_batch_certificate_v1,
)
from src.core.uniform_batch_optimality import (
    UniformBatchAuditCandidateV1,
    UniformBatchOptimalityCertificateV1,
    UniformBatchOptimalityVerificationResult,
    build_uniform_batch_exact_out_grid_audit_candidates_v1,
    build_uniform_batch_optimality_certificate_v1,
    build_uniform_batch_v2_bounded_grid_audit_candidates_v1,
    build_uniform_batch_v2_bounded_grid_optimality_table_v1,
    uniform_batch_candidate_id_for_certificate,
    uniform_batch_candidate_id_for_certificate_hash,
    uniform_batch_fill_vector_hash,
    uniform_batch_optimality_candidate_set_hash,
    uniform_batch_optimality_certificate_hash,
    uniform_batch_v2_bounded_grid_optimality_table_root,
    verify_uniform_batch_bound_optimality_certificate_v1,
    verify_uniform_batch_optimality_certificate_v1,
    verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1,
    verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus


def _candidate(candidate_id: str, *, volume: int, surplus: int) -> UniformBatchAuditCandidateV1:
    return UniformBatchAuditCandidateV1(candidate_id=candidate_id, volume=volume, surplus=surplus)


def _certificate(
    candidates: tuple[UniformBatchAuditCandidateV1, ...],
    *,
    winner_id: str,
    volume_upper: int,
    surplus_upper: int,
) -> UniformBatchOptimalityCertificateV1:
    return UniformBatchOptimalityCertificateV1(
        candidate_set_hash=uniform_batch_optimality_candidate_set_hash(candidates),
        winner_id=winner_id,
        volume_upper=volume_upper,
        surplus_upper_at_winner_volume=surplus_upper,
        candidates=candidates,
    )


def _uniform_certificate(label: str = "winner") -> UniformBatchCertificateV1:
    return UniformBatchCertificateV1(
        pool_id=f"pool-{label}",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=f"pool-hash-{label}",
        intent_set_hash=f"intent-set-hash-{label}",
        price_num=1,
        price_den=1,
        fills=(
            UniformBatchFillV1(
                intent_id=f"intent-{label}",
                executed_in=100,
                executed_out=100,
            ),
        ),
    )


def _uniform_v2_partial_certificate(label: str = "winner") -> UniformBatchCertificateV1:
    return UniformBatchCertificateV1(
        pool_id=f"pool-{label}",
        base_asset="A",
        quote_asset="B",
        pool_state_hash=f"pool-hash-{label}",
        intent_set_hash=f"intent-set-hash-{label}",
        price_num=1,
        price_den=1,
        fills=(
            UniformBatchFillV1(
                intent_id=f"intent-{label}-a",
                executed_in=60,
                executed_out=60,
            ),
            UniformBatchFillV1(
                intent_id=f"intent-{label}-b",
                executed_in=0,
                executed_out=0,
            ),
        ),
        policy_id=UNIFORM_BATCH_POLICY_V2_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    )


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


_HASH_A = "0x" + "a" * 64
_HASH_B = "0x" + "b" * 64
_HASH_C = "0x" + "c" * 64


def test_uniform_batch_optimality_result_ok_flag_must_be_bool() -> None:
    with pytest.raises(ValueError, match="ok must be bool"):
        UniformBatchOptimalityVerificationResult(
            ok=1,  # type: ignore[arg-type]
            error=None,
            certificate_hash=_HASH_A,
            candidate_set_hash=_HASH_B,
        )


def test_uniform_batch_optimality_result_accept_requires_hashes() -> None:
    with pytest.raises(ValueError, match="certificate_hash"):
        UniformBatchOptimalityVerificationResult(ok=True, error=None)

    with pytest.raises(ValueError, match="candidate_set_hash"):
        UniformBatchOptimalityVerificationResult(
            ok=True,
            error=None,
            certificate_hash=_HASH_A,
        )

    with pytest.raises(ValueError, match="cannot include error"):
        UniformBatchOptimalityVerificationResult(
            ok=True,
            error="mismatch",
            certificate_hash=_HASH_A,
            candidate_set_hash=_HASH_B,
        )


def test_uniform_batch_optimality_result_reject_has_no_accepted_artifacts() -> None:
    with pytest.raises(ValueError, match="include an error"):
        UniformBatchOptimalityVerificationResult(ok=False, error=None)

    with pytest.raises(ValueError, match="accepted artifacts"):
        UniformBatchOptimalityVerificationResult(
            ok=False,
            error="mismatch",
            certificate_hash=_HASH_A,
        )

    with pytest.raises(ValueError, match="accepted artifacts"):
        UniformBatchOptimalityVerificationResult(
            ok=False,
            error="mismatch",
            candidate_set_hash=_HASH_B,
            table_root=_HASH_C,
        )


def test_uniform_batch_optimality_result_accepts_optional_table_root() -> None:
    result = UniformBatchOptimalityVerificationResult(
        ok=True,
        error=None,
        certificate_hash=_HASH_A,
        candidate_set_hash=_HASH_B,
        table_root=_HASH_C,
    )

    assert result.table_root == _HASH_C


def _balances() -> BalanceTable:
    balances = BalanceTable()
    balances.set("alice", "A", 1_000)
    balances.set("alice", "B", 0)
    balances.set("bob", "A", 0)
    balances.set("bob", "B", 1_000)
    return balances


def _exact_out_intent(
    label: str,
    sender: str,
    asset_in: str,
    asset_out: str,
    *,
    amount_out: int = 100,
    max_amount_in: int = 100,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id="0x" + label.encode("utf-8").hex().ljust(64, "0")[:64],
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


def _exact_out_intents(*, max_amount_in: int = 100) -> list[Intent]:
    return [
        _exact_out_intent(
            "alice-a-to-b",
            "alice",
            "A",
            "B",
            max_amount_in=max_amount_in,
        ),
        _exact_out_intent(
            "bob-b-to-a",
            "bob",
            "B",
            "A",
            max_amount_in=max_amount_in,
        ),
    ]


def _exact_in_intent(
    label: str,
    sender: str,
    asset_in: str,
    asset_out: str,
    *,
    amount_in: int = 100,
    min_amount_out: int = 0,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + label.encode("utf-8").hex().ljust(64, "0")[:64],
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


def _exact_in_intents() -> list[Intent]:
    return [
        _exact_in_intent("alice-in-a-to-b", "alice", "A", "B"),
        _exact_in_intent("bob-in-b-to-a", "bob", "B", "A"),
    ]


def _exact_out_direction(intent: Intent, pool: PoolState) -> str:
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return "base_to_quote"
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return "quote_to_base"
    raise AssertionError("test intent direction does not match pool")


def _independent_exact_out_grid_certificate(
    *,
    intents: tuple[Intent, ...],
    pool: PoolState,
    price_num: int,
    price_den: int,
) -> UniformBatchCertificateV1:
    fills: list[UniformBatchFillV1] = []
    for intent in sorted(intents, key=lambda item: item.intent_id):
        assert intent.kind == IntentKind.SWAP_EXACT_OUT
        amount_out = int(intent.get_field("amount_out"))
        fills.append(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=uniform_batch_exact_out_gross_in_for_price(
                    amount_out=amount_out,
                    direction=_exact_out_direction(intent, pool),
                    price_num=price_num,
                    price_den=price_den,
                    fee_bps=pool.fee_bps,
                ),
                executed_out=amount_out,
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
        policy_id=UNIFORM_BATCH_POLICY_V3_ID,
        schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
    )


def _independent_exact_out_audit_tuple(
    certificate: UniformBatchCertificateV1,
    *,
    intents_by_id: dict[str, Intent],
) -> tuple[str, int, int, tuple[tuple[str, int, int], ...]]:
    volume = 0
    surplus = 0
    for fill in certificate.fills:
        intent = intents_by_id[fill.intent_id]
        volume += fill.executed_out
        surplus += int(intent.get_field("max_amount_in")) - fill.executed_in
    return (
        uniform_batch_candidate_id_for_certificate(certificate),
        volume,
        surplus,
        tuple((fill.intent_id, fill.executed_in, fill.executed_out) for fill in certificate.fills),
    )


def _full_fill_plan_projection(
    certificate: UniformBatchCertificateV1,
) -> tuple[tuple[str, int], ...]:
    return tuple((fill.intent_id, fill.executed_out) for fill in certificate.fills)


def _v2_fill_vector(executed_in: int) -> tuple[UniformBatchFillV1, ...]:
    return tuple(
        sorted(
            (
                UniformBatchFillV1(
                    intent_id=_exact_in_intents()[0].intent_id,
                    executed_in=executed_in,
                    executed_out=executed_in,
                ),
                UniformBatchFillV1(
                    intent_id=_exact_in_intents()[1].intent_id,
                    executed_in=executed_in,
                    executed_out=executed_in,
                ),
            ),
            key=lambda fill: fill.intent_id,
        )
    )


def _sorted_candidates(
    candidates: list[UniformBatchAuditCandidateV1],
) -> tuple[UniformBatchAuditCandidateV1, ...]:
    return tuple(sorted(candidates, key=lambda candidate: candidate.candidate_id))


def test_uniform_batch_optimality_certificate_accepts_weak_winner() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
        _candidate("c", volume=100, surplus=35),
    )
    certificate = _certificate(
        candidates,
        winner_id="b",
        volume_upper=100,
        surplus_upper=40,
    )

    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is True
    assert result.error is None
    assert result.certificate_hash == certificate.hash()
    assert result.certificate_hash == uniform_batch_optimality_certificate_hash(certificate)


def test_build_uniform_batch_optimality_certificate_selects_canonical_winner() -> None:
    candidates = (
        _candidate("c", volume=100, surplus=41),
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=41),
    )

    certificate = build_uniform_batch_optimality_certificate_v1(candidates)
    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is True
    assert certificate.winner_id == "b"
    assert certificate.volume_upper == 100
    assert certificate.surplus_upper_at_winner_volume == 41
    assert [candidate.candidate_id for candidate in certificate.candidates] == ["a", "b", "c"]
    assert certificate.candidate_set_hash == uniform_batch_optimality_candidate_set_hash(
        certificate.candidates
    )


def test_build_uniform_batch_optimality_certificate_rejects_empty_candidate_set() -> None:
    with pytest.raises(ValueError, match="requires at least one candidate"):
        build_uniform_batch_optimality_certificate_v1(())


def test_uniform_batch_optimality_certificate_is_audited_set_scoped() -> None:
    winner = _candidate("winner", volume=100, surplus=40)
    omitted_better = _candidate("omitted-better", volume=101, surplus=0)
    scoped_certificate = _certificate(
        (winner,),
        winner_id="winner",
        volume_upper=100,
        surplus_upper=40,
    )

    scoped_result = verify_uniform_batch_optimality_certificate_v1(scoped_certificate)

    assert scoped_result.ok is True

    expanded_certificate = _certificate(
        _sorted_candidates([winner, omitted_better]),
        winner_id="winner",
        volume_upper=100,
        surplus_upper=40,
    )

    expanded_result = verify_uniform_batch_optimality_certificate_v1(expanded_certificate)

    assert expanded_result.ok is False
    assert expanded_result.error == "audited candidate exceeds volume upper bound"


def test_uniform_batch_optimality_certificate_rejects_candidate_with_more_volume() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
        _candidate("c", volume=101, surplus=0),
    )
    certificate = _certificate(
        candidates,
        winner_id="b",
        volume_upper=100,
        surplus_upper=40,
    )

    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is False
    assert result.error == "audited candidate exceeds volume upper bound"


def test_uniform_batch_optimality_certificate_rejects_equal_volume_higher_surplus() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
        _candidate("c", volume=100, surplus=41),
    )
    certificate = _certificate(
        candidates,
        winner_id="b",
        volume_upper=100,
        surplus_upper=40,
    )

    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is False
    assert result.error == "audited candidate exceeds surplus upper bound at winner volume"


def test_uniform_batch_optimality_certificate_rejects_missing_winner() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
    )
    certificate = _certificate(
        candidates,
        winner_id="z",
        volume_upper=100,
        surplus_upper=40,
    )

    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is False
    assert result.error == "optimality certificate winner_id must reference exactly one candidate"


def test_uniform_batch_optimality_certificate_rejects_winner_volume_mismatch() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
    )
    certificate = _certificate(
        candidates,
        winner_id="b",
        volume_upper=101,
        surplus_upper=40,
    )

    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is False
    assert result.error == "optimality certificate winner volume does not match volume_upper"


def test_uniform_batch_optimality_certificate_rejects_winner_surplus_mismatch() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
    )
    certificate = _certificate(
        candidates,
        winner_id="b",
        volume_upper=100,
        surplus_upper=41,
    )

    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is False
    assert result.error == "optimality certificate winner surplus does not match surplus upper bound"


def test_uniform_batch_optimality_certificate_rejects_candidate_set_hash_mismatch() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
    )
    certificate_obj = _certificate(
        candidates,
        winner_id="b",
        volume_upper=100,
        surplus_upper=40,
    ).to_dict()
    certificate_obj["candidate_set_hash"] = "different"

    result = verify_uniform_batch_optimality_certificate_v1(certificate_obj)

    assert result.ok is False
    assert result.error == "optimality certificate candidate_set_hash mismatch"


def test_uniform_batch_optimality_certificate_rejects_unsorted_candidates() -> None:
    candidates = (
        _candidate("b", volume=100, surplus=40),
        _candidate("a", volume=90, surplus=1_000),
    )
    certificate = UniformBatchOptimalityCertificateV1(
        candidate_set_hash=uniform_batch_optimality_candidate_set_hash(candidates),
        winner_id="b",
        volume_upper=100,
        surplus_upper_at_winner_volume=40,
        candidates=candidates,
    )

    result = verify_uniform_batch_optimality_certificate_v1(certificate)

    assert result.ok is False
    assert result.error == "optimality candidates must be sorted by candidate_id"


def test_uniform_batch_optimality_candidate_set_hash_is_order_invariant() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
        _candidate("c", volume=100, surplus=35),
    )

    assert uniform_batch_optimality_candidate_set_hash(candidates) == uniform_batch_optimality_candidate_set_hash(
        tuple(reversed(candidates))
    )


def test_uniform_batch_optimality_certificate_rejects_closed_schema_violation() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
    )
    certificate_obj = _certificate(
        candidates,
        winner_id="b",
        volume_upper=100,
        surplus_upper=40,
    ).to_dict()
    certificate_obj["unexpected"] = True

    result = verify_uniform_batch_optimality_certificate_v1(certificate_obj)

    assert result.ok is False
    assert result.error == "optimality.certificate contains unknown keys: unexpected"


def test_uniform_batch_optimality_certificate_rejects_bool_score() -> None:
    candidates = (
        _candidate("a", volume=90, surplus=1_000),
        _candidate("b", volume=100, surplus=40),
    )
    certificate_obj = _certificate(
        candidates,
        winner_id="b",
        volume_upper=100,
        surplus_upper=40,
    ).to_dict()
    certificate_obj["candidates"][1]["volume"] = True

    result = verify_uniform_batch_optimality_certificate_v1(certificate_obj)

    assert result.ok is False
    assert result.error == "candidate.volume must be an integer"


def test_uniform_batch_candidate_id_for_certificate_is_hash_bound() -> None:
    certificate = _uniform_certificate()
    candidate_id = uniform_batch_candidate_id_for_certificate(certificate)

    assert candidate_id == uniform_batch_candidate_id_for_certificate_hash(certificate.hash())
    assert candidate_id != uniform_batch_candidate_id_for_certificate(_uniform_certificate("other"))


def test_uniform_batch_candidate_id_for_certificate_hash_rejects_malformed_hash() -> None:
    try:
        uniform_batch_candidate_id_for_certificate_hash("not-a-hash")
    except ValueError as exc:
        assert str(exc) == "uniform_batch_certificate_hash must be 0x-prefixed lowercase sha256 hex"
    else:
        raise AssertionError("expected malformed certificate hash rejection")


def test_uniform_batch_bound_optimality_certificate_accepts_matching_winner() -> None:
    uniform_certificate = _uniform_certificate()
    winner_id = uniform_batch_candidate_id_for_certificate(uniform_certificate)
    candidates = _sorted_candidates(
        [
            _candidate("other", volume=90, surplus=1_000),
            _candidate(winner_id, volume=100, surplus=40),
        ]
    )
    certificate = _certificate(
        candidates,
        winner_id=winner_id,
        volume_upper=100,
        surplus_upper=40,
    )

    result = verify_uniform_batch_bound_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=uniform_certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.certificate_hash == certificate.hash()


def test_uniform_batch_bound_optimality_certificate_accepts_v2_partial_fill_winner() -> None:
    uniform_certificate = _uniform_v2_partial_certificate()
    winner_id = uniform_batch_candidate_id_for_certificate(uniform_certificate)
    candidates = _sorted_candidates(
        [
            _candidate("lower-volume-partial-plan", volume=40, surplus=1_000),
            _candidate(winner_id, volume=60, surplus=25),
        ]
    )
    certificate = _certificate(
        candidates,
        winner_id=winner_id,
        volume_upper=60,
        surplus_upper=25,
    )

    result = verify_uniform_batch_bound_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=uniform_certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.certificate_hash == certificate.hash()


def test_uniform_batch_fill_vector_hash_is_canonical_by_intent_id() -> None:
    uniform_certificate = _uniform_v2_partial_certificate()

    assert uniform_batch_fill_vector_hash(uniform_certificate.fills) == uniform_batch_fill_vector_hash(
        tuple(reversed(uniform_certificate.fills))
    )


def test_uniform_batch_v2_bounded_grid_fill_vector_domain_is_canonical_by_intent_id() -> None:
    intents = _exact_in_intents()
    sorted_fill_vectors = (_v2_fill_vector(40), _v2_fill_vector(100))
    unsorted_fill_vectors = tuple(tuple(reversed(fill_vector)) for fill_vector in sorted_fill_vectors)

    sorted_scored = build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=sorted_fill_vectors,
    )
    unsorted_scored = build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=unsorted_fill_vectors,
    )

    assert [item.audit_candidate.to_dict() for item in sorted_scored] == [
        item.audit_candidate.to_dict() for item in unsorted_scored
    ]
    assert [item.certificate.hash() for item in sorted_scored] == [
        item.certificate.hash() for item in unsorted_scored
    ]

    sorted_rows = build_uniform_batch_v2_bounded_grid_optimality_table_v1(sorted_scored)
    unsorted_rows = build_uniform_batch_v2_bounded_grid_optimality_table_v1(unsorted_scored)
    assert uniform_batch_v2_bounded_grid_optimality_table_root(
        sorted_rows
    ) == uniform_batch_v2_bounded_grid_optimality_table_root(unsorted_rows)


def test_uniform_batch_v2_bounded_grid_rejects_fill_vector_missing_admitted_intent() -> None:
    with pytest.raises(ValueError, match="v2 partial-fill vector must cover every admitted intent"):
        build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
            intents=_exact_in_intents(),
            pool=_pool(),
            balances=_balances(),
            max_price_num=1,
            max_price_den=1,
            fill_vectors=(_v2_fill_vector(40)[:-1],),
        )


def test_uniform_batch_v2_bounded_grid_candidates_build_table_root() -> None:
    intents = _exact_in_intents()
    scored_candidates = build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=(_v2_fill_vector(40), _v2_fill_vector(100)),
    )

    assert len(scored_candidates) == 2
    assert {item.certificate.policy_id for item in scored_candidates} == {UNIFORM_BATCH_POLICY_V2_ID}
    assert {item.certificate.schema for item in scored_candidates} == {UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2}
    assert {item.audit_candidate.volume for item in scored_candidates} == {80, 200}
    assert all(item.audit_candidate.fill_vector_hash is not None for item in scored_candidates)

    rows = build_uniform_batch_v2_bounded_grid_optimality_table_v1(scored_candidates)
    table_root = uniform_batch_v2_bounded_grid_optimality_table_root(rows)

    assert table_root == uniform_batch_v2_bounded_grid_optimality_table_root(tuple(reversed(rows)))

    certificate = build_uniform_batch_optimality_certificate_v1(
        tuple(item.audit_candidate for item in scored_candidates)
    )
    winner = max(
        scored_candidates,
        key=lambda item: (item.audit_candidate.volume, item.audit_candidate.surplus),
    )

    result = verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=winner.certificate,
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=(_v2_fill_vector(40), _v2_fill_vector(100)),
        expected_table_root=table_root,
    )

    assert result.ok is True
    assert result.error is None
    assert result.table_root == table_root
    assert result.candidate_set_hash == certificate.candidate_set_hash


def test_uniform_batch_v2_bounded_grid_rejects_omitted_better_candidate() -> None:
    intents = _exact_in_intents()
    scored_candidates = build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=(_v2_fill_vector(40), _v2_fill_vector(100)),
    )
    lower = min(scored_candidates, key=lambda item: item.audit_candidate.volume)
    scoped_certificate = build_uniform_batch_optimality_certificate_v1((lower.audit_candidate,))

    finite_result = verify_uniform_batch_bound_optimality_certificate_v1(
        optimality_certificate=scoped_certificate,
        uniform_batch_certificate=lower.certificate,
    )
    complete_result = verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1(
        optimality_certificate=scoped_certificate,
        uniform_batch_certificate=lower.certificate,
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=(_v2_fill_vector(40), _v2_fill_vector(100)),
    )

    assert finite_result.ok is True
    assert complete_result.ok is False
    assert complete_result.error == "v2 bounded-grid candidate_set_hash mismatch"


def test_uniform_batch_v2_bounded_grid_rejects_table_root_mismatch() -> None:
    intents = _exact_in_intents()
    scored_candidates = build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=(_v2_fill_vector(40),),
    )
    certificate = build_uniform_batch_optimality_certificate_v1(
        tuple(item.audit_candidate for item in scored_candidates)
    )

    result = verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=scored_candidates[0].certificate,
        intents=intents,
        pool=_pool(),
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
        fill_vectors=(_v2_fill_vector(40),),
        expected_table_root="0x" + "0" * 64,
    )

    assert result.ok is False
    assert result.error == "v2 bounded-grid table_root mismatch"


def test_uniform_batch_bound_optimality_rejects_winner_fill_vector_mismatch() -> None:
    uniform_certificate = _uniform_v2_partial_certificate()
    winner_id = uniform_batch_candidate_id_for_certificate(uniform_certificate)
    bad_fill_vector_hash = uniform_batch_fill_vector_hash(
        (
            UniformBatchFillV1(
                intent_id="intent-winner-a",
                executed_in=1,
                executed_out=1,
            ),
        )
    )
    candidates = (
        UniformBatchAuditCandidateV1(
            candidate_id=winner_id,
            volume=60,
            surplus=25,
            fill_vector_hash=bad_fill_vector_hash,
        ),
    )
    certificate = _certificate(
        candidates,
        winner_id=winner_id,
        volume_upper=60,
        surplus_upper=25,
    )

    result = verify_uniform_batch_bound_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=uniform_certificate,
    )

    assert result.ok is False
    assert result.error == "optimality winner fill_vector_hash does not match uniform batch certificate"


def test_uniform_batch_exact_out_grid_candidates_enumerate_v3_winner() -> None:
    pool = _pool()
    intents = _exact_out_intents()

    candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )

    assert len(candidates) == 1
    scored = candidates[0]
    assert scored.certificate.policy_id == UNIFORM_BATCH_POLICY_V3_ID
    assert scored.certificate.schema == UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3
    assert scored.audit_candidate.candidate_id == uniform_batch_candidate_id_for_certificate(scored.certificate)
    assert scored.audit_candidate.volume == 200
    assert scored.audit_candidate.surplus == 0


def test_uniform_batch_exact_out_grid_candidates_accept_high_fee_boundary() -> None:
    pool = _pool()
    pool.fee_bps = 9_999
    balances = BalanceTable()
    balances.set("alice", "A", 10_000)
    balances.set("bob", "B", 10_000)
    intents = [
        _exact_out_intent(
            "alice-high-fee-a-to-b",
            "alice",
            "A",
            "B",
            amount_out=1,
            max_amount_in=10_000,
        ),
        _exact_out_intent(
            "bob-high-fee-b-to-a",
            "bob",
            "B",
            "A",
            amount_out=1,
            max_amount_in=10_000,
        ),
    ]

    candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        max_price_num=1,
        max_price_den=1,
    )

    assert len(candidates) == 1
    fills_by_id = {fill.intent_id: fill for fill in candidates[0].certificate.fills}
    assert [fills_by_id[intent.intent_id].executed_in for intent in intents] == [10_000, 10_000]
    assert [fills_by_id[intent.intent_id].executed_out for intent in intents] == [1, 1]
    assert candidates[0].audit_candidate.volume == 2
    assert candidates[0].audit_candidate.surplus == 0


def test_uniform_batch_exact_out_grid_candidates_feed_optimality_certificate() -> None:
    pool = _pool()
    intents = _exact_out_intents(max_amount_in=110)
    scored_candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )
    candidates = tuple(item.audit_candidate for item in scored_candidates)
    certificate = build_uniform_batch_optimality_certificate_v1(candidates)

    result = verify_uniform_batch_bound_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=scored_candidates[0].certificate,
    )

    assert result.ok is True
    assert result.error is None


def test_uniform_batch_exact_out_grid_complete_domain_verifier_accepts_full_fill_certificate() -> None:
    pool = _pool()
    intents = _exact_out_intents(max_amount_in=110)
    scored_candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )
    optimality_certificate = build_uniform_batch_optimality_certificate_v1(
        tuple(item.audit_candidate for item in scored_candidates)
    )

    result = verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1(
        optimality_certificate=optimality_certificate,
        uniform_batch_certificate=scored_candidates[0].certificate,
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )

    assert result.ok is True
    assert result.error is None
    assert result.candidate_set_hash == optimality_certificate.candidate_set_hash


def test_uniform_batch_exact_out_grid_complete_domain_verifier_rejects_candidate_set_hash_mismatch() -> None:
    pool = _pool()
    intents = _exact_out_intents(max_amount_in=110)
    scored_candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )
    optimality_certificate = build_uniform_batch_optimality_certificate_v1(
        tuple(item.audit_candidate for item in scored_candidates)
    )
    certificate_obj = optimality_certificate.to_dict()
    certificate_obj["candidate_set_hash"] = "different"

    result = verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1(
        optimality_certificate=certificate_obj,
        uniform_batch_certificate=scored_candidates[0].certificate,
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )

    assert result.ok is False
    assert result.error == "v3 exact-out grid candidate_set_hash mismatch"


def test_uniform_batch_exact_out_grid_complete_domain_verifier_rejects_non_v3_winner() -> None:
    pool = _pool()
    intents = _exact_out_intents(max_amount_in=110)
    scored_candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )
    optimality_certificate = build_uniform_batch_optimality_certificate_v1(
        tuple(item.audit_candidate for item in scored_candidates)
    )
    wrong_certificate = _uniform_v2_partial_certificate()

    result = verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1(
        optimality_certificate=optimality_certificate,
        uniform_batch_certificate=wrong_certificate,
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=1,
        max_price_den=1,
    )

    assert result.ok is False
    assert result.error == "v3 exact-out grid verifier requires v3 uniform batch certificate"


def test_uniform_batch_exact_out_grid_candidates_filter_noncanonical_prices() -> None:
    pool = _pool()
    intents = _exact_out_intents(max_amount_in=500)

    candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=_balances(),
        max_price_num=2,
        max_price_den=2,
    )

    assert len(candidates) == 1
    assert candidates[0].certificate.price_num == 1
    assert candidates[0].certificate.price_den == 1


def test_uniform_batch_exact_out_grid_candidates_match_independent_reduced_grid_replay() -> None:
    pool = _pool()
    intents = tuple(_exact_out_intents(max_amount_in=1_000))
    intents_by_id = {intent.intent_id: intent for intent in intents}
    balances = _balances()

    helper_candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        max_price_num=3,
        max_price_den=3,
    )
    helper_replay = {
        _independent_exact_out_audit_tuple(
            scored.certificate,
            intents_by_id=intents_by_id,
        )
        for scored in helper_candidates
    }

    independent_replay = set()
    for price_num in range(1, 4):
        for price_den in range(1, 4):
            if gcd(price_num, price_den) != 1:
                continue
            certificate = _independent_exact_out_grid_certificate(
                intents=intents,
                pool=pool,
                price_num=price_num,
                price_den=price_den,
            )
            result = verify_uniform_batch_certificate_v1(
                intents=intents,
                pool=pool,
                balances=balances,
                certificate=certificate,
            )
            if result.ok:
                independent_replay.add(
                    _independent_exact_out_audit_tuple(
                        certificate,
                        intents_by_id=intents_by_id,
                    )
                )

    assert helper_replay == independent_replay
    assert helper_replay
    expected_full_fill_plan = tuple(
        sorted((intent.intent_id, int(intent.get_field("amount_out"))) for intent in intents)
    )
    helper_full_fill_plans = {
        _full_fill_plan_projection(scored.certificate)
        for scored in helper_candidates
    }
    independent_full_fill_plans = {
        _full_fill_plan_projection(
            _independent_exact_out_grid_certificate(
                intents=intents,
                pool=pool,
                price_num=price_num,
                price_den=price_den,
            )
        )
        for price_num in range(1, 4)
        for price_den in range(1, 4)
        if gcd(price_num, price_den) == 1
    }
    assert helper_full_fill_plans == {expected_full_fill_plan}
    assert independent_full_fill_plans == {expected_full_fill_plan}
    for scored in helper_candidates:
        assert scored.certificate.policy_id == UNIFORM_BATCH_POLICY_V3_ID
        assert scored.certificate.schema == UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3
        assert tuple(fill.intent_id for fill in scored.certificate.fills) == tuple(
            sorted(intent.intent_id for intent in intents)
        )
        for fill in scored.certificate.fills:
            assert fill.executed_out == int(intents_by_id[fill.intent_id].get_field("amount_out"))


def test_uniform_batch_exact_out_grid_candidates_reject_mixed_intent_kinds() -> None:
    with pytest.raises(ValueError, match="exact-out grid candidates require SWAP_EXACT_OUT intents"):
        build_uniform_batch_exact_out_grid_audit_candidates_v1(
            intents=(_exact_out_intents()[0], _exact_in_intents()[0]),
            pool=_pool(),
            balances=_balances(),
            max_price_num=1,
            max_price_den=1,
        )


def test_uniform_batch_exact_out_grid_candidates_reject_large_grid() -> None:
    with pytest.raises(ValueError, match="price grid exceeds optimality candidate limit"):
        build_uniform_batch_exact_out_grid_audit_candidates_v1(
            intents=_exact_out_intents(),
            pool=_pool(),
            balances=_balances(),
            max_price_num=17,
            max_price_den=17,
        )


def test_uniform_batch_bound_optimality_certificate_rejects_mismatched_uniform_certificate() -> None:
    winner_certificate = _uniform_certificate("winner")
    other_certificate = _uniform_certificate("other")
    winner_id = uniform_batch_candidate_id_for_certificate(winner_certificate)
    candidates = _sorted_candidates(
        [
            _candidate("other", volume=90, surplus=1_000),
            _candidate(winner_id, volume=100, surplus=40),
        ]
    )
    certificate = _certificate(
        candidates,
        winner_id=winner_id,
        volume_upper=100,
        surplus_upper=40,
    )

    result = verify_uniform_batch_bound_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=other_certificate,
    )

    assert result.ok is False
    assert result.error == "optimality certificate winner_id does not match uniform batch certificate"


def test_uniform_batch_bound_optimality_certificate_rejects_invalid_uniform_certificate() -> None:
    uniform_certificate = _uniform_certificate().to_dict()
    uniform_certificate["price_num"] = 0
    certificate = _certificate(
        (_candidate("winner", volume=100, surplus=40),),
        winner_id="winner",
        volume_upper=100,
        surplus_upper=40,
    )

    result = verify_uniform_batch_bound_optimality_certificate_v1(
        optimality_certificate=certificate,
        uniform_batch_certificate=uniform_certificate,
    )

    assert result.ok is False
    assert result.error == "certificate.price_num must be positive"
