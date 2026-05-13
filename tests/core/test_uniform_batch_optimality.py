from __future__ import annotations

from src.core.uniform_batch_clearing import UniformBatchCertificateV1, UniformBatchFillV1
from src.core.uniform_batch_optimality import (
    UniformBatchAuditCandidateV1,
    UniformBatchOptimalityCertificateV1,
    uniform_batch_candidate_id_for_certificate,
    uniform_batch_candidate_id_for_certificate_hash,
    uniform_batch_optimality_candidate_set_hash,
    uniform_batch_optimality_certificate_hash,
    verify_uniform_batch_bound_optimality_certificate_v1,
    verify_uniform_batch_optimality_certificate_v1,
)


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
