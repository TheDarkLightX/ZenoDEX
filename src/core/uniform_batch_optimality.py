"""Finite audit-set optimality certificate verifier for UPBA.

This module verifies a small certificate shape that matches the starter Lean
optimality boundary in `Proofs/UniformBatchOptimality.lean`.

The checker does not construct a UPBA settlement. It only verifies that, inside
an explicitly supplied finite candidate audit set, the declared winner is weakly
optimal by volume first and surplus second.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .uniform_batch_clearing import UNIFORM_BATCH_MAX_FILLS, UNIFORM_BATCH_OUTPUT_AMOUNT_MAX

UNIFORM_BATCH_OPTIMALITY_CERTIFICATE_SCHEMA = "zenodex/uniform_batch_optimality_certificate/v1"
UNIFORM_BATCH_OPTIMALITY_CANDIDATE_SET_SCHEMA = "zenodex/uniform_batch_optimality_candidate_set/v1"
UNIFORM_BATCH_OPTIMALITY_OBJECTIVE_ID = "zenodex/upba/lexicographic_volume_then_surplus/audit_set_v1"
UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES = UNIFORM_BATCH_MAX_FILLS
UNIFORM_BATCH_OPTIMALITY_SCORE_MAX = UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * UNIFORM_BATCH_MAX_FILLS

_OPTIMALITY_CANDIDATE_KEYS = frozenset({"candidate_id", "volume", "surplus"})
_OPTIMALITY_CERTIFICATE_KEYS = frozenset(
    {
        "schema",
        "objective_id",
        "candidate_set_hash",
        "winner_id",
        "volume_upper",
        "surplus_upper_at_winner_volume",
        "candidates",
    }
)


@dataclass(frozen=True)
class UniformBatchAuditCandidateV1:
    candidate_id: str
    volume: int
    surplus: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_id": self.candidate_id,
            "volume": int(self.volume),
            "surplus": int(self.surplus),
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchAuditCandidateV1":
        _reject_unknown_keys(obj, allowed=_OPTIMALITY_CANDIDATE_KEYS, name="optimality.candidate")
        return cls(
            candidate_id=_require_str(obj.get("candidate_id"), name="candidate.candidate_id"),
            volume=_require_nonnegative_int(
                obj.get("volume"),
                name="candidate.volume",
                maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
            ),
            surplus=_require_nonnegative_int(
                obj.get("surplus"),
                name="candidate.surplus",
                maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
            ),
        )


@dataclass(frozen=True)
class UniformBatchOptimalityCertificateV1:
    candidate_set_hash: str
    winner_id: str
    volume_upper: int
    surplus_upper_at_winner_volume: int
    candidates: tuple[UniformBatchAuditCandidateV1, ...]
    objective_id: str = UNIFORM_BATCH_OPTIMALITY_OBJECTIVE_ID
    schema: str = UNIFORM_BATCH_OPTIMALITY_CERTIFICATE_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "objective_id": self.objective_id,
            "candidate_set_hash": self.candidate_set_hash,
            "winner_id": self.winner_id,
            "volume_upper": int(self.volume_upper),
            "surplus_upper_at_winner_volume": int(self.surplus_upper_at_winner_volume),
            "candidates": [candidate.to_dict() for candidate in self.candidates],
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchOptimalityCertificateV1":
        _reject_unknown_keys(obj, allowed=_OPTIMALITY_CERTIFICATE_KEYS, name="optimality.certificate")
        schema = _require_str(obj.get("schema"), name="certificate.schema")
        if schema != UNIFORM_BATCH_OPTIMALITY_CERTIFICATE_SCHEMA:
            raise ValueError("unsupported uniform batch optimality certificate schema")
        objective_id = _require_str(obj.get("objective_id"), name="certificate.objective_id")
        if objective_id != UNIFORM_BATCH_OPTIMALITY_OBJECTIVE_ID:
            raise ValueError("unsupported uniform batch optimality objective_id")
        candidates_obj = obj.get("candidates")
        if not isinstance(candidates_obj, Sequence) or isinstance(candidates_obj, (str, bytes, bytearray)):
            raise TypeError("certificate.candidates must be a sequence")
        if len(candidates_obj) > UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES:
            raise ValueError(
                f"certificate.candidates exceeds maximum length {UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES}"
            )
        return cls(
            candidate_set_hash=_require_str(
                obj.get("candidate_set_hash"),
                name="certificate.candidate_set_hash",
            ),
            winner_id=_require_str(obj.get("winner_id"), name="certificate.winner_id"),
            volume_upper=_require_nonnegative_int(
                obj.get("volume_upper"),
                name="certificate.volume_upper",
                maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
            ),
            surplus_upper_at_winner_volume=_require_nonnegative_int(
                obj.get("surplus_upper_at_winner_volume"),
                name="certificate.surplus_upper_at_winner_volume",
                maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
            ),
            candidates=tuple(
                UniformBatchAuditCandidateV1.from_obj(
                    _require_mapping(candidate, name="certificate.candidate")
                )
                for candidate in candidates_obj
            ),
            objective_id=objective_id,
            schema=schema,
        )

    def hash(self) -> str:
        return uniform_batch_optimality_certificate_hash(self)


@dataclass(frozen=True)
class UniformBatchOptimalityVerificationResult:
    ok: bool
    error: str | None
    certificate_hash: str | None = None


def uniform_batch_optimality_candidate_set_hash(
    candidates: Sequence[UniformBatchAuditCandidateV1 | Mapping[str, Any]],
) -> str:
    parsed = tuple(
        candidate
        if isinstance(candidate, UniformBatchAuditCandidateV1)
        else UniformBatchAuditCandidateV1.from_obj(_require_mapping(candidate, name="candidate"))
        for candidate in candidates
    )
    if len(parsed) > UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES:
        raise ValueError(f"candidate set exceeds maximum length {UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES}")
    _validate_candidate_tuple(parsed, require_sorted=False)
    body = {
        "schema": UNIFORM_BATCH_OPTIMALITY_CANDIDATE_SET_SCHEMA,
        "objective_id": UNIFORM_BATCH_OPTIMALITY_OBJECTIVE_ID,
        "candidates": [candidate.to_dict() for candidate in sorted(parsed, key=lambda item: item.candidate_id)],
    }
    return sha256_hex(
        domain_sep_bytes("uniform_batch_optimality_candidate_set", version=1)
        + canonical_json_bytes(body)
    )


def uniform_batch_optimality_certificate_hash(
    certificate: UniformBatchOptimalityCertificateV1 | Mapping[str, Any],
) -> str:
    parsed = (
        certificate
        if isinstance(certificate, UniformBatchOptimalityCertificateV1)
        else UniformBatchOptimalityCertificateV1.from_obj(
            _require_mapping(certificate, name="optimality.certificate")
        )
    )
    _validate_optimality_certificate_shape(parsed)
    return sha256_hex(
        domain_sep_bytes("uniform_batch_optimality_certificate", version=1)
        + canonical_json_bytes(parsed.to_dict())
    )


def verify_uniform_batch_optimality_certificate_v1(
    certificate: UniformBatchOptimalityCertificateV1 | Mapping[str, Any],
) -> UniformBatchOptimalityVerificationResult:
    try:
        parsed = (
            certificate
            if isinstance(certificate, UniformBatchOptimalityCertificateV1)
            else UniformBatchOptimalityCertificateV1.from_obj(
                _require_mapping(certificate, name="optimality.certificate")
            )
        )
        _validate_optimality_certificate_shape(parsed)
        expected_candidate_set_hash = uniform_batch_optimality_candidate_set_hash(parsed.candidates)
        if parsed.candidate_set_hash != expected_candidate_set_hash:
            raise ValueError("optimality certificate candidate_set_hash mismatch")
        winners = [candidate for candidate in parsed.candidates if candidate.candidate_id == parsed.winner_id]
        if len(winners) != 1:
            raise ValueError("optimality certificate winner_id must reference exactly one candidate")
        winner = winners[0]
        if winner.volume != parsed.volume_upper:
            raise ValueError("optimality certificate winner volume does not match volume_upper")
        if winner.surplus != parsed.surplus_upper_at_winner_volume:
            raise ValueError("optimality certificate winner surplus does not match surplus upper bound")
        for candidate in parsed.candidates:
            if candidate.volume > parsed.volume_upper:
                raise ValueError("audited candidate exceeds volume upper bound")
            if (
                candidate.volume == parsed.volume_upper
                and candidate.surplus > parsed.surplus_upper_at_winner_volume
            ):
                raise ValueError("audited candidate exceeds surplus upper bound at winner volume")
        return UniformBatchOptimalityVerificationResult(
            ok=True,
            error=None,
            certificate_hash=parsed.hash(),
        )
    except (TypeError, ValueError) as exc:
        return UniformBatchOptimalityVerificationResult(ok=False, error=str(exc))


def _validate_optimality_certificate_shape(certificate: UniformBatchOptimalityCertificateV1) -> None:
    if certificate.schema != UNIFORM_BATCH_OPTIMALITY_CERTIFICATE_SCHEMA:
        raise ValueError("unsupported uniform batch optimality certificate schema")
    if certificate.objective_id != UNIFORM_BATCH_OPTIMALITY_OBJECTIVE_ID:
        raise ValueError("unsupported uniform batch optimality objective_id")
    _require_str(certificate.candidate_set_hash, name="certificate.candidate_set_hash")
    _require_str(certificate.winner_id, name="certificate.winner_id")
    _require_nonnegative_int(
        certificate.volume_upper,
        name="certificate.volume_upper",
        maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
    )
    _require_nonnegative_int(
        certificate.surplus_upper_at_winner_volume,
        name="certificate.surplus_upper_at_winner_volume",
        maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
    )
    if not isinstance(certificate.candidates, tuple):
        raise TypeError("certificate.candidates must be a tuple")
    if not certificate.candidates:
        raise ValueError("optimality certificate requires at least one candidate")
    if len(certificate.candidates) > UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES:
        raise ValueError(f"certificate.candidates exceeds maximum length {UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES}")
    _validate_candidate_tuple(certificate.candidates, require_sorted=True)


def _validate_candidate_tuple(
    candidates: tuple[UniformBatchAuditCandidateV1, ...],
    *,
    require_sorted: bool,
) -> None:
    ids: list[str] = []
    for candidate in candidates:
        if not isinstance(candidate, UniformBatchAuditCandidateV1):
            raise TypeError("certificate.candidates must contain UniformBatchAuditCandidateV1 values")
        _require_str(candidate.candidate_id, name="candidate.candidate_id")
        _require_nonnegative_int(
            candidate.volume,
            name="candidate.volume",
            maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
        )
        _require_nonnegative_int(
            candidate.surplus,
            name="candidate.surplus",
            maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
        )
        ids.append(candidate.candidate_id)
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate optimality candidate_id")
    if require_sorted and ids != sorted(ids):
        raise ValueError("optimality candidates must be sorted by candidate_id")


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise TypeError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an integer")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} exceeds maximum {maximum}")
    return int(value)


def _reject_unknown_keys(obj: Mapping[str, Any], *, allowed: frozenset[str], name: str) -> None:
    unknown = sorted(set(obj) - set(allowed))
    if unknown:
        joined = ", ".join(unknown)
        raise ValueError(f"{name} contains unknown keys: {joined}")
