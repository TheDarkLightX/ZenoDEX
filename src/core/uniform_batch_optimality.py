"""Finite audit-set optimality certificate verifier for UPBA.

This module verifies a small certificate shape that matches the starter Lean
optimality boundary in `Proofs/UniformBatchOptimality.lean`.

The checker does not construct a UPBA settlement. It only verifies that, inside
an explicitly supplied finite candidate audit set, the declared winner is weakly
optimal by volume first and surplus second.

The v2 bounded-grid helpers below build the concrete finite audit set from
accepted partial-fill certificate candidates. That gives runtime code a
deterministic table root for the extra completeness premise used by the Lean v2
bounded-grid bridge.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Any, Mapping, Sequence

from ..state.balances import BalanceTable
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .domain_limits import DEX_SWAP_AMOUNT_MAX
from .uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3,
    UNIFORM_BATCH_MAX_FILLS,
    UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
    UNIFORM_BATCH_POLICY_V2_ID,
    UNIFORM_BATCH_POLICY_V3_ID,
    UNIFORM_BATCH_PRICE_RATIO_MAX,
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    uniform_batch_certificate_hash,
    uniform_batch_exact_out_gross_in_for_price,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
    verify_uniform_batch_certificate_v1,
)

UNIFORM_BATCH_OPTIMALITY_CERTIFICATE_SCHEMA = "zenodex/uniform_batch_optimality_certificate/v1"
UNIFORM_BATCH_OPTIMALITY_CANDIDATE_SET_SCHEMA = "zenodex/uniform_batch_optimality_candidate_set/v1"
UNIFORM_BATCH_OPTIMALITY_WINNER_BINDING_SCHEMA = "zenodex/uniform_batch_optimality_winner_binding/v1"
UNIFORM_BATCH_FILL_VECTOR_SCHEMA = "zenodex/uniform_batch_fill_vector/v1"
UNIFORM_BATCH_V2_BOUNDED_GRID_TABLE_SCHEMA = (
    "zenodex/uniform_batch_v2_bounded_grid_optimality_table/v1"
)
UNIFORM_BATCH_OPTIMALITY_OBJECTIVE_ID = "zenodex/upba/lexicographic_volume_then_surplus/audit_set_v1"
UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES = UNIFORM_BATCH_MAX_FILLS
UNIFORM_BATCH_OPTIMALITY_SCORE_MAX = UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * UNIFORM_BATCH_MAX_FILLS

_OPTIMALITY_CANDIDATE_KEYS = frozenset(
    {"candidate_id", "volume", "surplus", "fill_vector_hash"}
)
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
_V2_BOUNDED_GRID_TABLE_ROW_KEYS = frozenset(
    {"price_num", "price_den", "fill_vector_hash", "candidate"}
)


@dataclass(frozen=True)
class UniformBatchAuditCandidateV1:
    candidate_id: str
    volume: int
    surplus: int
    fill_vector_hash: str | None = None

    def to_dict(self) -> dict[str, Any]:
        body = {
            "candidate_id": self.candidate_id,
            "volume": int(self.volume),
            "surplus": int(self.surplus),
        }
        if self.fill_vector_hash is not None:
            body["fill_vector_hash"] = self.fill_vector_hash
        return body

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchAuditCandidateV1":
        _reject_unknown_keys(obj, allowed=_OPTIMALITY_CANDIDATE_KEYS, name="optimality.candidate")
        fill_vector_hash_obj = obj.get("fill_vector_hash")
        fill_vector_hash = (
            None
            if fill_vector_hash_obj is None
            else _require_sha256_hex(fill_vector_hash_obj, name="candidate.fill_vector_hash")
        )
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
            fill_vector_hash=fill_vector_hash,
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
    candidate_set_hash: str | None = None
    table_root: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise ValueError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted optimality result cannot include error")
            try:
                _require_sha256_hex(self.certificate_hash, name="optimality.result.certificate_hash")
                _require_sha256_hex(self.candidate_set_hash, name="optimality.result.candidate_set_hash")
                if self.table_root is not None:
                    _require_sha256_hex(self.table_root, name="optimality.result.table_root")
            except (TypeError, ValueError) as exc:
                raise ValueError(str(exc)) from exc
            return

        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected optimality result must include an error")
        if self.certificate_hash is not None or self.candidate_set_hash is not None or self.table_root is not None:
            raise ValueError("rejected optimality result cannot include accepted artifacts")


@dataclass(frozen=True)
class UniformBatchScoredCertificateCandidateV1:
    certificate: UniformBatchCertificateV1
    audit_candidate: UniformBatchAuditCandidateV1


@dataclass(frozen=True)
class UniformBatchV2BoundedGridTableRowV1:
    price_num: int
    price_den: int
    fill_vector_hash: str
    candidate: UniformBatchAuditCandidateV1

    def to_dict(self) -> dict[str, Any]:
        return {
            "price_num": int(self.price_num),
            "price_den": int(self.price_den),
            "fill_vector_hash": self.fill_vector_hash,
            "candidate": self.candidate.to_dict(),
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchV2BoundedGridTableRowV1":
        _reject_unknown_keys(obj, allowed=_V2_BOUNDED_GRID_TABLE_ROW_KEYS, name="v2_bounded_grid.row")
        return cls(
            price_num=_require_positive_int(
                obj.get("price_num"),
                name="row.price_num",
                maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
            ),
            price_den=_require_positive_int(
                obj.get("price_den"),
                name="row.price_den",
                maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
            ),
            fill_vector_hash=_require_sha256_hex(
                obj.get("fill_vector_hash"),
                name="row.fill_vector_hash",
            ),
            candidate=UniformBatchAuditCandidateV1.from_obj(
                _require_mapping(obj.get("candidate"), name="row.candidate")
            ),
        )


def uniform_batch_fill_vector_hash(
    fills: Sequence[UniformBatchFillV1 | Mapping[str, Any]],
) -> str:
    parsed = _parse_fill_vector(fills, name="fill_vector")
    body = {
        "schema": UNIFORM_BATCH_FILL_VECTOR_SCHEMA,
        "fills": [fill.to_dict() for fill in parsed],
    }
    return sha256_hex(
        domain_sep_bytes("uniform_batch_fill_vector", version=1)
        + canonical_json_bytes(body)
    )


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


def build_uniform_batch_v2_bounded_grid_optimality_table_v1(
    scored_candidates: Sequence[UniformBatchScoredCertificateCandidateV1],
) -> tuple[UniformBatchV2BoundedGridTableRowV1, ...]:
    if len(scored_candidates) > UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES:
        raise ValueError(
            f"v2 bounded-grid table exceeds maximum length {UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES}"
        )
    rows: list[UniformBatchV2BoundedGridTableRowV1] = []
    for item in scored_candidates:
        if not isinstance(item, UniformBatchScoredCertificateCandidateV1):
            raise TypeError("scored_candidates must contain UniformBatchScoredCertificateCandidateV1 values")
        certificate = item.certificate
        if certificate.policy_id != UNIFORM_BATCH_POLICY_V2_ID:
            raise ValueError("v2 bounded-grid table requires v2 uniform batch certificates")
        if certificate.schema != UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2:
            raise ValueError("v2 bounded-grid table requires v2 uniform batch certificate schema")
        fill_vector_hash = uniform_batch_fill_vector_hash(certificate.fills)
        audit_candidate = item.audit_candidate
        if audit_candidate.fill_vector_hash is not None and audit_candidate.fill_vector_hash != fill_vector_hash:
            raise ValueError("audit candidate fill_vector_hash does not match certificate fills")
        candidate = UniformBatchAuditCandidateV1(
            candidate_id=audit_candidate.candidate_id,
            volume=audit_candidate.volume,
            surplus=audit_candidate.surplus,
            fill_vector_hash=fill_vector_hash,
        )
        rows.append(
            UniformBatchV2BoundedGridTableRowV1(
                price_num=certificate.price_num,
                price_den=certificate.price_den,
                fill_vector_hash=fill_vector_hash,
                candidate=candidate,
            )
        )
    rows.sort(key=_v2_bounded_grid_row_sort_key)
    _validate_v2_bounded_grid_rows(tuple(rows), require_sorted=True)
    return tuple(rows)


def uniform_batch_v2_bounded_grid_optimality_table_root(
    rows: Sequence[UniformBatchV2BoundedGridTableRowV1 | Mapping[str, Any]],
) -> str:
    parsed = tuple(
        row
        if isinstance(row, UniformBatchV2BoundedGridTableRowV1)
        else UniformBatchV2BoundedGridTableRowV1.from_obj(_require_mapping(row, name="v2_bounded_grid.row"))
        for row in rows
    )
    _validate_v2_bounded_grid_rows(parsed, require_sorted=False)
    sorted_rows = tuple(sorted(parsed, key=_v2_bounded_grid_row_sort_key))
    candidates = tuple(row.candidate for row in sorted_rows)
    body = {
        "schema": UNIFORM_BATCH_V2_BOUNDED_GRID_TABLE_SCHEMA,
        "objective_id": UNIFORM_BATCH_OPTIMALITY_OBJECTIVE_ID,
        "candidate_set_hash": uniform_batch_optimality_candidate_set_hash(candidates),
        "rows": [row.to_dict() for row in sorted_rows],
    }
    return sha256_hex(
        domain_sep_bytes("uniform_batch_v2_bounded_grid_optimality_table", version=1)
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


def build_uniform_batch_optimality_certificate_v1(
    candidates: Sequence[UniformBatchAuditCandidateV1 | Mapping[str, Any]],
) -> UniformBatchOptimalityCertificateV1:
    parsed = tuple(
        candidate
        if isinstance(candidate, UniformBatchAuditCandidateV1)
        else UniformBatchAuditCandidateV1.from_obj(_require_mapping(candidate, name="candidate"))
        for candidate in candidates
    )
    if not parsed:
        raise ValueError("optimality certificate requires at least one candidate")
    if len(parsed) > UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES:
        raise ValueError(f"candidate set exceeds maximum length {UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES}")
    _validate_candidate_tuple(parsed, require_sorted=False)
    sorted_candidates = tuple(sorted(parsed, key=lambda item: item.candidate_id))
    winner = sorted_candidates[0]
    for candidate in sorted_candidates[1:]:
        if candidate.volume > winner.volume or (
            candidate.volume == winner.volume and candidate.surplus > winner.surplus
        ):
            winner = candidate
    return UniformBatchOptimalityCertificateV1(
        candidate_set_hash=uniform_batch_optimality_candidate_set_hash(sorted_candidates),
        winner_id=winner.candidate_id,
        volume_upper=winner.volume,
        surplus_upper_at_winner_volume=winner.surplus,
        candidates=sorted_candidates,
    )


def uniform_batch_candidate_id_for_certificate(
    certificate: UniformBatchCertificateV1 | Mapping[str, Any],
) -> str:
    return uniform_batch_candidate_id_for_certificate_hash(uniform_batch_certificate_hash(certificate))


def uniform_batch_candidate_id_for_certificate_hash(certificate_hash: str) -> str:
    parsed_hash = _require_sha256_hex(certificate_hash, name="uniform_batch_certificate_hash")
    body = {
        "schema": UNIFORM_BATCH_OPTIMALITY_WINNER_BINDING_SCHEMA,
        "uniform_batch_certificate_hash": parsed_hash,
    }
    return sha256_hex(
        domain_sep_bytes("uniform_batch_optimality_winner_binding", version=1)
        + canonical_json_bytes(body)
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
            candidate_set_hash=expected_candidate_set_hash,
        )
    except (TypeError, ValueError) as exc:
        return UniformBatchOptimalityVerificationResult(ok=False, error=str(exc))


def verify_uniform_batch_bound_optimality_certificate_v1(
    *,
    optimality_certificate: UniformBatchOptimalityCertificateV1 | Mapping[str, Any],
    uniform_batch_certificate: UniformBatchCertificateV1 | Mapping[str, Any],
) -> UniformBatchOptimalityVerificationResult:
    try:
        parsed = (
            optimality_certificate
            if isinstance(optimality_certificate, UniformBatchOptimalityCertificateV1)
            else UniformBatchOptimalityCertificateV1.from_obj(
                _require_mapping(optimality_certificate, name="optimality.certificate")
            )
        )
        uniform_certificate = (
            uniform_batch_certificate
            if isinstance(uniform_batch_certificate, UniformBatchCertificateV1)
            else UniformBatchCertificateV1.from_obj(
                _require_mapping(uniform_batch_certificate, name="uniform_batch_certificate")
            )
        )
        expected_winner_id = uniform_batch_candidate_id_for_certificate(uniform_certificate)
        if parsed.winner_id != expected_winner_id:
            raise ValueError("optimality certificate winner_id does not match uniform batch certificate")
        winners = [candidate for candidate in parsed.candidates if candidate.candidate_id == parsed.winner_id]
        if len(winners) == 1 and winners[0].fill_vector_hash is not None:
            expected_fill_vector_hash = uniform_batch_fill_vector_hash(uniform_certificate.fills)
            if winners[0].fill_vector_hash != expected_fill_vector_hash:
                raise ValueError(
                    "optimality winner fill_vector_hash does not match uniform batch certificate"
                )
        return verify_uniform_batch_optimality_certificate_v1(parsed)
    except (TypeError, ValueError) as exc:
        return UniformBatchOptimalityVerificationResult(ok=False, error=str(exc))


def verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1(
    *,
    optimality_certificate: UniformBatchOptimalityCertificateV1 | Mapping[str, Any],
    uniform_batch_certificate: UniformBatchCertificateV1 | Mapping[str, Any],
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    max_price_num: int,
    max_price_den: int,
    fill_vectors: Sequence[Sequence[UniformBatchFillV1 | Mapping[str, Any]]],
    expected_table_root: str | None = None,
) -> UniformBatchOptimalityVerificationResult:
    try:
        scored_candidates = build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            max_price_num=max_price_num,
            max_price_den=max_price_den,
            fill_vectors=fill_vectors,
        )
        if not scored_candidates:
            raise ValueError("v2 bounded-grid audit set has no accepted candidates")
        rows = build_uniform_batch_v2_bounded_grid_optimality_table_v1(scored_candidates)
        table_root = uniform_batch_v2_bounded_grid_optimality_table_root(rows)
        if expected_table_root is not None and expected_table_root != table_root:
            raise ValueError("v2 bounded-grid table_root mismatch")
        expected_candidates = tuple(row.candidate for row in rows)
        expected_candidate_set_hash = uniform_batch_optimality_candidate_set_hash(expected_candidates)
        parsed = (
            optimality_certificate
            if isinstance(optimality_certificate, UniformBatchOptimalityCertificateV1)
            else UniformBatchOptimalityCertificateV1.from_obj(
                _require_mapping(optimality_certificate, name="optimality.certificate")
            )
        )
        if parsed.candidate_set_hash != expected_candidate_set_hash:
            raise ValueError("v2 bounded-grid candidate_set_hash mismatch")
        result = verify_uniform_batch_bound_optimality_certificate_v1(
            optimality_certificate=parsed,
            uniform_batch_certificate=uniform_batch_certificate,
        )
        if not result.ok:
            return result
        return UniformBatchOptimalityVerificationResult(
            ok=True,
            error=None,
            certificate_hash=result.certificate_hash,
            candidate_set_hash=expected_candidate_set_hash,
            table_root=table_root,
        )
    except (TypeError, ValueError) as exc:
        return UniformBatchOptimalityVerificationResult(ok=False, error=str(exc))


def verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1(
    *,
    optimality_certificate: UniformBatchOptimalityCertificateV1 | Mapping[str, Any],
    uniform_batch_certificate: UniformBatchCertificateV1 | Mapping[str, Any],
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    max_price_num: int,
    max_price_den: int,
) -> UniformBatchOptimalityVerificationResult:
    try:
        scored_candidates = build_uniform_batch_exact_out_grid_audit_candidates_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            max_price_num=max_price_num,
            max_price_den=max_price_den,
        )
        if not scored_candidates:
            raise ValueError("v3 exact-out grid audit set has no accepted candidates")
        expected_candidates = tuple(item.audit_candidate for item in scored_candidates)
        expected_candidate_set_hash = uniform_batch_optimality_candidate_set_hash(expected_candidates)
        parsed = (
            optimality_certificate
            if isinstance(optimality_certificate, UniformBatchOptimalityCertificateV1)
            else UniformBatchOptimalityCertificateV1.from_obj(
                _require_mapping(optimality_certificate, name="optimality.certificate")
            )
        )
        if parsed.candidate_set_hash != expected_candidate_set_hash:
            raise ValueError("v3 exact-out grid candidate_set_hash mismatch")
        uniform_certificate = (
            uniform_batch_certificate
            if isinstance(uniform_batch_certificate, UniformBatchCertificateV1)
            else UniformBatchCertificateV1.from_obj(
                _require_mapping(uniform_batch_certificate, name="uniform_batch_certificate")
            )
        )
        if uniform_certificate.policy_id != UNIFORM_BATCH_POLICY_V3_ID:
            raise ValueError("v3 exact-out grid verifier requires v3 uniform batch certificate")
        if uniform_certificate.schema != UNIFORM_BATCH_CERTIFICATE_SCHEMA_V3:
            raise ValueError("v3 exact-out grid verifier requires v3 uniform batch certificate schema")
        winner_result = verify_uniform_batch_certificate_v1(
            intents=tuple(intents),
            pool=pool,
            balances=balances,
            certificate=uniform_certificate,
        )
        if not winner_result.ok:
            raise ValueError(f"v3 exact-out winner certificate rejected: {winner_result.error}")
        result = verify_uniform_batch_bound_optimality_certificate_v1(
            optimality_certificate=parsed,
            uniform_batch_certificate=uniform_certificate,
        )
        if not result.ok:
            return result
        return UniformBatchOptimalityVerificationResult(
            ok=True,
            error=None,
            certificate_hash=result.certificate_hash,
            candidate_set_hash=expected_candidate_set_hash,
        )
    except (TypeError, ValueError) as exc:
        return UniformBatchOptimalityVerificationResult(ok=False, error=str(exc))


def build_uniform_batch_v2_bounded_grid_audit_candidates_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    max_price_num: int,
    max_price_den: int,
    fill_vectors: Sequence[Sequence[UniformBatchFillV1 | Mapping[str, Any]]],
) -> tuple[UniformBatchScoredCertificateCandidateV1, ...]:
    """Enumerate accepted v2 partial-fill candidates over a reduced integer price grid."""

    max_num = _require_positive_int(
        max_price_num,
        name="max_price_num",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    max_den = _require_positive_int(
        max_price_den,
        name="max_price_den",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    parsed_fill_vectors = tuple(
        _parse_fill_vector(fill_vector, name="fill_vector")
        for fill_vector in fill_vectors
    )
    if not parsed_fill_vectors:
        raise ValueError("v2 bounded-grid enumeration requires at least one fill vector")
    max_price_pairs = UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES // len(parsed_fill_vectors)
    price_pairs = _reduced_price_pairs_with_limit(
        max_num=max_num,
        max_den=max_den,
        max_pairs=max_price_pairs,
        error="v2 bounded-grid candidate domain exceeds optimality candidate limit",
    )
    parsed_intents = tuple(intents)
    if not parsed_intents:
        raise ValueError("v2 bounded-grid candidate enumeration requires at least one intent")
    intents_by_id = {intent.intent_id: intent for intent in parsed_intents}
    if len(intents_by_id) != len(parsed_intents):
        raise ValueError("duplicate intent_id")
    for intent in parsed_intents:
        if intent.kind != IntentKind.SWAP_EXACT_IN:
            raise ValueError("v2 bounded-grid candidates require SWAP_EXACT_IN intents")
    expected_fill_ids = sorted(intents_by_id)
    for fill_vector in parsed_fill_vectors:
        fill_ids = [fill.intent_id for fill in fill_vector]
        if fill_ids != expected_fill_ids:
            raise ValueError("v2 partial-fill vector must cover every admitted intent")

    candidates: list[UniformBatchScoredCertificateCandidateV1] = []
    seen_candidate_ids: set[str] = set()
    for price_num, price_den in price_pairs:
        for fill_vector in parsed_fill_vectors:
            certificate = UniformBatchCertificateV1(
                pool_id=pool.pool_id,
                base_asset=pool.asset0,
                quote_asset=pool.asset1,
                pool_state_hash=uniform_batch_pool_state_hash(pool),
                intent_set_hash=uniform_batch_intent_set_hash(parsed_intents),
                price_num=price_num,
                price_den=price_den,
                fills=fill_vector,
                policy_id=UNIFORM_BATCH_POLICY_V2_ID,
                schema=UNIFORM_BATCH_CERTIFICATE_SCHEMA_V2,
            )
            result = verify_uniform_batch_certificate_v1(
                intents=parsed_intents,
                pool=pool,
                balances=balances,
                certificate=certificate,
            )
            if not result.ok:
                continue
            audit_candidate = _audit_candidate_for_uniform_batch_certificate(
                certificate,
                intents_by_id=intents_by_id,
                include_fill_vector_hash=True,
            )
            if audit_candidate.candidate_id in seen_candidate_ids:
                raise ValueError("duplicate accepted v2 bounded-grid candidate_id")
            seen_candidate_ids.add(audit_candidate.candidate_id)
            candidates.append(
                UniformBatchScoredCertificateCandidateV1(
                    certificate=certificate,
                    audit_candidate=audit_candidate,
                )
            )
    candidates.sort(key=lambda item: item.audit_candidate.candidate_id)
    return tuple(candidates)


def build_uniform_batch_exact_out_grid_audit_candidates_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    max_price_num: int,
    max_price_den: int,
) -> tuple[UniformBatchScoredCertificateCandidateV1, ...]:
    """Enumerate accepted v3 exact-out candidates over a reduced integer price grid."""

    max_num = _require_positive_int(
        max_price_num,
        name="max_price_num",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    max_den = _require_positive_int(
        max_price_den,
        name="max_price_den",
        maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
    )
    price_pairs = _reduced_price_pairs_with_limit(
        max_num=max_num,
        max_den=max_den,
        max_pairs=UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES,
        error="exact-out price grid exceeds optimality candidate limit",
    )
    parsed_intents = tuple(intents)
    if not parsed_intents:
        raise ValueError("exact-out candidate enumeration requires at least one intent")
    intents_by_id = {intent.intent_id: intent for intent in parsed_intents}
    if len(intents_by_id) != len(parsed_intents):
        raise ValueError("duplicate intent_id")
    candidates: list[UniformBatchScoredCertificateCandidateV1] = []
    for price_num, price_den in price_pairs:
        certificate = _build_uniform_batch_exact_out_certificate_for_price_v1(
            intents=parsed_intents,
            pool=pool,
            price_num=price_num,
            price_den=price_den,
        )
        result = verify_uniform_batch_certificate_v1(
            intents=parsed_intents,
            pool=pool,
            balances=balances,
            certificate=certificate,
        )
        if not result.ok:
            continue
        candidates.append(
            UniformBatchScoredCertificateCandidateV1(
                certificate=certificate,
                audit_candidate=_audit_candidate_for_uniform_batch_certificate(
                    certificate,
                    intents_by_id=intents_by_id,
                ),
            )
        )
    candidates.sort(key=lambda item: item.audit_candidate.candidate_id)
    return tuple(candidates)


def _reduced_price_pairs_with_limit(
    *,
    max_num: int,
    max_den: int,
    max_pairs: int,
    error: str,
) -> tuple[tuple[int, int], ...]:
    if max_pairs <= 0:
        raise ValueError(error)
    pairs: list[tuple[int, int]] = []
    for price_num in range(1, max_num + 1):
        for price_den in range(1, max_den + 1):
            if gcd(price_num, price_den) != 1:
                continue
            pairs.append((price_num, price_den))
            if len(pairs) > max_pairs:
                raise ValueError(error)
    return tuple(pairs)


def _build_uniform_batch_exact_out_certificate_for_price_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    price_num: int,
    price_den: int,
) -> UniformBatchCertificateV1:
    fills: list[UniformBatchFillV1] = []
    for intent in sorted(intents, key=lambda item: item.intent_id):
        if intent.kind != IntentKind.SWAP_EXACT_OUT:
            raise ValueError("exact-out grid candidates require SWAP_EXACT_OUT intents")
        amount_out = _require_positive_int(
            intent.get_field("amount_out"),
            name="intent.amount_out",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        direction = _uniform_batch_intent_direction(intent=intent, pool=pool)
        executed_in = uniform_batch_exact_out_gross_in_for_price(
            amount_out=amount_out,
            direction=direction,
            price_num=price_num,
            price_den=price_den,
            fee_bps=pool.fee_bps,
        )
        fills.append(
            UniformBatchFillV1(
                intent_id=intent.intent_id,
                executed_in=executed_in,
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


def _audit_candidate_for_uniform_batch_certificate(
    certificate: UniformBatchCertificateV1,
    *,
    intents_by_id: Mapping[str, Intent],
    include_fill_vector_hash: bool = False,
) -> UniformBatchAuditCandidateV1:
    volume = 0
    surplus = 0
    for fill in certificate.fills:
        intent = intents_by_id.get(fill.intent_id)
        if intent is None:
            raise ValueError("certificate fill references unknown intent_id")
        volume += fill.executed_out
        if intent.kind == IntentKind.SWAP_EXACT_OUT:
            max_amount_in = _require_nonnegative_int(
                intent.get_field("max_amount_in"),
                name="intent.max_amount_in",
                maximum=DEX_SWAP_AMOUNT_MAX,
            )
            if fill.executed_in > max_amount_in:
                raise ValueError("certificate fill exceeds intent max_amount_in")
            surplus += max_amount_in - fill.executed_in
            continue
        if intent.kind != IntentKind.SWAP_EXACT_IN:
            raise ValueError("unsupported intent kind for uniform batch audit scoring")
        amount_in = _require_positive_int(
            intent.get_field("amount_in"),
            name="intent.amount_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        min_amount_out = _require_nonnegative_int(
            intent.get_field("min_amount_out"),
            name="intent.min_amount_out",
            maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
        )
        if fill.executed_in > amount_in:
            raise ValueError("certificate fill exceeds intent amount_in")
        required_min_out = _ceil_div(min_amount_out * fill.executed_in, amount_in)
        if fill.executed_out < required_min_out:
            raise ValueError("certificate fill violates intent limit price")
        surplus += fill.executed_out - required_min_out
    _require_nonnegative_int(
        volume,
        name="candidate.volume",
        maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
    )
    _require_nonnegative_int(
        surplus,
        name="candidate.surplus",
        maximum=UNIFORM_BATCH_OPTIMALITY_SCORE_MAX,
    )
    return UniformBatchAuditCandidateV1(
        candidate_id=uniform_batch_candidate_id_for_certificate(certificate),
        volume=volume,
        surplus=surplus,
        fill_vector_hash=(
            uniform_batch_fill_vector_hash(certificate.fills)
            if include_fill_vector_hash
            else None
        ),
    )


def _uniform_batch_intent_direction(*, intent: Intent, pool: PoolState) -> str:
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return "base_to_quote"
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return "quote_to_base"
    raise ValueError("intent direction does not match pool assets")


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
        if candidate.fill_vector_hash is not None:
            _require_sha256_hex(candidate.fill_vector_hash, name="candidate.fill_vector_hash")
        ids.append(candidate.candidate_id)
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate optimality candidate_id")
    if require_sorted and ids != sorted(ids):
        raise ValueError("optimality candidates must be sorted by candidate_id")


def _validate_v2_bounded_grid_rows(
    rows: tuple[UniformBatchV2BoundedGridTableRowV1, ...],
    *,
    require_sorted: bool,
) -> None:
    if len(rows) > UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES:
        raise ValueError(
            f"v2 bounded-grid table exceeds maximum length {UNIFORM_BATCH_OPTIMALITY_MAX_CANDIDATES}"
        )
    row_keys: list[tuple[int, int, str, str]] = []
    candidate_ids: list[str] = []
    for row in rows:
        if not isinstance(row, UniformBatchV2BoundedGridTableRowV1):
            raise TypeError("v2 bounded-grid rows must contain UniformBatchV2BoundedGridTableRowV1 values")
        _require_positive_int(
            row.price_num,
            name="row.price_num",
            maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
        )
        _require_positive_int(
            row.price_den,
            name="row.price_den",
            maximum=UNIFORM_BATCH_PRICE_RATIO_MAX,
        )
        if gcd(int(row.price_num), int(row.price_den)) != 1:
            raise ValueError("v2 bounded-grid row price ratio must be reduced")
        _require_sha256_hex(row.fill_vector_hash, name="row.fill_vector_hash")
        if row.candidate.fill_vector_hash != row.fill_vector_hash:
            raise ValueError("v2 bounded-grid row candidate fill_vector_hash mismatch")
        _validate_candidate_tuple((row.candidate,), require_sorted=False)
        row_keys.append(_v2_bounded_grid_row_sort_key(row))
        candidate_ids.append(row.candidate.candidate_id)
    if len(candidate_ids) != len(set(candidate_ids)):
        raise ValueError("duplicate v2 bounded-grid candidate_id")
    if require_sorted and row_keys != sorted(row_keys):
        raise ValueError("v2 bounded-grid rows must be sorted")


def _v2_bounded_grid_row_sort_key(row: UniformBatchV2BoundedGridTableRowV1) -> tuple[int, int, str, str]:
    return (
        int(row.price_num),
        int(row.price_den),
        row.fill_vector_hash,
        row.candidate.candidate_id,
    )


def _parse_fill_vector(
    fills: Sequence[UniformBatchFillV1 | Mapping[str, Any]],
    *,
    name: str,
) -> tuple[UniformBatchFillV1, ...]:
    if not isinstance(fills, Sequence) or isinstance(fills, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    if len(fills) > UNIFORM_BATCH_MAX_FILLS:
        raise ValueError(f"{name} exceeds maximum length {UNIFORM_BATCH_MAX_FILLS}")
    parsed = tuple(
        fill
        if isinstance(fill, UniformBatchFillV1)
        else UniformBatchFillV1.from_obj(_require_mapping(fill, name=f"{name}.fill"))
        for fill in fills
    )
    ids: list[str] = []
    for fill in parsed:
        _require_str(fill.intent_id, name=f"{name}.fill.intent_id")
        _require_nonnegative_int(
            fill.executed_in,
            name=f"{name}.fill.executed_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        _require_nonnegative_int(
            fill.executed_out,
            name=f"{name}.fill.executed_out",
            maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
        )
        ids.append(fill.intent_id)
    if len(ids) != len(set(ids)):
        raise ValueError(f"duplicate {name} fill intent_id")
    return tuple(sorted(parsed, key=lambda fill: fill.intent_id))


def _ceil_div(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (int(numerator) + int(denominator) - 1) // int(denominator)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise TypeError(f"{name} must be a non-empty string")
    return value


def _require_sha256_hex(value: Any, *, name: str) -> str:
    parsed = _require_str(value, name=name)
    if (
        len(parsed) != 66
        or not parsed.startswith("0x")
        or any(char not in "0123456789abcdef" for char in parsed[2:])
    ):
        raise ValueError(f"{name} must be 0x-prefixed lowercase sha256 hex")
    return parsed


def _require_nonnegative_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an integer")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} exceeds maximum {maximum}")
    return int(value)


def _require_positive_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    value_int = _require_nonnegative_int(value, name=name, maximum=maximum)
    if value_int <= 0:
        raise ValueError(f"{name} must be positive")
    return value_int


def _reject_unknown_keys(obj: Mapping[str, Any], *, allowed: frozenset[str], name: str) -> None:
    unknown = sorted(set(obj) - set(allowed))
    if unknown:
        joined = ", ".join(unknown)
        raise ValueError(f"{name} contains unknown keys: {joined}")
