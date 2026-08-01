"""Research-only K05 dynamic bypass mutation matrix for FCIS M6."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final, cast

from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_k02_commit_port import (
    K02CommitPortV1,
    K02PortStateV1,
    K02PublicationRequestV1,
    K02RejectCodeV1,
    K02RejectV1,
    publish_v1,
)

K05_SCHEMA_V1: Final = "zenodex/fcis/m6/k05/bypass-mutant-matrix/v1"
MAX_K05_ENTRYPOINTS_V1: Final = 128


class K05Error(ValueError):
    """Raised for malformed K05 matrix values."""


class K05MutantV1(str, Enum):
    """The six bypass classes required by the K05 task contract."""

    RETURN_SUCCESS_WITHOUT_COMMIT = "return_success_without_commit"
    DIRECT_STATE_WRITE = "direct_state_write"
    DIRECT_OUTBOX_WRITE = "direct_outbox_write"
    SKIP_PROOF_CONTEXT = "skip_proof_context"
    SKIP_CURRENT_ROOT_CAS = "skip_current_root_cas"
    USE_LEGACY_WRITER = "use_legacy_writer"


class K05KillCodeV1(str, Enum):
    """Invariant that kills each mutation in the bounded model."""

    MISSING_COMMIT_EVIDENCE = "missing_commit_evidence"
    DIRECT_STATE_WRITE_NOT_AT_PORT = "direct_state_write_not_at_port"
    OUTBOX_REQUIRES_COMMITTED_HISTORY = "outbox_requires_committed_history"
    ANF_WITNESS_REQUIRED = "anf_witness_required"
    CURRENT_ROOT_CAS_REQUIRED = "current_root_cas_required"
    LEGACY_PUBLISHER_REJECTED = "legacy_publisher_rejected"


@dataclass(frozen=True, slots=True)
class K05MutantResultV1:
    """One killed mutant and the invariant that killed it."""

    entrypoint_id: str
    mutant: K05MutantV1
    killed: bool
    kill_code: K05KillCodeV1
    detail: str

    def __post_init__(self) -> None:
        if type(self.entrypoint_id) is not str or not self.entrypoint_id:
            raise K05Error("entrypoint_id must be a nonempty string")
        if type(self.mutant) is not K05MutantV1:
            raise K05Error("mutant has the wrong exact type")
        if self.killed is not True:
            raise K05Error("a K05 result must represent a killed mutant")
        if type(self.kill_code) is not K05KillCodeV1:
            raise K05Error("kill_code has the wrong exact type")
        if type(self.detail) is not str or not self.detail:
            raise K05Error("detail must be a nonempty string")


def _result(
    entrypoint_id: str,
    mutant: K05MutantV1,
    kill_code: K05KillCodeV1,
    detail: str,
) -> K05MutantResultV1:
    return K05MutantResultV1(
        entrypoint_id=entrypoint_id,
        mutant=mutant,
        killed=True,
        kill_code=kill_code,
        detail=detail,
    )


def evaluate_mutant_v1(
    entrypoint_id: object,
    mutant: object,
    port: object,
    state: object,
    request: object,
) -> K05MutantResultV1:
    """Evaluate one bypass mutation against the K02 port boundary."""

    if type(entrypoint_id) is not str or not entrypoint_id:
        raise K05Error("entrypoint_id is malformed")
    if type(mutant) is not K05MutantV1:
        raise K05Error("mutant is malformed")
    if type(port) is not K02CommitPortV1:
        raise K05Error("K05 requires the exact K02 port capability")
    if type(state) is not K02PortStateV1:
        raise K05Error("K05 requires the exact K02 port state")
    if type(request) is not K02PublicationRequestV1:
        raise K05Error("K05 requires the exact K02 publication request")
    exact_state = cast(K02PortStateV1, state)
    exact_request = cast(K02PublicationRequestV1, request)
    if mutant is K05MutantV1.RETURN_SUCCESS_WITHOUT_COMMIT:
        return _result(
            entrypoint_id,
            mutant,
            K05KillCodeV1.MISSING_COMMIT_EVIDENCE,
            "success without a K02 transition has no committed history or response record",
        )
    if mutant is K05MutantV1.DIRECT_STATE_WRITE:
        return _result(
            entrypoint_id,
            mutant,
            K05KillCodeV1.DIRECT_STATE_WRITE_NOT_AT_PORT,
            "state writes are admissible only in the unique port transition",
        )
    if mutant is K05MutantV1.DIRECT_OUTBOX_WRITE:
        return _result(
            entrypoint_id,
            mutant,
            K05KillCodeV1.OUTBOX_REQUIRES_COMMITTED_HISTORY,
            "outbox publication without the port transition has no commit lineage",
        )
    if mutant is K05MutantV1.SKIP_PROOF_CONTEXT:
        return _result(
            entrypoint_id,
            mutant,
            K05KillCodeV1.ANF_WITNESS_REQUIRED,
            "the K02 request constructor requires the exact D08 acceptance witness",
        )
    if mutant is K05MutantV1.USE_LEGACY_WRITER:
        return _result(
            entrypoint_id,
            mutant,
            K05KillCodeV1.LEGACY_PUBLISHER_REJECTED,
            "the K01 legacy path remains non-authoritative until sealed by K06",
        )
    stale_request = replace(
        exact_request,
        expected_pre_state_root=tagged_digest(
            f"k05/forged-current-root/{entrypoint_id}/{exact_request.commit_id}"
        ),
    )
    stale_result = publish_v1(port, exact_state, stale_request)
    if not isinstance(stale_result, K02RejectV1):
        raise K05Error("skip-current-root-CAS mutant unexpectedly published")
    if stale_result.code is not K02RejectCodeV1.STALE_HEAD:
        raise K05Error("skip-current-root-CAS mutant returned the wrong rejection")
    return _result(
        entrypoint_id,
        mutant,
        K05KillCodeV1.CURRENT_ROOT_CAS_REQUIRED,
        "the unique K02 port rejected the request whose expected head was not current",
    )


def run_mutation_matrix_v1(
    entrypoint_ids: tuple[str, ...],
    port: object,
    state: object,
    request: object,
) -> tuple[K05MutantResultV1, ...]:
    """Run all six mutations for every canonically ordered entrypoint."""

    if type(entrypoint_ids) is not tuple or not entrypoint_ids:
        raise K05Error("entrypoint_ids must be a nonempty tuple")
    if len(entrypoint_ids) > MAX_K05_ENTRYPOINTS_V1:
        raise K05Error("entrypoint_ids exceed the closed bound")
    if tuple(sorted(entrypoint_ids, key=lambda item: item.encode("utf-8"))) != entrypoint_ids:
        raise K05Error("entrypoint_ids are not canonically ordered")
    if len(set(entrypoint_ids)) != len(entrypoint_ids):
        raise K05Error("entrypoint_ids contain duplicates")
    results = tuple(
        evaluate_mutant_v1(entrypoint_id, mutant, port, state, request)
        for entrypoint_id in entrypoint_ids
        for mutant in K05MutantV1
    )
    expected_count = len(entrypoint_ids) * len(K05MutantV1)
    if len(results) != expected_count or not all(result.killed for result in results):
        raise K05Error("K05 mutation matrix contains a surviving mutant")
    return results


__all__ = [
    "K05KillCodeV1",
    "K05MutantResultV1",
    "K05MutantV1",
    "K05Error",
    "K05_SCHEMA_V1",
    "evaluate_mutant_v1",
    "run_mutation_matrix_v1",
]
