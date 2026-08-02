"""E07 transport-loss model around the E05 publication and E04 lookup ports."""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

from experiments.fcis_m6_e04_retry_classifier import (
    build_attempt,
    build_reopen_receipt,
    build_state,
)
from experiments.fcis_m6_e05_expected_root_cas import (
    create_database,
    publish,
)
from src.core.fcis_m6_e04_retry_classifier import (
    E04ClientKnowledgeV1,
    E04DurableOutcomeV1,
    E04RetryResolutionV1,
    E04StoredStateV1,
    classify_e04_retry,
)
from src.core.fcis_m6_e05_expected_root_cas import (
    E05CommitReceiptV1,
    E05PublicationRequestV1,
    E05RejectV1,
)

MAX_E07_LOSS_POINTS_V1: Final = 4
E07ResultV1: TypeAlias = E05CommitReceiptV1 | E05RejectV1


class E07TransportLossPointV1(Enum):
    """Boundaries where a response or request can be lost."""

    BEFORE_REQUEST_REACHES_SERVER = "before_request_reaches_server"
    AFTER_VALIDATION_BEFORE_TRANSACTION = "after_validation_before_transaction"
    AFTER_TRANSACTION_COMMIT_BEFORE_RESPONSE = "after_transaction_commit_before_response"
    AFTER_RESPONSE_GENERATION_DURING_TRANSPORT = "after_response_generation_during_transport"


class E07TransportError(ValueError):
    """Raised when the transport-loss witness is malformed."""


@dataclass(frozen=True, slots=True)
class E07ObservationV1:
    """Fresh-lookup result for one transport loss point."""

    loss_point: E07TransportLossPointV1
    client_knowledge: E04ClientKnowledgeV1
    fresh_durable_outcome: E04DurableOutcomeV1
    first_server_result: str
    blind_retry_result: str
    publication_count: int
    nullifier_count: int
    effect_count: int

    def __post_init__(self) -> None:
        if type(self.loss_point) is not E07TransportLossPointV1:
            raise E07TransportError("loss point has the wrong exact type")
        if type(self.client_knowledge) is not E04ClientKnowledgeV1:
            raise E07TransportError("client knowledge has the wrong exact type")
        if type(self.fresh_durable_outcome) is not E04DurableOutcomeV1:
            raise E07TransportError("durable outcome has the wrong exact type")
        for name in ("first_server_result", "blind_retry_result"):
            value = getattr(self, name)
            if type(value) is not str or not value:
                raise E07TransportError(f"{name} must be a nonempty string")
        if any(
            type(value) is not int or value < 0
            for value in (self.publication_count, self.nullifier_count, self.effect_count)
        ):
            raise E07TransportError("row counts must be nonnegative integers")

    def to_wire(self) -> dict[str, object]:
        return {
            "loss_point": self.loss_point.value,
            "client_knowledge": self.client_knowledge.value,
            "fresh_durable_outcome": self.fresh_durable_outcome.value,
            "first_server_result": self.first_server_result,
            "blind_retry_result": self.blind_retry_result,
            "publication_count": self.publication_count,
            "nullifier_count": self.nullifier_count,
            "effect_count": self.effect_count,
        }


def _request() -> E05PublicationRequestV1:
    attempt = build_attempt()
    pre_state = build_state()
    post_state = build_state(
        attempts=((attempt, "6" * 64),),
        current_state_root="6" * 64,
    )
    return E05PublicationRequestV1(
        attempt=attempt,
        pre_state=pre_state,
        post_state=post_state,
        reopen_receipt=build_reopen_receipt(pre_state),
    )


def _fresh_lookup(
    request: E05PublicationRequestV1,
    state: E04StoredStateV1,
) -> E04RetryResolutionV1:
    result = classify_e04_retry(
        request.attempt,
        state,
        E04ClientKnowledgeV1.INDETERMINATE,
        build_reopen_receipt(
            state,
            freshness_epoch=2,
        ),
    )
    if type(result) is not E04RetryResolutionV1:
        raise E07TransportError(f"fresh lookup rejected its state subject: {result!r}")
    return result


def _count(connection: sqlite3.Connection, table: str) -> int:
    value = connection.execute(f"SELECT COUNT(*) FROM {table}").fetchone()
    if value is None:
        raise E07TransportError(f"row count missing for {table}")
    return int(value[0])


def simulate_loss(loss_point: E07TransportLossPointV1) -> E07ObservationV1:
    """Run one loss point and resolve it through a fresh E04 lookup."""

    if type(loss_point) is not E07TransportLossPointV1:
        raise E07TransportError("loss point has the wrong exact type")
    request = _request()
    connection = create_database(request.pre_state)
    first_server_result = "NO_REQUEST"
    blind_retry_result = "NOT_ATTEMPTED"

    if loss_point is E07TransportLossPointV1.BEFORE_REQUEST_REACHES_SERVER:
        pass
    elif loss_point is E07TransportLossPointV1.AFTER_VALIDATION_BEFORE_TRANSACTION:
        request.__post_init__()
        first_server_result = "VALIDATED_NO_TRANSACTION"
    else:
        committed = publish(connection, request)
        if type(committed) is not E05CommitReceiptV1:
            raise E07TransportError(f"valid request failed before simulated loss: {committed!r}")
        first_server_result = (
            "COMMITTED_RESPONSE_LOST"
            if loss_point is E07TransportLossPointV1.AFTER_TRANSACTION_COMMIT_BEFORE_RESPONSE
            else "RESPONSE_GENERATED_TRANSPORT_LOST"
        )

    if loss_point in (
        E07TransportLossPointV1.BEFORE_REQUEST_REACHES_SERVER,
        E07TransportLossPointV1.AFTER_VALIDATION_BEFORE_TRANSACTION,
    ):
        fresh = _fresh_lookup(request, request.pre_state)
        retried = publish(connection, request)
        if type(retried) is not E05CommitReceiptV1:
            raise E07TransportError(f"absent retry did not commit: {retried!r}")
        blind_retry_result = "COMMITTED"
    else:
        fresh = _fresh_lookup(request, request.post_state)
        blind_retry = publish(connection, request)
        if type(blind_retry) is not E05RejectV1:
            raise E07TransportError(f"blind retry unexpectedly committed: {blind_retry!r}")
        blind_retry_result = blind_retry.code.value

    return E07ObservationV1(
        loss_point=loss_point,
        client_knowledge=fresh.client_knowledge,
        fresh_durable_outcome=fresh.outcome,
        first_server_result=first_server_result,
        blind_retry_result=blind_retry_result,
        publication_count=_count(connection, "e05_publications"),
        nullifier_count=_count(connection, "e05_nullifiers"),
        effect_count=_count(connection, "e05_effects"),
    )


def run_campaign() -> tuple[E07ObservationV1, ...]:
    """Run all E07 loss points in enum order."""

    points = tuple(E07TransportLossPointV1)
    if len(points) != MAX_E07_LOSS_POINTS_V1:
        raise E07TransportError("loss-point manifest is incomplete")
    return tuple(simulate_loss(point) for point in points)


__all__ = (
    "E07ObservationV1",
    "E07TransportError",
    "E07TransportLossPointV1",
    "run_campaign",
    "simulate_loss",
)
