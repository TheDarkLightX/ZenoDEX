"""Focused E07 transport-loss tests."""

from __future__ import annotations

from experiments.fcis_m6_e07_transport_loss import run_campaign


def test_every_loss_point_resolves_through_fresh_lookup() -> None:
    observations = run_campaign()

    assert tuple(item.loss_point.value for item in observations) == (
        "before_request_reaches_server",
        "after_validation_before_transaction",
        "after_transaction_commit_before_response",
        "after_response_generation_during_transport",
    )
    assert tuple(item.fresh_durable_outcome.value for item in observations) == (
        "absent_retryable",
        "absent_retryable",
        "already_committed",
        "already_committed",
    )
    assert all(item.client_knowledge.value == "indeterminate" for item in observations)
    assert observations[0].blind_retry_result == "COMMITTED"
    assert observations[1].blind_retry_result == "COMMITTED"
    assert observations[2].blind_retry_result == "stale_snapshot_cas"
    assert observations[3].blind_retry_result == "stale_snapshot_cas"
    assert all(
        (item.publication_count, item.nullifier_count, item.effect_count) == (1, 1, 1)
        for item in observations
    )


def test_transport_campaign_is_repeatable() -> None:
    first = tuple(item.to_wire() for item in run_campaign())
    second = tuple(item.to_wire() for item in run_campaign())

    assert first == second
