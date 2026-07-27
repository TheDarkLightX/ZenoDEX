from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    _derive_bundle_claim_v1,
    _derive_outbox_plan_v1,
    build_commit_bundle_v1,
    recompute_bundle_root_v1,
)
from src.core.fcis_commit_reference import (
    ReferenceCommitResultV1,
    ReferenceCommitStatusV1,
    ReferenceCommitStoreV1,
    ReferenceCrashPointV1,
    ReferencePublicationV1,
    _initial_reference_commit_store_v1,
    reference_commit_v1,
)
from src.core.fcis_decision_derivation import (
    AcceptV1,
    evaluate_fcis_decision_v1,
)
from src.state.fcis_committed_state_values import FCISCommittedStateV1
from src.state.fcis_execution_context_values import (
    FCISSettlementExecutionContextSourceV1,
    FCISStepExecutionContextSourceV1,
)
from src.state.owned_json import snapshot_owned_json_object
from tests.core.test_fcis_decision_derivation import _exact_inputs, _two_event_inputs


def _accept() -> AcceptV1:
    result = evaluate_fcis_decision_v1(**_exact_inputs())
    assert type(result) is AcceptV1
    return result


def _bundle() -> CommitBundleV1:
    bundle = build_commit_bundle_v1(_accept())
    assert type(bundle) is CommitBundleV1
    return bundle


def _bundle_at(now: int) -> CommitBundleV1:
    inputs = _exact_inputs()
    context = inputs["context"]
    assert type(context) is FCISStepExecutionContextSourceV1
    settlement_context = context.settlement
    assert type(settlement_context) is FCISSettlementExecutionContextSourceV1
    inputs["context"] = replace(
        context,
        settlement=replace(settlement_context, now=now),
    )
    decision = evaluate_fcis_decision_v1(**inputs)
    assert type(decision) is AcceptV1
    bundle = build_commit_bundle_v1(decision)
    assert type(bundle) is CommitBundleV1
    return bundle


def _two_event_bundle() -> CommitBundleV1:
    decision = evaluate_fcis_decision_v1(**_two_event_inputs())
    assert type(decision) is AcceptV1
    bundle = build_commit_bundle_v1(decision)
    assert type(bundle) is CommitBundleV1
    return bundle


def _store_from_pre_state() -> ReferenceCommitStoreV1:
    inputs = _exact_inputs()
    from src.core.fcis_step_evaluation_values import FCISStepEvaluationOkV1
    from src.core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1

    evaluation = evaluate_fcis_step_candidate_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )
    assert type(evaluation) is FCISStepEvaluationOkV1
    return _initial_reference_commit_store_v1(evaluation.material.pre_state)


def test_initial_store_has_empty_publications() -> None:
    store = _store_from_pre_state()

    assert store.publications == ()
    assert type(store.current_state) is FCISCommittedStateV1


def test_reference_commit_publishes_exact_bundle() -> None:
    """M5-P3-COMMIT-001: root match publishes one complete bundle."""
    store = _store_from_pre_state()
    bundle = _bundle()

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.PUBLISHED
    assert len(result.store.publications) == 1
    assert result.store.publications[0].bundle is bundle
    assert result.store.current_state == bundle.decision.next_state


def test_reference_commit_stale_returns_unchanged_store() -> None:
    """M5-P3-COMMIT-002: a stale root publishes nothing."""
    bundle = _bundle()
    wrong_state = _accept().next_state
    store = _initial_reference_commit_store_v1(wrong_state)

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.STALE
    assert result.store is store
    assert result.store.publications == ()


def test_reference_commit_duplicate_returns_already_committed() -> None:
    """M5-P3-COMMIT-006: retry is idempotent and preserves one publication."""
    store = _store_from_pre_state()
    bundle = _bundle()

    first = reference_commit_v1(store, bundle)
    assert first.status is ReferenceCommitStatusV1.PUBLISHED

    second = reference_commit_v1(first.store, bundle)

    assert second.status is ReferenceCommitStatusV1.ALREADY_COMMITTED
    assert second.store is first.store
    assert len(second.store.publications) == 1


def test_reference_commit_invalid_bundle_returns_unchanged_store() -> None:
    """M5-P3-COMMIT-003: an invalid bundle publishes nothing."""
    store = _store_from_pre_state()

    result = reference_commit_v1(store, object())

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is store


def test_reference_commit_rejects_non_exact_store_at_the_typed_edge() -> None:
    bundle = _bundle()
    with pytest.raises(TypeError, match="exact ReferenceCommitStoreV1"):
        reference_commit_v1(object(), bundle)  # type: ignore[arg-type]


def test_reference_commit_crash_before_linearization_returns_unchanged() -> None:
    """M5-P3-COMMIT-004: pre-linearization crash publishes nothing."""
    store = _store_from_pre_state()
    bundle = _bundle()

    result = reference_commit_v1(
        store,
        bundle,
        crash_point=ReferenceCrashPointV1.BEFORE_LINEARIZATION,
    )

    assert result.status is ReferenceCommitStatusV1.CRASHED_BEFORE_LINEARIZATION
    assert result.store is store
    assert result.store.publications == ()


def test_reference_commit_crash_after_linearization_returns_complete_store() -> None:
    """M5-P3-COMMIT-005: post-linearization crash exposes the whole publication."""
    store = _store_from_pre_state()
    bundle = _bundle()

    result = reference_commit_v1(
        store,
        bundle,
        crash_point=ReferenceCrashPointV1.AFTER_LINEARIZATION,
    )

    assert result.status is ReferenceCommitStatusV1.CRASHED_AFTER_LINEARIZATION
    assert len(result.store.publications) == 1
    assert result.store.publications[0].bundle is bundle
    assert result.store.current_state == bundle.decision.next_state


def test_reference_commit_is_deterministic() -> None:
    store = _store_from_pre_state()
    bundle = _bundle()

    first = reference_commit_v1(store, bundle)
    second = reference_commit_v1(store, bundle)

    assert first.status == second.status
    assert first.store == second.store


def test_exhaustive_bounded_commit_replay_and_retry_laws() -> None:
    """M5-P3-COMMIT-PROP-001: bounded contexts replay and retry identically."""

    for now in (700, 701, 702, 703):
        store = _store_from_pre_state()
        bundle = _bundle_at(now)
        first = reference_commit_v1(store, bundle)
        replay = reference_commit_v1(store, bundle)
        retry = reference_commit_v1(first.store, bundle)

        assert first.status is ReferenceCommitStatusV1.PUBLISHED
        assert replay == first
        assert retry.status is ReferenceCommitStatusV1.ALREADY_COMMITTED
        assert retry.store is first.store
        assert len(first.store.publications) == 1
        assert first.store.current_state == bundle.decision.next_state


def test_reference_commit_publication_retains_bundle() -> None:
    """M5-P3-COMMIT-010: committed outputs remain reachable as one lineage."""
    store = _store_from_pre_state()
    bundle = _bundle()

    result = reference_commit_v1(store, bundle)

    assert type(result.store.publications[0]) is ReferencePublicationV1
    assert result.store.publications[0].bundle is bundle


def test_reference_commit_result_has_exact_status_and_store() -> None:
    store = _store_from_pre_state()
    bundle = _bundle()

    result = reference_commit_v1(store, bundle)

    assert type(result) is ReferenceCommitResultV1
    assert type(result.status) is ReferenceCommitStatusV1
    assert type(result.store) is ReferenceCommitStoreV1


def test_initial_store_rejects_non_exact_state() -> None:
    with pytest.raises(TypeError, match="exact committed state"):
        _initial_reference_commit_store_v1(object())  # type: ignore[arg-type]


@pytest.mark.parametrize(
    "corrupt",
    (
        lambda bundle: object.__setattr__(bundle.decision.commit_plan, "patch", object()),
        lambda bundle: object.__setattr__(
            bundle.decision.receipt.binding,
            "snapshot_version",
            object(),
        ),
        lambda bundle: object.__setattr__(bundle.outbox_plan, "records", object()),
    ),
)
def test_exact_nested_corruption_returns_invalid_without_publication(corrupt) -> None:
    """M5-P3-BUNDLE-009: hostile nested corruption fails before publication."""

    store = _store_from_pre_state()
    bundle = _bundle()
    corrupt(bundle)

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is store
    assert result.store.publications == ()


@pytest.mark.parametrize(
    "component",
    ("decision", "state", "plan", "replay", "receipt", "outbox"),
)
def test_cross_lineage_component_substitution_returns_invalid(component: str) -> None:
    """M5-P3-BUNDLE-008: independently valid components cannot be swapped."""

    store = _store_from_pre_state()
    first = _bundle()
    second = _two_event_bundle()
    if component == "decision":
        object.__setattr__(first, "decision", second.decision)
    elif component == "state":
        assert first.decision.next_state != second.decision.next_state
        object.__setattr__(first.decision, "next_state", second.decision.next_state)
    elif component == "plan":
        assert first.decision.commit_plan != second.decision.commit_plan
        object.__setattr__(first.decision, "commit_plan", second.decision.commit_plan)
    elif component == "replay":
        assert first.decision.commit_plan.replay != second.decision.commit_plan.replay
        object.__setattr__(
            first.decision.commit_plan,
            "replay",
            second.decision.commit_plan.replay,
        )
    elif component == "receipt":
        object.__setattr__(first.decision, "receipt", second.decision.receipt)
    else:
        event = snapshot_owned_json_object({"kind": "substituted", "amount": 1})
        alternate_plan = _derive_outbox_plan_v1((event,), first.receipt_root)
        object.__setattr__(first, "outbox_plan", alternate_plan)

    result = reference_commit_v1(store, first)

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is store


@pytest.mark.parametrize("mutation", ("reorder", "delete", "duplicate", "payload"))
def test_event_plan_substitution_returns_invalid(mutation: str) -> None:
    """M5-P3-BUNDLE-008A: event sequence and payload remain receipt-bound."""

    store = _store_from_pre_state()
    bundle = _two_event_bundle()
    events = bundle.decision.commit_plan.effects.settlement.events
    assert events is not None
    assert len(events) == 2
    if mutation == "reorder":
        changed = (events[1], events[0])
    elif mutation == "delete":
        changed = (events[0],)
    elif mutation == "duplicate":
        changed = (events[0], events[0])
    else:
        changed = (
            snapshot_owned_json_object({"kind": "payload-substitution", "amount": 1}),
            events[1],
        )
    alternate = _derive_outbox_plan_v1(changed, bundle.receipt_root)
    assert alternate != bundle.outbox_plan
    object.__setattr__(bundle, "outbox_plan", alternate)

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is store


def test_corrupted_retry_with_prior_cached_root_fails_before_duplicate_detection() -> None:
    """M5-P3-COMMIT-006A: a cached prior root cannot bypass full revalidation."""

    store = _store_from_pre_state()
    published_bundle = _bundle()
    published = reference_commit_v1(store, published_bundle)
    assert published.status is ReferenceCommitStatusV1.PUBLISHED
    retry_bundle = _bundle()
    assert retry_bundle is not published_bundle
    assert retry_bundle.bundle_root == published_bundle.bundle_root
    object.__setattr__(retry_bundle.decision.commit_plan, "patch", object())

    result = reference_commit_v1(published.store, retry_bundle)

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is published.store
    assert len(result.store.publications) == 1


def test_expected_old_mismatch_returns_invalid_with_unchanged_store() -> None:
    """M5-P3-COMMIT-009: compare-and-replace mismatch publishes nothing."""

    store = _store_from_pre_state()
    bundle = _bundle()
    write = bundle.decision.commit_plan.patch.balance_writes[0]
    object.__setattr__(write, "expected_old", write.expected_old + 1)
    canonical_bytes, bundle_root = recompute_bundle_root_v1(bundle)
    object.__setattr__(bundle, "_canonical_bundle_bytes", canonical_bytes)
    object.__setattr__(bundle, "_bundle_root", bundle_root)

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is store


def test_replay_application_reproduces_successor_nonce_state() -> None:
    """M5-P3-COMMIT-008: replay updates reproduce the successor nonce state."""

    bundle = _bundle()
    result = reference_commit_v1(_store_from_pre_state(), bundle)

    assert result.status is ReferenceCommitStatusV1.PUBLISHED
    assert result.store.current_state.nonces == bundle.decision.next_state.nonces


def test_patch_application_reproduces_all_non_replay_state_fields() -> None:
    """M5-P3-COMMIT-007: the patch reproduces all non-replay state fields."""

    bundle = _bundle()
    result = reference_commit_v1(_store_from_pre_state(), bundle)

    assert result.status is ReferenceCommitStatusV1.PUBLISHED
    actual = result.store.current_state
    expected = bundle.decision.next_state
    assert (
        actual.balances,
        actual.pools,
        actual.lp_balances,
        actual.vault,
        actual.oracle,
        actual.fee_accumulator,
        actual.perps,
    ) == (
        expected.balances,
        expected.pools,
        expected.lp_balances,
        expected.vault,
        expected.oracle,
        expected.fee_accumulator,
        expected.perps,
    )


def test_corrupted_publication_store_fails_closed_before_duplicate_detection() -> None:
    store = _store_from_pre_state()
    bundle = _bundle()
    first = reference_commit_v1(store, bundle)
    assert first.status is ReferenceCommitStatusV1.PUBLISHED
    object.__setattr__(first.store.publications[0], "bundle", object())

    result = reference_commit_v1(first.store, _bundle())

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is first.store


def test_decoded_bundle_claim_has_no_commit_authority() -> None:
    store = _store_from_pre_state()
    bundle = _bundle()
    decoded_claim = _derive_bundle_claim_v1(bundle.decision, bundle.outbox_plan)

    result = reference_commit_v1(store, decoded_claim)  # type: ignore[arg-type]

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is store


def test_invalid_crash_point_is_rejected_at_the_typed_edge() -> None:
    with pytest.raises(TypeError, match="exact ReferenceCrashPointV1"):
        reference_commit_v1(
            _store_from_pre_state(),
            _bundle(),
            crash_point=object(),  # type: ignore[arg-type]
        )


def test_reference_value_constructors_reject_wrong_exact_types() -> None:
    bundle = _bundle()
    store = _store_from_pre_state()
    with pytest.raises(TypeError, match="exact CommitBundleV1"):
        ReferencePublicationV1(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact committed state"):
        ReferenceCommitStoreV1(object(), ())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact publication tuple"):
        ReferenceCommitStoreV1(store.current_state, [])  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact ReferenceCommitStatusV1"):
        ReferenceCommitResultV1(object(), store)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact ReferenceCommitStoreV1"):
        ReferenceCommitResultV1(ReferenceCommitStatusV1.INVALID, object())  # type: ignore[arg-type]
    assert type(bundle) is CommitBundleV1
