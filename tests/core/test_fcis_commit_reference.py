from __future__ import annotations

import pytest

from src.core.fcis_commit_bundle_derivation import build_commit_bundle_v1
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
from tests.core.test_fcis_decision_derivation import _exact_inputs


def _accept() -> AcceptV1:
    result = evaluate_fcis_decision_v1(**_exact_inputs())
    assert type(result) is AcceptV1
    return result


def _bundle() -> object:
    return build_commit_bundle_v1(_accept())


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
    store = _store_from_pre_state()
    bundle = _bundle()

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.PUBLISHED
    assert len(result.store.publications) == 1
    assert result.store.publications[0].bundle is bundle
    assert result.store.current_state == bundle.decision.next_state


def test_reference_commit_stale_returns_unchanged_store() -> None:
    bundle = _bundle()
    wrong_state = _accept().next_state
    store = _initial_reference_commit_store_v1(wrong_state)

    result = reference_commit_v1(store, bundle)

    assert result.status is ReferenceCommitStatusV1.STALE
    assert result.store is store
    assert result.store.publications == ()


def test_reference_commit_duplicate_returns_already_committed() -> None:
    store = _store_from_pre_state()
    bundle = _bundle()

    first = reference_commit_v1(store, bundle)
    assert first.status is ReferenceCommitStatusV1.PUBLISHED

    second = reference_commit_v1(first.store, bundle)

    assert second.status is ReferenceCommitStatusV1.ALREADY_COMMITTED
    assert second.store is first.store
    assert len(second.store.publications) == 1


def test_reference_commit_invalid_bundle_returns_unchanged_store() -> None:
    store = _store_from_pre_state()

    result = reference_commit_v1(store, object())

    assert result.status is ReferenceCommitStatusV1.INVALID
    assert result.store is store


def test_reference_commit_invalid_store_returns_unchanged() -> None:
    bundle = _bundle()

    result = reference_commit_v1(object(), bundle)  # type: ignore[arg-type]

    assert result.status is ReferenceCommitStatusV1.INVALID


def test_reference_commit_crash_before_linearization_returns_unchanged() -> None:
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


def test_reference_commit_publication_retains_bundle() -> None:
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
