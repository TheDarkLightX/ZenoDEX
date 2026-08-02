"""Independent deterministic checks for the E04 retry-classifier packet."""

from __future__ import annotations

import json
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from experiments.fcis_m6_e04_retry_classifier import (  # noqa: E402
    DEFAULT_OUTPUT_PATH,
    OTHER_STATE_ROOT_V1,
    OTHER_WRITER_ROOT_V1,
    build_attempt,
    build_committed_state,
    build_nullifier_collision_state,
    build_payload,
    build_reopen_receipt,
    build_state,
)
from src.core.fcis_m6_e03_unique_commit_port import (  # noqa: E402
    _mint_e03_commit_identity_v1,
)
from src.core.fcis_m6_e04_retry_classifier import (  # noqa: E402
    E04ClientKnowledgeV1,
    E04DurableOutcomeV1,
    E04RejectCodeV1,
    E04RejectV1,
    E04RetryResolutionV1,
    classify_e04_retry,
    is_verified_e04_attempt_v1,
    is_verified_e04_stored_state_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.build_fcis_m6_e03_database_uniqueness import build_candidate  # noqa: E402


def _resolution(result: object) -> E04RetryResolutionV1:
    if type(result) is not E04RetryResolutionV1:
        raise AssertionError(f"expected E04 resolution, got {result!r}")
    return result


def _reject(result: object, code: E04RejectCodeV1) -> None:
    if type(result) is not E04RejectV1:
        raise AssertionError(f"expected E04 rejection, got {result!r}")
    if result.code is not code:
        raise AssertionError(f"wrong E04 rejection: {result!r}")


def run_checks() -> None:
    vector_path = _ROOT / DEFAULT_OUTPUT_PATH
    vector = json.loads(vector_path.read_text(encoding="utf-8"))
    regenerated = build_payload()
    if vector != regenerated:
        raise AssertionError("E04 vector is not the independently regenerated payload")

    attempt = build_attempt()
    cases = (
        ("absent", build_state(), E04DurableOutcomeV1.ABSENT_RETRYABLE),
        ("already", build_committed_state(attempt), E04DurableOutcomeV1.ALREADY_COMMITTED),
        (
            "nullifier_collision",
            build_nullifier_collision_state(),
            E04DurableOutcomeV1.DEFINITE_REJECTION,
        ),
        (
            "stale",
            build_state(
                genesis_state_root=OTHER_STATE_ROOT_V1, current_state_root=OTHER_STATE_ROOT_V1
            ),
            E04DurableOutcomeV1.STALE_STATE,
        ),
        (
            "head_authority",
            build_state(allowed_writer_roots=(OTHER_WRITER_ROOT_V1,)),
            E04DurableOutcomeV1.DEFINITE_REJECTION,
        ),
    )
    for name, state, expected in cases:
        receipt = build_reopen_receipt(state)
        confirmed = _resolution(
            classify_e04_retry(attempt, state, E04ClientKnowledgeV1.CONFIRMED, receipt)
        )
        indeterminate = _resolution(
            classify_e04_retry(attempt, state, E04ClientKnowledgeV1.INDETERMINATE, receipt)
        )
        if confirmed.outcome is not expected or indeterminate.outcome is not expected:
            raise AssertionError(f"E04 case {name} resolved incorrectly")
        if confirmed.attempt_root != indeterminate.attempt_root:
            raise AssertionError(f"E04 case {name} changed attempt lineage by transport knowledge")
        if confirmed.snapshot_root != indeterminate.snapshot_root:
            raise AssertionError(f"E04 case {name} changed state lineage by transport knowledge")

    changed_fingerprint = build_attempt(expected_pre_root=OTHER_STATE_ROOT_V1)
    committed_state = build_committed_state(attempt)
    _resolution(
        classify_e04_retry(
            changed_fingerprint,
            committed_state,
            E04ClientKnowledgeV1.CONFIRMED,
            build_reopen_receipt(committed_state),
        )
    )
    changed_result = classify_e04_retry(
        changed_fingerprint,
        committed_state,
        E04ClientKnowledgeV1.CONFIRMED,
        build_reopen_receipt(committed_state),
    )
    if (
        type(changed_result) is not E04RetryResolutionV1
        or changed_result.outcome is not E04DurableOutcomeV1.DEFINITE_REJECTION
    ):
        raise AssertionError("same-ID changed-fingerprint precedence failed")

    baseline = build_candidate()
    sequence_two = _mint_e03_commit_identity_v1(
        sequence=2,
        commit_id="f" * 64,
        nullifier=baseline.nullifier,
        effects=baseline.effects,
    )
    sequence_mismatch = build_attempt(commit=sequence_two)
    empty_state = build_state()
    sequence_result = _resolution(
        classify_e04_retry(
            sequence_mismatch,
            empty_state,
            E04ClientKnowledgeV1.CONFIRMED,
            build_reopen_receipt(empty_state),
        )
    )
    if sequence_result.outcome is not E04DurableOutcomeV1.DEFINITE_REJECTION:
        raise AssertionError("sequence mismatch was accepted")

    for state_overrides in (
        {"authority_epoch_index": 4},
        {"authority_state_root": OTHER_STATE_ROOT_V1},
        {"allowed_writer_roots": (OTHER_WRITER_ROOT_V1,)},
        {"verifier_profile_root": OTHER_STATE_ROOT_V1},
    ):
        context_state = build_state(**state_overrides)
        context_result = _resolution(
            classify_e04_retry(
                attempt,
                context_state,
                E04ClientKnowledgeV1.CONFIRMED,
                build_reopen_receipt(context_state),
            )
        )
        if context_result.outcome is not E04DurableOutcomeV1.DEFINITE_REJECTION:
            raise AssertionError("head or authority context mismatch was accepted")

    stale_context = build_state(
        genesis_state_root=OTHER_STATE_ROOT_V1,
        current_state_root=OTHER_STATE_ROOT_V1,
        allowed_writer_roots=(OTHER_WRITER_ROOT_V1,),
    )
    stale_result = _resolution(
        classify_e04_retry(
            attempt,
            stale_context,
            E04ClientKnowledgeV1.CONFIRMED,
            build_reopen_receipt(stale_context),
        )
    )
    if stale_result.outcome is not E04DurableOutcomeV1.STALE_STATE:
        raise AssertionError("stale state did not precede context rejection")

    receipt_state = build_state()
    receipt = build_reopen_receipt(receipt_state)
    _reject(
        classify_e04_retry(
            attempt,
            receipt_state,
            E04ClientKnowledgeV1.CONFIRMED,
            object(),
        ),
        E04RejectCodeV1.WRONG_REOPEN_RECEIPT_TYPE,
    )
    _reject(
        classify_e04_retry(
            attempt,
            build_committed_state(),
            E04ClientKnowledgeV1.CONFIRMED,
            receipt,
        ),
        E04RejectCodeV1.REOPEN_SUBJECT_MISMATCH,
    )

    forged_attempt = object.__new__(type(attempt))
    for name in (
        "request_identity",
        "commit",
        "expected_pre_root",
        "writer_profile_root",
        "authority_state_root",
        "verifier_profile_root",
        "sequence_binding",
    ):
        object.__setattr__(forged_attempt, name, object.__getattribute__(attempt, name))
    if is_verified_e04_attempt_v1(forged_attempt):
        raise AssertionError("forged E04 attempt crossed the verifier boundary")
    _reject(
        classify_e04_retry(
            forged_attempt,
            build_state(),
            E04ClientKnowledgeV1.CONFIRMED,
            build_reopen_receipt(build_state()),
        ),
        E04RejectCodeV1.UNVERIFIED_ATTEMPT,
    )

    state = build_state()
    forged_state = object.__new__(type(state))
    for name in (
        "genesis_state_root",
        "current_state_root",
        "authority_epoch_index",
        "authority_state_root",
        "allowed_writer_roots",
        "deployment_config_root",
        "verifier_profile_root",
        "commits",
        "snapshot_root",
    ):
        object.__setattr__(forged_state, name, object.__getattribute__(state, name))
    if is_verified_e04_stored_state_v1(forged_state):
        raise AssertionError("forged E04 state crossed the verifier boundary")
    _reject(
        classify_e04_retry(
            attempt,
            forged_state,
            E04ClientKnowledgeV1.CONFIRMED,
            build_reopen_receipt(state),
        ),
        E04RejectCodeV1.UNVERIFIED_STATE,
    )
    _reject(
        classify_e04_retry(attempt, state, True, build_reopen_receipt(state)),
        E04RejectCodeV1.WRONG_KNOWLEDGE_TYPE,
    )
    if canonical_json_bytes(regenerated) + b"\n" != vector_path.read_bytes():
        raise AssertionError("E04 vector bytes are not canonical")
    print("E04_RETRY_CLASSIFIER_CHECKS_PASS")


if __name__ == "__main__":
    run_checks()
