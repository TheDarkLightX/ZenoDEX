from __future__ import annotations

import hashlib
from dataclasses import FrozenInstanceError

import pytest

from src.core.deterministic_parallel_admission import (
    FrozenFactSet,
    MonotoneFact,
    ParallelExecutionContext,
    SemanticRejection,
    WorkerBundle,
    join_parallel_admission,
)


def _h(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("ascii")).hexdigest()


def _context(*, suffix: str = "", profile: str = "logical-v1") -> ParallelExecutionContext:
    return ParallelExecutionContext(
        pre_state_root=_h("state" + suffix),
        command_set_root=_h("commands" + suffix),
        execution_context_hash=_h("execution" + suffix),
        policy_hash=_h("policy" + suffix),
        module_version_digest=_h("module" + suffix),
        algorithm_version_digest=_h("algorithm" + suffix),
        partition_profile_version=profile,
    )


def _bundle(
    context: ParallelExecutionContext,
    partition_id: int,
    *,
    facts: tuple[MonotoneFact, ...] = (),
    rejections: tuple[SemanticRejection, ...] = (),
    failure_code: str | None = None,
) -> WorkerBundle:
    return WorkerBundle(
        context_hash=context.context_hash,
        partition_profile_version=context.partition_profile_version,
        logical_partition_id=partition_id,
        facts=facts,
        semantic_rejections=rejections,
        failure_code=failure_code,
        failure_evidence_hash=(
            None if failure_code is None else _h(f"failure:{partition_id}:{failure_code}")
        ),
    )


def test_context_hash_binds_every_authority_field() -> None:
    base = _context()
    assert base == _context()
    assert base.context_hash != _context(suffix="-other").context_hash


def test_arrival_order_and_local_fact_order_do_not_change_frozen_result() -> None:
    context = _context()
    fact_a = MonotoneFact("intent/0001/authenticated", b"yes")
    fact_b = MonotoneFact("intent/0002/authenticated", b"yes")
    left = _bundle(context, 10, facts=(fact_b, fact_a))
    right = _bundle(context, 20, facts=(fact_a,))

    first = join_parallel_admission(
        context,
        expected_partition_ids=(10, 20),
        bundles=(left, right),
    )
    second = join_parallel_admission(
        context,
        expected_partition_ids=(10, 20),
        bundles=(right, left),
    )

    assert first.ok is True
    assert second.ok is True
    assert first.join_hash == second.join_hash
    assert first.frozen_facts == second.frozen_facts
    assert first.frozen_facts is not None
    assert tuple(fact.key for fact in first.frozen_facts.facts) == (
        "intent/0001/authenticated",
        "intent/0002/authenticated",
    )


def test_identical_fact_writes_are_idempotent() -> None:
    context = _context()
    fact = MonotoneFact("proof/abc/verified", b"receipt-digest")
    result = join_parallel_admission(
        context,
        expected_partition_ids=(0, 1),
        bundles=(
            _bundle(context, 0, facts=(fact, fact)),
            _bundle(context, 1, facts=(fact,)),
        ),
    )

    assert result.ok is True
    assert result.frozen_facts is not None
    assert result.frozen_facts.facts == (fact,)


def test_conflicting_fact_values_fail_without_candidate_deterministically() -> None:
    context = _context()
    first_bundle = _bundle(
        context,
        0,
        facts=(MonotoneFact("intent/0001/verdict", b"accept"),),
    )
    second_bundle = _bundle(
        context,
        1,
        facts=(MonotoneFact("intent/0001/verdict", b"reject"),),
    )

    first = join_parallel_admission(
        context,
        expected_partition_ids=(0, 1),
        bundles=(first_bundle, second_bundle),
    )
    second = join_parallel_admission(
        context,
        expected_partition_ids=(0, 1),
        bundles=(second_bundle, first_bundle),
    )

    assert first.ok is False
    assert first.frozen_facts is None
    assert first.rejection is not None
    assert first.rejection.code == "FACT_CONFLICT"
    assert first.rejection.fact_key == "intent/0001/verdict"
    assert first.join_hash == second.join_hash


@pytest.mark.parametrize(
    ("bundles", "expected_partition"),
    [
        (lambda c: (_bundle(c, 0),), 1),
        (lambda c: (_bundle(c, 0), _bundle(c, 0), _bundle(c, 1)), 0),
        (lambda c: (_bundle(c, 0), _bundle(c, 1), _bundle(c, 2)), 2),
    ],
)
def test_partition_shape_failures_are_canonical(
    bundles,
    expected_partition: int,
) -> None:
    context = _context()
    result = join_parallel_admission(
        context,
        expected_partition_ids=(0, 1),
        bundles=bundles(context),
    )

    assert result.ok is False
    assert result.frozen_facts is None
    assert result.rejection is not None
    assert result.rejection.code == "PARTITION_SET_INVALID"
    assert result.rejection.partition_id == expected_partition


def test_context_and_partition_profile_mismatch_fail_closed() -> None:
    context = _context()
    other = _context(suffix="-other")
    wrong_context = join_parallel_admission(
        context,
        expected_partition_ids=(0,),
        bundles=(_bundle(other, 0),),
    )
    wrong_profile_bundle = WorkerBundle(
        context_hash=context.context_hash,
        partition_profile_version="logical-v2",
        logical_partition_id=0,
    )
    wrong_profile = join_parallel_admission(
        context,
        expected_partition_ids=(0,),
        bundles=(wrong_profile_bundle,),
    )

    assert wrong_context.rejection is not None
    assert wrong_context.rejection.code == "CONTEXT_MISMATCH"
    assert wrong_context.frozen_facts is None
    assert wrong_profile.rejection is not None
    assert wrong_profile.rejection.code == "PARTITION_PROFILE_MISMATCH"
    assert wrong_profile.frozen_facts is None


def test_worker_failure_returns_no_candidate() -> None:
    context = _context()
    result = join_parallel_admission(
        context,
        expected_partition_ids=(0,),
        bundles=(_bundle(context, 0, failure_code="TIMEOUT"),),
    )

    assert result.ok is False
    assert result.frozen_facts is None
    assert result.rejection is not None
    assert result.rejection.code == "WORKER_FAILURE"


def test_semantic_rejection_precedence_uses_logical_order_not_arrival_order() -> None:
    context = _context()
    later_partition_earlier_local = SemanticRejection(
        local_command_index=0,
        code="LATER_PARTITION",
        evidence_hash=_h("later"),
    )
    earlier_partition_later_local = SemanticRejection(
        local_command_index=9,
        code="EARLIER_PARTITION",
        evidence_hash=_h("earlier"),
    )
    result = join_parallel_admission(
        context,
        expected_partition_ids=(5, 9),
        bundles=(
            _bundle(context, 9, rejections=(later_partition_earlier_local,)),
            _bundle(context, 5, rejections=(earlier_partition_later_local,)),
        ),
    )

    assert result.ok is False
    assert result.rejection is not None
    assert result.rejection.code == "SEMANTIC_REJECTION"
    assert result.rejection.partition_id == 5
    assert result.rejection.local_command_index == 9


def test_frozen_fact_set_is_transitively_immutable_at_public_surface() -> None:
    fact = MonotoneFact("intent/0001/authenticated", b"yes")
    frozen = FrozenFactSet((fact,))

    with pytest.raises(FrozenInstanceError):
        frozen.facts = ()  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        fact.payload = b"no"  # type: ignore[misc]


def test_worker_bundle_canonicalizes_duplicate_inputs() -> None:
    context = _context()
    fact = MonotoneFact("proof/abc/verified", b"receipt")
    rejection = SemanticRejection(0, "INVALID_PROOF", _h("proof"))
    with_duplicates = _bundle(
        context,
        0,
        facts=(fact, fact),
        rejections=(rejection, rejection),
    )
    canonical = _bundle(
        context,
        0,
        facts=(fact,),
        rejections=(rejection,),
    )

    assert with_duplicates == canonical
    assert with_duplicates.bundle_hash == canonical.bundle_hash


def test_bool_is_not_a_logical_partition_id() -> None:
    context = _context()
    with pytest.raises(TypeError):
        WorkerBundle(
            context_hash=context.context_hash,
            partition_profile_version=context.partition_profile_version,
            logical_partition_id=True,  # type: ignore[arg-type]
        )
