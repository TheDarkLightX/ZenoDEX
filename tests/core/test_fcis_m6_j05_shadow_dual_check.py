"""J05 shadow replay, dual check, and divergence tests."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from experiments.fcis_m6_j05_shadow_dual_check import (
    EXACT_RELATION_ID,
    REVIEWED_RELATION_ID,
    J05CodeV1,
    J05ComparisonModeV1,
    J05DualCandidateV1,
    J05DualCheckV1,
    J05Error,
    J05OutcomeV1,
    J05RejectV1,
    J05ReplayContextV1,
    J05ShadowOutputV1,
    derive_relation_root,
    derive_reviewed_refinement_result_root,
    derive_shadow_output_root,
    run_shadow_replay_v1,
    verify_dual_check_v1,
)
from src.core.fcis_durable_retraction import tagged_digest

_J04 = (
    Path(__file__).resolve().parents[2]
    / "docs/research/m6_tasks/TASK_J04_MIGRATION_MANIFEST_V1.json"
)


def _context() -> J05ReplayContextV1:
    manifest = json.loads(_J04.read_text(encoding="utf-8"))
    return J05ReplayContextV1(
        manifest_root=manifest["manifest_root"],
        activation_sequence=manifest["activation_sequence"],
        source_profile_root=manifest["source_profile_root"],
        target_profile_root=manifest["target_profile_root"],
        source_result_root=manifest["source_state_root"],
    )


def _candidate(
    context: J05ReplayContextV1,
    mode: J05ComparisonModeV1,
    target_result_root: str,
) -> J05DualCandidateV1:
    shadow_result = run_shadow_replay_v1(context, target_result_root)
    if not isinstance(shadow_result, J05ShadowOutputV1):
        raise AssertionError(f"expected shadow output, got {shadow_result!r}")
    relation_id = (
        EXACT_RELATION_ID if mode is J05ComparisonModeV1.EXACT_EQUALITY else REVIEWED_RELATION_ID
    )
    return J05DualCandidateV1(
        shadow=shadow_result,
        mode=mode,
        relation_id=relation_id,
        relation_root=derive_relation_root(context, shadow_result, mode, relation_id),
    )


def test_j05_exact_equality_allows_phase_progression() -> None:
    context = _context()
    result = verify_dual_check_v1(
        context,
        _candidate(context, J05ComparisonModeV1.EXACT_EQUALITY, context.source_result_root),
    )

    assert isinstance(result, J05DualCheckV1)
    assert result.outcome is J05OutcomeV1.EXACT_MATCH
    assert result.phase_advance_allowed is True
    assert result.divergence is None
    assert result.shadow.is_authoritative is False


def test_j05_reviewed_refinement_allows_only_the_declared_relation() -> None:
    context = _context()
    target_root = derive_reviewed_refinement_result_root(context)

    result = verify_dual_check_v1(
        context,
        _candidate(context, J05ComparisonModeV1.REVIEWED_REFINEMENT, target_root),
    )

    assert isinstance(result, J05DualCheckV1)
    assert result.outcome is J05OutcomeV1.REFINEMENT_MATCH
    assert result.phase_advance_allowed is True


def test_j05_divergence_is_retained_and_blocks_phase_advance() -> None:
    context = _context()
    divergent_root = tagged_digest("j05/divergent-target")
    result = verify_dual_check_v1(
        context,
        _candidate(context, J05ComparisonModeV1.EXACT_EQUALITY, divergent_root),
    )

    assert isinstance(result, J05DualCheckV1)
    assert result.outcome is J05OutcomeV1.DIVERGENCE_RETAINED
    assert result.phase_advance_allowed is False
    assert result.divergence is not None
    assert result.divergence.retained is True
    assert result.divergence.is_authoritative is False
    assert result.divergence.target_result_root == divergent_root


def test_j05_forged_relation_root_rejects() -> None:
    context = _context()
    candidate = _candidate(
        context,
        J05ComparisonModeV1.EXACT_EQUALITY,
        context.source_result_root,
    )
    forged = replace(candidate, relation_root=tagged_digest("j05/forged-relation"))

    result = verify_dual_check_v1(context, forged)

    assert isinstance(result, J05RejectV1)
    assert result.code is J05CodeV1.RELATION_MISMATCH


def test_j05_shadow_output_cannot_be_authoritative() -> None:
    context = _context()
    shadow = run_shadow_replay_v1(context, context.source_result_root)
    assert isinstance(shadow, J05ShadowOutputV1)
    with pytest.raises(J05Error, match="cannot carry authority"):
        J05ShadowOutputV1(
            manifest_root=shadow.manifest_root,
            activation_sequence=shadow.activation_sequence,
            target_profile_root=shadow.target_profile_root,
            target_result_root=shadow.target_result_root,
            output_root=derive_shadow_output_root(shadow),
            is_authoritative=True,
        )


def test_j05_profile_and_sequence_crossings_reject() -> None:
    context = _context()
    candidate = _candidate(
        context,
        J05ComparisonModeV1.EXACT_EQUALITY,
        context.source_result_root,
    )
    foreign_profile = tagged_digest("j05/foreign-profile")
    foreign_context = replace(
        context,
        activation_sequence=context.activation_sequence + 1,
        target_profile_root=foreign_profile,
    )
    crossed_result = run_shadow_replay_v1(foreign_context, context.source_result_root)
    assert isinstance(crossed_result, J05ShadowOutputV1)
    crossed = replace(
        candidate,
        shadow=crossed_result,
        relation_root=derive_relation_root(
            context,
            crossed_result,
            J05ComparisonModeV1.EXACT_EQUALITY,
            EXACT_RELATION_ID,
        ),
    )

    result = verify_dual_check_v1(context, crossed)

    assert isinstance(result, J05RejectV1)
    assert result.code is J05CodeV1.SEQUENCE_MISMATCH
