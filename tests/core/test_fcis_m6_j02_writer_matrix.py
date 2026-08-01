"""J02 writer matrix and stale-writer rejection tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import fcis_durable_retraction as dra
from tools.check_fcis_m6_j02_writer_matrix import (
    EXPECTED_WRITERS,
    check_writer_matrix,
)


def _trace() -> tuple[dra.AuthorityStateV1, ...]:
    legacy = dra.tagged_digest("j02/test-legacy")
    target = dra.tagged_digest("j02/test-target")
    phases = tuple(dra.MigrationPhaseV1)
    states = [dra.initial_authority_state(legacy, target)]
    for index, phase in enumerate(phases[1:], start=1):
        states.append(
            dra.advance_authority_state(
                states[-1],
                phase,
                dra.tagged_digest(f"j02/test-transport/{index}"),
            )
        )
    return tuple(states)


def test_j02_writer_matrix_checker_passes() -> None:
    check_writer_matrix()


def test_j02_writer_policy_matches_every_phase() -> None:
    states = _trace()
    legacy = states[0].legacy_profile_root
    target = states[0].target_profile_root
    for state in states:
        expected = EXPECTED_WRITERS[state.phase]
        expected_roots = (
            (legacy,) if expected == "legacy" else (target,) if expected == "target" else ()
        )
        assert state.allowed_writer_roots == expected_roots


def test_j02_dual_writer_and_quiesced_writer_mutants_reject() -> None:
    legacy, target = _trace()[0].legacy_profile_root, _trace()[0].target_profile_root
    authority = _trace()[0]
    with pytest.raises(dra.DurableRetractionError, match="writer set"):
        replace(
            authority,
            allowed_writer_roots=tuple(sorted((legacy, target))),
        )

    quiesced = next(state for state in _trace() if state.phase is dra.MigrationPhaseV1.QUIESCED)
    with pytest.raises(dra.DurableRetractionError, match="writer set"):
        replace(quiesced, allowed_writer_roots=(legacy,))


def test_j02_legacy_writer_is_rejected_after_switch() -> None:
    states = _trace()
    switched = next(
        state for state in states if state.phase is dra.MigrationPhaseV1.AUTHORITY_SWITCH
    )

    assert switched.allowed_writer_roots == (switched.target_profile_root,)
    assert switched.legacy_profile_root not in switched.allowed_writer_roots
