"""J01 exact migration lifecycle checker tests."""

from __future__ import annotations

import pytest

from src.core import fcis_durable_retraction as dra
from tools.check_fcis_m6_j01_migration_lifecycle import (
    EXPECTED_PHASE_NAMES,
    check_lifecycle,
)


def test_j01_exact_lifecycle_checker_passes() -> None:
    check_lifecycle()


def test_j01_phase_enum_is_exact_and_closed() -> None:
    assert tuple(phase.name for phase in dra.MigrationPhaseV1) == EXPECTED_PHASE_NAMES
    with pytest.raises(ValueError, match="UNKNOWN"):
        dra.MigrationPhaseV1("UNKNOWN")


def test_j01_skip_and_reverse_edges_reject() -> None:
    legacy = dra.tagged_digest("j01/test-legacy")
    target = dra.tagged_digest("j01/test-target")
    genesis = dra.initial_authority_state(legacy, target)

    with pytest.raises(dra.DurableRetractionError, match="one edge"):
        dra.advance_authority_state(
            genesis,
            dra.MigrationPhaseV1.DUAL_CHECK,
            dra.tagged_digest("j01/test-skip"),
        )

    shadow = dra.advance_authority_state(
        genesis,
        dra.MigrationPhaseV1.SHADOW_REPLAY,
        dra.tagged_digest("j01/test-shadow"),
    )
    with pytest.raises(dra.DurableRetractionError, match="one edge"):
        dra.advance_authority_state(
            shadow,
            dra.MigrationPhaseV1.LEGACY,
            dra.tagged_digest("j01/test-reverse"),
        )


def test_j01_terminal_phase_rejects_repeat_transition() -> None:
    legacy = dra.tagged_digest("j01/terminal-legacy")
    target = dra.tagged_digest("j01/terminal-target")
    authority = dra.initial_authority_state(legacy, target)
    phases = tuple(dra.MigrationPhaseV1)
    for index, phase in enumerate(phases[1:], start=1):
        authority = dra.advance_authority_state(
            authority,
            phase,
            dra.tagged_digest(f"j01/terminal/{index}"),
        )

    with pytest.raises(dra.DurableRetractionError, match="terminal"):
        dra.advance_authority_state(
            authority,
            dra.MigrationPhaseV1.LEGACY_DISABLED,
            dra.tagged_digest("j01/terminal-repeat"),
        )
