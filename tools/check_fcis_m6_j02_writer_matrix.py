"""Fail-closed checker for the FCIS M6 J02 writer matrix."""

from __future__ import annotations

import sys
from typing import Final

from src.core import fcis_durable_retraction as dra

EXPECTED_WRITERS: Final[dict[dra.MigrationPhaseV1, str | None]] = {
    dra.MigrationPhaseV1.LEGACY: "legacy",
    dra.MigrationPhaseV1.SHADOW_REPLAY: "legacy",
    dra.MigrationPhaseV1.DUAL_CHECK: "legacy",
    dra.MigrationPhaseV1.QUIESCED: None,
    dra.MigrationPhaseV1.AUTHORITY_SWITCH: "target",
    dra.MigrationPhaseV1.POST_SWITCH_VALIDATION: "target",
    dra.MigrationPhaseV1.LEGACY_DISABLED: "target",
}


def _expected_writer_roots(
    phase: dra.MigrationPhaseV1,
    legacy_root: str,
    target_root: str,
) -> tuple[str, ...]:
    writer = EXPECTED_WRITERS[phase]
    if writer == "legacy":
        return (legacy_root,)
    if writer == "target":
        return (target_root,)
    if writer is None:
        return ()
    raise ValueError(f"unknown writer policy for {phase.name}")


def check_writer_matrix() -> None:
    """Verify the phase-to-writer relation and reject forbidden sets."""

    phases = tuple(dra.MigrationPhaseV1)
    if tuple(EXPECTED_WRITERS) != phases:
        raise ValueError("writer matrix does not cover the exact phase order")
    legacy_root = dra.tagged_digest("j02/legacy-profile")
    target_root = dra.tagged_digest("j02/target-profile")
    authority = dra.initial_authority_state(legacy_root, target_root)
    for index, phase in enumerate(phases):
        if index:
            authority = dra.advance_authority_state(
                authority,
                phase,
                dra.tagged_digest(f"j02/transport/{index}"),
            )
        expected_writers = _expected_writer_roots(phase, legacy_root, target_root)
        if authority.allowed_writer_roots != expected_writers:
            raise ValueError(f"writer set mismatch for {phase.name}")
        expected_active = (
            legacy_root
            if phase
            in (
                dra.MigrationPhaseV1.LEGACY,
                dra.MigrationPhaseV1.SHADOW_REPLAY,
                dra.MigrationPhaseV1.DUAL_CHECK,
                dra.MigrationPhaseV1.QUIESCED,
            )
            else target_root
        )
        if authority.active_profile_root != expected_active:
            raise ValueError(f"active profile mismatch for {phase.name}")
        if len(authority.allowed_writer_roots) > 1:
            raise ValueError(f"dual writer set accepted for {phase.name}")
        if phase is dra.MigrationPhaseV1.QUIESCED and authority.allowed_writer_roots:
            raise ValueError("quiesced phase has a value-moving writer")
        if authority.allowed_writer_roots and authority.active_profile_root not in (
            authority.allowed_writer_roots
        ):
            raise ValueError(f"active writer is absent for {phase.name}")

    quiesced = next(
        state
        for state in _authority_trace(legacy_root, target_root)
        if state.phase is dra.MigrationPhaseV1.QUIESCED
    )
    if _writer_is_allowed(quiesced, legacy_root) or _writer_is_allowed(quiesced, target_root):
        raise ValueError("quiesced writer bypass accepted")

    switched = next(
        state
        for state in _authority_trace(legacy_root, target_root)
        if state.phase is dra.MigrationPhaseV1.AUTHORITY_SWITCH
    )
    if _writer_is_allowed(switched, legacy_root):
        raise ValueError("legacy writer remains enabled after authority switch")
    if not _writer_is_allowed(switched, target_root):
        raise ValueError("target writer is absent after authority switch")


def _authority_trace(
    legacy_root: str,
    target_root: str,
) -> tuple[dra.AuthorityStateV1, ...]:
    phases = tuple(dra.MigrationPhaseV1)
    states: list[dra.AuthorityStateV1] = [dra.initial_authority_state(legacy_root, target_root)]
    for index, phase in enumerate(phases[1:], start=1):
        states.append(
            dra.advance_authority_state(
                states[-1],
                phase,
                dra.tagged_digest(f"j02/trace/{index}"),
            )
        )
    return tuple(states)


def _writer_is_allowed(authority: dra.AuthorityStateV1, writer_root: str) -> bool:
    if type(writer_root) is not str:
        return False
    return writer_root in authority.allowed_writer_roots


def main(argv: list[str]) -> int:
    if len(argv) != 1:
        print("usage: check_fcis_m6_j02_writer_matrix.py", file=sys.stderr)
        return 2
    try:
        check_writer_matrix()
    except (dra.DurableRetractionError, TypeError, ValueError) as exc:
        print(f"J02_WRITER_MATRIX_REJECT: {exc}", file=sys.stderr)
        return 1
    print("J02_WRITER_MATRIX_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
