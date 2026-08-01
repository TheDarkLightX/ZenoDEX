"""Fail-closed checker for the FCIS M6 J01 migration lifecycle."""

from __future__ import annotations

import sys
from typing import Final

from src.core import fcis_durable_retraction as dra

EXPECTED_PHASE_NAMES: Final[tuple[str, ...]] = (
    "LEGACY",
    "SHADOW_REPLAY",
    "DUAL_CHECK",
    "QUIESCED",
    "AUTHORITY_SWITCH",
    "POST_SWITCH_VALIDATION",
    "LEGACY_DISABLED",
)


def check_lifecycle() -> None:
    """Verify exact phase membership, adjacency, and rejection behavior."""

    actual_names = tuple(phase.name for phase in dra.MigrationPhaseV1)
    if actual_names != EXPECTED_PHASE_NAMES:
        raise ValueError(f"phase registry mismatch: {actual_names!r}")
    phases = tuple(dra.MigrationPhaseV1[name] for name in EXPECTED_PHASE_NAMES)
    legacy_root = dra.tagged_digest("j01/legacy-profile")
    target_root = dra.tagged_digest("j01/target-profile")
    authority = dra.initial_authority_state(legacy_root, target_root)
    if authority.phase is not phases[0] or authority.epoch_index != 0:
        raise ValueError("genesis authority is not LEGACY at epoch zero")
    for index, next_phase in enumerate(phases[1:], start=1):
        authority = dra.advance_authority_state(
            authority,
            next_phase,
            dra.tagged_digest(f"j01/transport/{index}"),
        )
        if authority.phase is not next_phase or authority.epoch_index != index:
            raise ValueError("valid lifecycle edge produced the wrong authority")
    if authority.phase is not phases[-1]:
        raise ValueError("lifecycle did not reach LEGACY_DISABLED")

    genesis = dra.initial_authority_state(legacy_root, target_root)
    invalid_edges = (
        (genesis, phases[2], "skip LEGACY -> DUAL_CHECK"),
        (
            dra.advance_authority_state(
                genesis,
                phases[1],
                dra.tagged_digest("j01/transport/reverse-base"),
            ),
            phases[0],
            "reverse SHADOW_REPLAY -> LEGACY",
        ),
        (
            dra.advance_authority_state(
                genesis,
                phases[1],
                dra.tagged_digest("j01/transport/unknown-base"),
            ),
            object(),
            "unknown phase",
        ),
    )
    for current, candidate, label in invalid_edges:
        try:
            dra.advance_authority_state(
                current,
                candidate,
                dra.tagged_digest(f"j01/invalid/{label}"),
            )
        except (dra.DurableRetractionError, TypeError, ValueError):
            continue
        raise ValueError(f"invalid lifecycle edge was accepted: {label}")

    terminal = authority
    try:
        dra.advance_authority_state(
            terminal,
            phases[-1],
            dra.tagged_digest("j01/terminal-repeat"),
        )
    except dra.DurableRetractionError:
        return
    raise ValueError("terminal lifecycle accepted another transition")


def main(argv: list[str]) -> int:
    if len(argv) != 1:
        print("usage: check_fcis_m6_j01_migration_lifecycle.py", file=sys.stderr)
        return 2
    try:
        check_lifecycle()
    except (dra.DurableRetractionError, TypeError, ValueError) as exc:
        print(f"J01_MIGRATION_LIFECYCLE_REJECT: {exc}", file=sys.stderr)
        return 1
    print("J01_MIGRATION_LIFECYCLE_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
