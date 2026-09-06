from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_split_routing_staircase_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/SplitRoutingStaircase.lean",
        (
            TheoremReference(
                "Proofs.SplitRoutingStaircase.remaining_input_antitone",
                """
                ∀ {c a D : Nat},
                  c ≤ a → D - a ≤ D - c
                """,
            ),
        ),
        tmp_path,
    )
