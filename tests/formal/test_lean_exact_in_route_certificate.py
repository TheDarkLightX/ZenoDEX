from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_lean_exact_in_route_certificate_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/ZenoDEXExactInRouteCertificate.lean",
        (
            TheoremReference(
                "TauSwap.Routing.ExactInRouteCertificate.keyLe_trans",
                """
                ∀ {a b c : TauSwap.Routing.ExactInRouteCertificate.Candidate},
                  TauSwap.Routing.ExactInRouteCertificate.keyLe a b →
                  TauSwap.Routing.ExactInRouteCertificate.keyLe b c →
                  TauSwap.Routing.ExactInRouteCertificate.keyLe a c
                """,
            ),
        ),
        tmp_path,
    )
