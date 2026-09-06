from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_lean_exact_out_route_certificate_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/ZenoDEXExactOutRouteCertificate.lean",
        (
            TheoremReference(
                "TauSwap.Routing.ExactOutRouteCertificate.keyLe_trans",
                """
                ∀ {a b c : TauSwap.Routing.ExactOutRouteCertificate.Candidate},
                  TauSwap.Routing.ExactOutRouteCertificate.keyLe a b →
                  TauSwap.Routing.ExactOutRouteCertificate.keyLe b c →
                  TauSwap.Routing.ExactOutRouteCertificate.keyLe a c
                """,
            ),
        ),
        tmp_path,
    )
