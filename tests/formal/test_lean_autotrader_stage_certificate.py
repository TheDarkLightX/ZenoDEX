from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_lean_autotrader_stage_certificate_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/ZenoDEXAutoTraderStageCertificate.lean",
        (
            TheoremReference(
                "TauSwap.AutoTrader.StageCertificate.verifyCertificate_of_build",
                """
                ∀ (inputs : TauSwap.AutoTrader.StageCertificate.Inputs),
                  TauSwap.AutoTrader.StageCertificate.verifyCertificate
                    inputs
                    (TauSwap.AutoTrader.StageCertificate.buildCertificate inputs)
                """,
            ),
        ),
        tmp_path,
    )
