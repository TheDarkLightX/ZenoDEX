from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_lean_settlement_price_history_certificate_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/ZenoDEXSettlementPriceHistoryCertificate.lean",
        (
            TheoremReference(
                "TauSwap.Settlement.PriceHistoryCertificate.verifyCertificate_of_build",
                """
                ∀ (inputs : TauSwap.Settlement.PriceHistoryCertificate.Inputs),
                  TauSwap.Settlement.PriceHistoryCertificate.verifyCertificate
                    inputs
                    (TauSwap.Settlement.PriceHistoryCertificate.buildCertificate inputs)
                """,
            ),
        ),
        tmp_path,
    )
