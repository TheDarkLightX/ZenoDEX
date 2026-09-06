from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_lean_autotrader_live_release_certificate_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/ZenoDEXAutoTraderLiveReleaseCertificate.lean",
        (
            TheoremReference(
                "TauSwap.AutoTrader.LiveReleaseCertificate.releaseOk_iff",
                """
                ∀ (emitRequested liveAdmissionOk systemComposeOk submitBundleOk
                    emitFinalizeOk : Bool),
                  TauSwap.AutoTrader.LiveReleaseCertificate.releaseOk
                      emitRequested liveAdmissionOk systemComposeOk submitBundleOk
                      emitFinalizeOk = true ↔
                    emitRequested = true ∧
                    liveAdmissionOk = true ∧
                    systemComposeOk = true ∧
                    submitBundleOk = true ∧
                    emitFinalizeOk = true
                """,
            ),
        ),
        tmp_path,
    )
