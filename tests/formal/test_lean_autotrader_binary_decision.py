from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_lean_autotrader_binary_decision_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/ZenoDEXAutoTraderBinaryDecision.lean",
        (
            TheoremReference(
                "TauSwap.AutoTrader.BinaryDecision.winnerPair_ge_noop",
                """
                ∀ (emitRequested emitAdmissible : Bool),
                  TauSwap.AutoTrader.BinaryDecision.GePair
                    (TauSwap.AutoTrader.BinaryDecision.winnerPair
                      emitRequested emitAdmissible)
                    (0, 0)
                """,
            ),
        ),
        tmp_path,
    )
