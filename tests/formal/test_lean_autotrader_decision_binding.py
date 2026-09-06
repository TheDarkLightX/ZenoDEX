from __future__ import annotations

from pathlib import Path

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    check_lean_stdlib_source,
)


def test_lean_autotrader_decision_binding_file_typechecks(tmp_path: Path) -> None:
    check_lean_stdlib_source(
        "Proofs/ZenoDEXAutoTraderDecisionBinding.lean",
        (
            TheoremReference(
                "TauSwap.AutoTrader.DecisionBinding.candidateSetHash_eq_canonicalCandidateSetHash",
                """
                ∀ (candidateSet :
                    TauSwap.AutoTrader.DecisionBinding.StrategyCandidateSet),
                  TauSwap.AutoTrader.DecisionBinding.candidateSetHash candidateSet =
                    TauSwap.AutoTrader.DecisionBinding.canonicalCandidateSetHash candidateSet
                """,
            ),
        ),
        tmp_path,
    )
