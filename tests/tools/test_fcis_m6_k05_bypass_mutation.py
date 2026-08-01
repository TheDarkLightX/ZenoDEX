"""K05 entrypoint bypass-mutation matrix tests."""

from __future__ import annotations

from experiments.fcis_m6_k05_bypass_mutation_check import run_checks
from src.core.fcis_m6_k05_bypass_mutants import K05MutantV1


def test_k05_full_matrix_kills_all_entrypoint_mutants() -> None:
    run_checks()


def test_k05_matrix_cardinality_is_six_mutants_per_entrypoint() -> None:
    assert len(K05MutantV1) == 6
