"""Grade-4 BV proof plus source-drift and fixed semantic-control evidence."""

from __future__ import annotations

from collections.abc import Callable
from pathlib import Path
from unittest.mock import Mock

import pytest
import z3

from experiments.tau_economic_qualification_v1.conservation_equivalence import (
    SOURCE_PATH,
    SOURCE_SHA256,
    candidate_source,
    check_conservation_equivalence,
)


def _source() -> str:
    return (Path(__file__).resolve().parents[2] / SOURCE_PATH).read_bytes().decode("utf-8")


def test_full_bv32_output_relation_equivalence_with_nonvacuity_and_mutant_controls() -> None:
    report = check_conservation_equivalence(_source())
    assert report.source_sha256 == SOURCE_SHA256
    assert [(item.name, item.observed) for item in report.obligations] == [
        ("equal_deltas_imply_modular_conservation", "unsat"),
        ("all_four_output_predicates_unchanged", "unsat"),
        ("one_atom_transfer_nonvacuity", "sat"),
        ("modular_wrap_still_rejected_by_direction", "sat"),
        ("missing_receiver_delta_still_rejected", "sat"),
    ]
    assert report.runtime_qualified is False
    assert report.performance_qualified is False


@pytest.mark.parametrize(
    "mutated_source",
    (
        lambda source: source.replace("(before - after) = amount", "(before + after) = amount"),
        lambda source: source.replace("(sb >= sa)", "(sb <= sa)"),
        lambda source: source.replace("(o4[t]:sbf = 1:sbf <->", "(o4[t]:sbf = 0:sbf <->"),
    ),
)
def test_source_drift_cannot_reuse_the_manual_translation(mutated_source: Callable[[str], str]) -> None:
    with pytest.raises(ValueError, match="^CONSERVATION_EQUIVALENCE_SOURCE_DRIFT$"):
        check_conservation_equivalence(mutated_source(_source()))


@pytest.mark.parametrize("status", (z3.unknown, z3.sat))
def test_unproved_miter_cannot_be_promoted(status: z3.CheckSatResult, monkeypatch: pytest.MonkeyPatch) -> None:
    solver = Mock()
    solver.check.return_value = status
    monkeypatch.setattr(z3, "SolverFor", lambda _logic: solver)
    with pytest.raises(
        ValueError,
        match=f"^CONSERVATION_EQUIVALENCE_NOT_ESTABLISHED:equal_deltas_imply_modular_conservation:{status}$",
    ):
        check_conservation_equivalence(_source())


def test_elision_retains_all_output_biconditionals_and_other_source_lines() -> None:
    source_lines = _source().splitlines()
    candidate_lines = candidate_source(_source()).splitlines()
    changed_lines = [
        index for index, (before, after) in enumerate(zip(source_lines, candidate_lines, strict=True), start=1)
        if before != after
    ]
    assert changed_lines == [42, 48]
    for index in (45, 47, 49, 51):
        assert ("= 1:sbf <->" in source_lines[index]) == ("= 1:sbf <->" in candidate_lines[index])
