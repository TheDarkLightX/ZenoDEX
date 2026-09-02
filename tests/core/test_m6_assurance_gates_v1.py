"""Tests for the explicit M6 assurance-gate vocabulary."""

from __future__ import annotations

from src.core.m6_assurance_gates_v1 import M6AssuranceGateV1
from src.core.m6_safe_mount_v1 import M6AssuranceGateV1 as FacadeM6AssuranceGateV1


def test_assurance_gate_names_are_distinct_from_letter_grades_and_requirement_ids() -> None:
    assert tuple(gate.value for gate in M6AssuranceGateV1) == (
        "FormalGate",
        "RuntimeRefinementGate",
        "MountedAuthorityGate",
    )
    assert all(not value.startswith("Grade ") for value in M6AssuranceGateV1)
    assert all(not value.startswith("M6-R") for value in M6AssuranceGateV1)


def test_runtime_gate_name_expands_the_ambiguous_r_label() -> None:
    assert M6AssuranceGateV1.RUNTIME_REFINEMENT.value == "RuntimeRefinementGate"


def test_safe_mount_facade_exports_the_same_gate_registry() -> None:
    assert FacadeM6AssuranceGateV1 is M6AssuranceGateV1
