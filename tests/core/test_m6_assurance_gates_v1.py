"""Tests for the explicit M6 assurance-gate vocabulary."""

from __future__ import annotations

from pathlib import Path

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


def test_m6_documents_use_explicit_gate_names() -> None:
    repository_root = Path(__file__).resolve().parents[2]
    documents = (
        repository_root / "docs/research/FCIS_M6_PR509_FORMAL_COMPLETENESS_REVIEW_20260802.md",
        repository_root / "docs/research/M6_GLOBAL_ECONOMIC_CORE_ATDD_BDD_V1.md",
        repository_root / "docs/research/M6_RESEARCH_PROGRAM_20260730.md",
    )
    for document in documents:
        text = document.read_text(encoding="utf-8")
        assert "FormalGate" in text
        assert "RuntimeRefinementGate" in text
        assert "MountedAuthorityGate" in text
        assert "Grade R" not in text
        assert "Grade M" not in text
