from __future__ import annotations

from dataclasses import FrozenInstanceError, replace

import pytest

from tools.fcis_inventory_core import (
    Diagnostic,
    Inventory,
    SourceFile,
    SurfaceRecord,
    binding_digest,
    canonical_report,
    validate_inventory,
)


def _surface(**changes) -> SurfaceRecord:
    record = SurfaceRecord(
        surface_id="spot",
        rust_entrypoints=("crate::step",),
        python_shadow_entrypoints=("shadow.step",),
        formal_transition_artifacts=("formal/step",),
        state_schema=("state",),
        command_schema=("command",),
        execution_context_schema=("context",),
        effect_schema=("effects",),
        receipt_schema=("receipt",),
        rejection_registry=("reject",),
        authority_profiles=(("public-testnet", "python_authority"),),
        invariants=("conservation",),
        proof_status="partial",
        differential_status="partial",
        test_status="pass",
        atomic_commit_status="partial",
        audit_cases=("CASE-1",),
        direct_callers=("caller",),
        commit_path=("commit",),
        external_delivery_path=(),
        source_patterns=("src/core/spot.py",),
        binding_patterns=("src/core/spot.py",),
        binding_sha256="placeholder",
        cbc_grade="partial",
        remaining_blockers=("atomic commit",),
    )
    return replace(record, **changes)


def test_records_are_transitively_immutable_for_owned_fields():
    with pytest.raises(FrozenInstanceError):
        _surface().surface_id = "changed"  # type: ignore[misc]


def test_unclassified_value_path_fails_closed():
    source = SourceFile("src/core/new_value.py", "balance += 1")
    surface = _surface(binding_sha256=binding_digest(_surface(), (source,)))
    diagnostics = validate_inventory(
        Inventory(("src/core",), (surface,)),
        (source,),
        require_release=False,
    )
    assert Diagnostic(
        "UNCLASSIFIED_VALUE_PATH", "src/core/new_value.py", "no inventory owner"
    ) in diagnostics


def test_report_is_byte_deterministic_under_source_reordering():
    sources = (
        SourceFile("src/core/spot.py", "balance += 1"),
        SourceFile("src/core/other.py", "value = 1"),
    )
    base = _surface()
    surface = replace(base, binding_sha256=binding_digest(base, sources))
    inventory = Inventory(("src/core",), (surface,))
    diagnostics = validate_inventory(inventory, sources, require_release=False)
    first = canonical_report(inventory, sources, diagnostics, require_release=False)
    second = canonical_report(
        inventory, tuple(reversed(sources)), diagnostics, require_release=False
    )
    assert first == second


def test_promoted_partial_surface_is_rejected():
    source = SourceFile("src/core/spot.py", "balance += 1")
    base = _surface(
        authority_profiles=(("public-testnet", "rust_authority_with_python_shadow"),)
    )
    surface = replace(base, binding_sha256=binding_digest(base, (source,)))
    diagnostics = validate_inventory(
        Inventory(("src/core",), (surface,)),
        (source,),
        require_release=False,
    )
    assert any(item.code == "PROMOTED_WITH_INCOMPLETE_EVIDENCE" for item in diagnostics)
