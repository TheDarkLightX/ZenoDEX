from __future__ import annotations

import copy

from tools.check_rust_fcis_policy import DEFAULT_MANIFEST, _load_json, _production_source, validate_manifest


def _manifest() -> dict:
    return copy.deepcopy(_load_json(DEFAULT_MANIFEST))


def test_repository_rust_fcis_manifest_is_internally_consistent() -> None:
    assert validate_manifest(_manifest()) == []


def test_duplicate_surface_id_fails_closed() -> None:
    manifest = _manifest()
    manifest["surfaces"].append(copy.deepcopy(manifest["surfaces"][0]))

    errors = validate_manifest(manifest)

    assert any("duplicate surface_id" in error for error in errors)


def test_partial_rust_authority_cannot_be_release_eligible() -> None:
    manifest = _manifest()
    zusd = next(surface for surface in manifest["surfaces"] if surface["surface_id"] == "zusd_single_vault")
    zusd["release_status"] = "eligible"

    errors = validate_manifest(manifest)

    assert any("partial Rust authority must remain release-blocked" in error for error in errors)


def test_value_moving_surface_requires_atomic_candidate_commit_before_eligibility() -> None:
    manifest = _manifest()
    balances = next(surface for surface in manifest["surfaces"] if surface["surface_id"] == "balances")
    balances["release_status"] = "eligible"

    errors = validate_manifest(manifest)

    assert any("without proved atomic commit must be blocked" in error for error in errors)


def test_released_claim_rejects_blockers_and_policy_exceptions() -> None:
    manifest = _manifest()
    manifest["release_claim"]["status"] = "released"

    errors = validate_manifest(manifest)

    assert any("released claim has blocked surfaces" in error for error in errors)
    assert any("released claim may not retain temporary policy exceptions" in error for error in errors)


def test_unknown_rust_module_fails_closed() -> None:
    manifest = _manifest()
    manifest["required_core_modules"].append("untracked_value_kernel")

    errors = validate_manifest(manifest)

    assert any("inventory modules absent from Rust lib.rs" in error for error in errors)


def test_production_source_ignores_test_only_panic_helpers() -> None:
    source = """
pub fn total() -> Result<(), ()> { Ok(()) }
#[cfg(test)]
mod tests {
    #[test]
    fn test_only() { panic!(\"not production\"); }
}
"""

    production = _production_source(source)

    assert "panic!" not in production
    assert "pub fn total" in production
