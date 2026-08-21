from __future__ import annotations

import json
from pathlib import Path

from tools import check_production_readiness_g1_asset_authority_v1 as checker


def test_given_candidate_when_checked_then_authority_remains_unselected() -> None:
    # Arrange / Act
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    # Assert
    assert report["ok"] is True
    assert report["candidate_profile_count"] == 1
    assert report["selected_profile_count"] == 0
    assert report["production_authority"] == "NONE"
    assert report["g1_complete"] is False
    assert document["decision_status"] == "PROPOSED_UNSELECTED_USER_CONFIRMATION_REQUIRED"


def test_candidate_names_exact_four_asset_authority_matrix() -> None:
    policies = {
        entry["asset_id"]: entry for entry in checker.build_document()["asset_policies"]
    }

    assert set(policies) == {"TAU", "ZDEX", "zUSD", "LP_SHARE_RELEASE_DEFINED"}
    assert policies["TAU"]["asset_class"] == "TAU_ORIGINATED_TOKEN"
    assert policies["TAU"]["local_issue_authority"] == "NO_LOCAL_AUTHORITY"
    assert policies["TAU"]["local_burn_authority"] == "NO_LOCAL_AUTHORITY"
    assert policies["ZDEX"]["local_issue_authority"] == (
        "GOVERNANCE_MIGRATION_GENESIS_ONLY"
    )
    assert policies["ZDEX"]["local_burn_authority"] == (
        "ZDEX_TOKENOMICS_EXACT_SOURCE"
    )
    assert policies["zUSD"]["local_issue_authority"] == "ZUSD_MONETARY_KERNEL"
    assert policies["zUSD"]["local_burn_authority"] == "ZUSD_MONETARY_KERNEL"
    assert policies["LP_SHARE_RELEASE_DEFINED"]["local_issue_authority"] == (
        "SPOT_LIQUIDITY_POOL_KERNEL"
    )
    assert policies["LP_SHARE_RELEASE_DEFINED"]["local_burn_authority"] == (
        "SPOT_LIQUIDITY_POOL_KERNEL"
    )


def test_tau_origin_uncertainty_is_a_fail_closed_integration_hold() -> None:
    tau = checker.build_document()["asset_policies"][1]

    assert tau["asset_id"] == "TAU"
    assert tau["availability"] == "TAU_INTEGRATION_HOLD"
    assert tau["entry_rule"] == "VERIFIED_TAU_OCCURRENCE_ADAPTER_REQUIRED"
    assert tau["local_supply_semantics"] == "MIRROR_ONLY_NO_LOCAL_ISSUE_OR_BURN"


def test_automatic_governance_can_only_originate_registered_proposals() -> None:
    boundary = checker.build_document()["automatic_governance_boundary"]

    assert boundary["role"] == "REGISTERED_PROPOSAL_ORIGINATOR"
    assert boundary["direct_issue_authority"] == "ABSENT_BY_CONSTRUCTION"
    assert boundary["direct_burn_authority"] == "ABSENT_BY_CONSTRUCTION"
    assert boundary["profile_activation_authority"] == "ABSENT_BY_CONSTRUCTION"
    assert boundary["settlement_publication_authority"] == "ABSENT_BY_CONSTRUCTION"


def test_python_rust_canonical_candidate_has_one_exact_root_vector() -> None:
    binding = checker.build_document()["canonical_rust_binding"]

    assert binding["status"] == "ONE_EXACT_PYTHON_RUST_GOLDEN_VECTOR"
    assert binding["precision_registry_root"].startswith("0x")
    assert len(binding["precision_registry_root"]) == 66
    assert binding["canonical_bytes_sha256"].startswith("sha256:")
    assert binding["candidate_profile_root"].startswith("0x")
    assert len(binding["candidate_profile_root"]) == 66


def test_authority_mutation_fails_exact_record_check(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["asset_policies"][1]["local_issue_authority"] = "AUTOGOV"
    candidate = tmp_path / "mutated.json"
    candidate.write_bytes(checker._encoded(artifact))

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_authority"] == "NONE"
    assert "artifact differs" in " ".join(report["errors"])


def test_false_selection_fails_exact_record_check(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["decision_status"] = "SELECTED"
    artifact["release_gate"]["activation_eligible"] = True
    candidate = tmp_path / "selected.json"
    candidate.write_bytes(checker._encoded(artifact))

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert report["selected_profile_count"] == 1
    assert report["g1_complete"] is False


def test_duplicate_json_key_fails_closed(tmp_path: Path) -> None:
    candidate = tmp_path / "duplicate.json"
    candidate.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert any("duplicate JSON keys" in error for error in report["errors"])


def test_bound_rust_source_drift_invalidates_artifact(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    for relative in checker.BOUND_PATHS:
        destination = repo / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((checker.REPO_ROOT / relative).read_bytes())
    artifact = checker.build_document(repo)
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(checker._encoded(artifact))
    (repo / checker.RUST_KERNEL_PATH).write_text("tampered\n", encoding="utf-8")

    report = checker.check_artifact(candidate, repo)

    assert report["ok"] is False
    assert "artifact differs" in " ".join(report["errors"])
