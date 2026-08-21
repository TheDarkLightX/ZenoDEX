from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import check_production_readiness_g1_spot_lp_policy_v1 as checker


def _copy_bound_repo(destination: Path) -> None:
    bound_paths = set(checker.BOUND_PATHS) | set(checker.ASSET_AUTHORITY_BOUND_PATHS)
    for relative in bound_paths:
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((checker.REPO_ROOT / relative).read_bytes())

    asset_destination = destination / checker.ASSET_AUTHORITY_ARTIFACT_PATH
    asset_destination.parent.mkdir(parents=True, exist_ok=True)
    asset_destination.write_bytes(
        (checker.REPO_ROOT / checker.ASSET_AUTHORITY_ARTIFACT_PATH).read_bytes()
    )


def test_given_candidate_when_checked_then_policy_remains_unselected() -> None:
    # Arrange / Act
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    # Assert
    assert report["ok"] is True
    assert document["decision_id"] == "spot_lp_fee_dust_withdrawal_policy"
    assert document["decision_status"] == ("PROPOSED_UNSELECTED_USER_CONFIRMATION_REQUIRED")
    assert report["selected_profile_count"] == 0
    assert report["production_authority"] == "NONE"
    assert report["g1_complete"] is False


def test_candidate_closes_fee_share_rounding_and_terminal_obligations() -> None:
    policy = checker.build_document()["spot_lp_policy"]

    assert policy["swap_fee_bps"] == 30
    assert policy["fee_rounding"] == "CEIL_GROSS_INPUT"
    assert policy["protocol_fee_share_bps"] == 0
    assert policy["fee_owner"] == "CURRENT_LP_CLAIMANTS_VIA_POOL_RESERVES"
    assert policy["reserve_ingress"] == "POOL_KERNEL_ONLY"
    assert policy["initial_lp_mint"] == "FLOOR_SQRT_PRODUCT_NO_PERMANENT_LOCK"
    assert policy["withdrawal"] == "PRO_RATA_FLOOR_FINAL_BURN_DRAINS_AND_CLOSES"
    assert policy["residue_owner"] == "REMAINING_LP_CLAIMANTS_THEN_FINAL_BURNER"


def test_differential_vectors_cover_bva_refunds_partial_and_final_close() -> None:
    vectors = checker.build_document()["differential_vectors"]

    fees = [row["expected"]["fee_atoms"] for row in vectors["exact_in"]]
    operations = [row["operation"] for row in vectors["lp_lifecycle"]]
    final = vectors["lp_lifecycle"][-1]["expected"]

    assert 1 in fees
    assert 2 in fees
    assert operations == ["CREATE", "ADD", "ADD", "REMOVE", "REMOVE"]
    rounding_add = vectors["lp_lifecycle"][2]["expected"]
    assert rounding_add["lp_minted_atoms"] == 2
    assert rounding_add["amount0_used_atoms"] == 3
    assert rounding_add["amount1_used_atoms"] == 5
    assert final["terminal_closed"] is True
    assert final["post_pool"] == {
        "lp_supply_atoms": 0,
        "reserve0_atoms": 0,
        "reserve1_atoms": 0,
        "status": "CLOSED",
    }


def test_false_selection_and_fee_mutation_fail_exact_record_check(
    tmp_path: Path,
) -> None:
    # Arrange
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["decision_status"] = "SELECTED"
    artifact["spot_lp_policy"]["swap_fee_bps"] = 31
    artifact["release_gate"]["activation_eligible"] = True
    candidate = tmp_path / "mutated.json"
    candidate.write_bytes(checker._encoded(artifact))

    # Act
    report = checker.check_artifact(candidate)

    # Assert
    assert report["ok"] is False
    assert report["selected_profile_count"] == 1
    assert report["production_authority"] == "NONE"
    assert "artifact differs" in " ".join(report["errors"])


def test_duplicate_json_key_fails_closed(tmp_path: Path) -> None:
    # Arrange
    candidate = tmp_path / "duplicate.json"
    candidate.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    # Act
    report = checker.check_artifact(candidate)

    # Assert
    assert report["ok"] is False
    assert any("duplicate JSON keys" in error for error in report["errors"])


def test_bound_rust_source_drift_invalidates_artifact(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    _copy_bound_repo(repo)
    artifact = checker.build_document(repo)
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(checker._encoded(artifact))
    (repo / checker.RUST_KERNEL_PATH).write_text("tampered\n", encoding="utf-8")

    # Act
    report = checker.check_artifact(candidate, repo)

    # Assert
    assert report["ok"] is False
    assert "artifact differs" in " ".join(report["errors"])


@pytest.mark.parametrize(
    "relative_path",
    [
        checker.CANONICAL_PATH,
        checker.CARGO_MANIFEST_PATH,
        checker.CARGO_LOCK_PATH,
    ],
)
def test_canonicalization_dependency_drift_invalidates_artifact(
    tmp_path: Path,
    relative_path: str,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    _copy_bound_repo(repo)
    artifact = checker.build_document(repo)
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(checker._encoded(artifact))
    (repo / relative_path).write_bytes(b"tampered\n")

    # Act
    report = checker.check_artifact(candidate, repo)

    # Assert
    assert report["ok"] is False
    assert "artifact differs" in " ".join(report["errors"])


def test_malformed_predecessor_root_fails_before_candidate_build(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    _copy_bound_repo(repo)
    asset_path = repo / checker.ASSET_AUTHORITY_ARTIFACT_PATH
    asset = json.loads(asset_path.read_text(encoding="utf-8"))
    asset["canonical_rust_binding"]["candidate_profile_root"] = "0xnot-a-root"
    asset_path.write_bytes(checker._encoded(asset))

    # Act / Assert
    with pytest.raises(ValueError, match="predecessor artifact failed"):
        checker.build_document(repo)
