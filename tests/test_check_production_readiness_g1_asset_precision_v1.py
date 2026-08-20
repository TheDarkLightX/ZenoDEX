from __future__ import annotations

import json
from pathlib import Path

from tools import check_production_readiness_g1_asset_precision_v1 as checker


def test_given_selected_e8_record_when_checked_then_authority_stays_closed() -> None:
    # Arrange / Act
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    # Assert
    assert report["ok"] is True
    assert report["target_common_decimals"] == 8
    assert report["production_authority"] == "NONE"
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["activation_eligible"] is False
    assert document["release_gate"]["launch_allowed"] is False


def test_e8_successor_preserves_whole_supply_and_recomputes_atoms() -> None:
    selected = checker.build_document()["selected_precision"]

    assert selected["target_unit_scale"] == 100_000_000
    assert selected["whole_zdex_supply"] == 2_000_000_000
    assert selected["zdex_genesis_supply_atoms"] == 200_000_000_000_000_000
    assert selected["zdex_supply_ceiling_atoms"] == selected["zdex_genesis_supply_atoms"]
    assert selected["launch_active_floor_atoms"] == 20_000_000_000_000_000
    assert selected["scale_change_rule"] == (
        "NEW_ASSET_IDENTITY_OR_PROVED_FORWARD_MIGRATION_ONLY"
    )


def test_tau_profiles_keep_current_compatibility_separate_from_bv64_target() -> None:
    tau = checker.build_document()["managed_asset_profiles"][0]

    assert tau["asset_id"] == "TAU"
    assert tau["current_testnet_adapter"]["source_decimals"] == 4
    assert tau["current_testnet_adapter"]["amount_width_bits"] == 24
    assert tau["target_profile"]["source_decimals"] == 8
    assert tau["target_profile"]["amount_width_bits"] == 64
    assert "CONDITIONAL" in tau["target_profile"]["status"]


def test_automatic_governance_has_no_scale_or_publication_authority() -> None:
    boundary = checker.build_document()["automatic_governance_boundary"]

    assert boundary["classification"] == "TYPED_COMMAND_ORIGINATOR_NOT_AN_ASSET"
    assert "SETTLEMENT_PUBLICATION_AUTHORITY" in boundary["may_not_hold"]
    assert "IN_PLACE_SCALE_REINTERPRETATION_AUTHORITY" in boundary["may_not_hold"]
    assert boundary["status"] == "OPEN_SEMANTICS_REQUIRED_BEFORE_MOUNTING"


def test_historical_e18_dependents_are_explicitly_profile_inapplicable() -> None:
    dependents = checker.build_document()["historical_e18_dependents"]

    assert dependents["status"] == (
        "HISTORICAL_E18_NOT_APPLICABLE_TO_CURRENT_E8_PROFILE"
    )
    assert tuple(dependents["paths"]) == checker.HISTORICAL_E18_DEPENDENTS
    assert all((checker.REPO_ROOT / path).is_file() for path in dependents["paths"])


def test_mutated_scale_fails_exact_record_check(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["selected_precision"]["target_common_decimals"] = 18
    candidate = tmp_path / "mutated.json"
    candidate.write_bytes(checker._encoded(artifact))

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_authority"] == "NONE"
    assert "artifact differs" in " ".join(report["errors"])


def test_duplicate_json_key_fails_closed(tmp_path: Path) -> None:
    candidate = tmp_path / "duplicate.json"
    candidate.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert any("duplicate JSON keys" in error for error in report["errors"])


def test_bound_rust_source_drift_invalidates_artifact(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    for relative in (
        checker.PREDECESSOR_PATH,
        checker.RUST_KERNEL_PATH,
        checker.RUST_EXPORT_PATH,
        checker.RUST_TEST_PATH,
        checker.CHECKER_PATH,
        checker.CHECKER_TEST_PATH,
        *checker.HISTORICAL_E18_DEPENDENTS,
    ):
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
