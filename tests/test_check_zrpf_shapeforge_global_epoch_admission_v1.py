from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

from tools import check_zrpf_shapeforge_global_epoch_admission_v1 as checker


def _contract() -> dict[str, Any]:
    return copy.deepcopy(dict(checker.load_json(checker.DEFAULT_CONTRACT)))


def _artifacts() -> dict[str, dict[str, Any]]:
    return copy.deepcopy(checker.load_artifacts(_contract()))


def test_exact_shape_bridge_is_closed_source_bound_and_unmounted() -> None:
    report = checker.validate_contract(_contract(), _artifacts())

    assert report == {
        "schema": "zenodex/zrpf-shapeforge-global-epoch-admission-check/v1",
        "ok": True,
        "contract_status": "RESEARCH_ONLY_UNMOUNTED",
        "production_authority": False,
        "world_model_id": "zenodex_shape_reference_v3",
        "slice_id": "global_epoch_receipt_admission",
        "slice_status": "contract",
        "implemented_slice_id": "asset_transfer_lane_module_output",
        "implemented_slice_status": "contract",
        "implemented_delta_axis": "operator",
        "managed_lifecycle_slice_id": "managed_asset_lifecycle_lane_module_output",
        "managed_lifecycle_slice_status": "contract",
        "release_route_slice_id": "lane_module_release_route_binding",
        "release_route_slice_status": "contract",
        "release_route_delta_axis": "guard",
        "module_receipt_slice_id": "lane_module_receipt_verification",
        "module_receipt_slice_status": "contract",
        "module_receipt_delta_axis": "evidence",
        "receipt_backed_lane_slice_id": "receipt_backed_asset_lane_composition",
        "receipt_backed_lane_slice_status": "contract",
        "receipt_backed_lane_delta_axis": "evidence",
        "route_composition_slice_id": "route_composition_receipt_verification",
        "route_composition_slice_status": "contract",
        "route_composition_delta_axis": "evidence",
        "axis": "evidence",
        "target_evidence_class": "contract",
        "artifact_count": 5,
        "source_pin_count": 101,
        "errors": [],
        "nonclaim": (
            "the ShapeForge refinement contract does not authenticate or mount a "
            "cryptographic verifier implementation, durable publisher, route, migration, "
            "or production authority"
        ),
    }


def test_production_authority_cannot_be_enabled_by_metadata_edit() -> None:
    contract = _contract()
    contract["production_authority"] = True

    report = checker.validate_contract(contract, _artifacts())

    assert report["ok"] is False
    assert "production_authority must be the JSON boolean false" in report["errors"]


def test_missing_world_model_slice_rejects() -> None:
    artifacts = _artifacts()
    artifacts["world_model"]["slices"] = [
        item
        for item in artifacts["world_model"]["slices"]
        if item["slice_id"] != "global_epoch_receipt_admission"
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "world model must contain exactly one required slice" in " ".join(report["errors"])


def test_scenario_cannot_mix_or_change_the_single_evidence_axis() -> None:
    artifacts = _artifacts()
    scenario = next(
        item
        for item in artifacts["world_model"]["scenario_transforms"]
        if item["scenario_id"] == checker.SCENARIO_ID
    )
    scenario["axis"] = "operator"

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "world-model scenario axis must equal evidence" in report["errors"]


def test_exact_verified_route_witness_guard_cannot_be_dropped() -> None:
    # Arrange
    contract = _contract()
    contract["phi"]["guards"].remove("exact_verified_route_witnesses")

    # Act
    report = checker.validate_contract(contract, _artifacts())

    # Assert
    assert report["ok"] is False
    assert "phi.guards must equal the closed required list" in report["errors"]


def test_exact_route_assumption_root_guard_cannot_be_dropped() -> None:
    contract = _contract()
    contract["phi"]["guards"].remove("exact_route_assumption_roots")

    report = checker.validate_contract(contract, _artifacts())

    assert report["ok"] is False
    assert "phi.guards must equal the closed required list" in report["errors"]


def test_exact_route_effect_plan_aggregation_guard_cannot_be_dropped() -> None:
    # Arrange
    contract = _contract()
    contract["phi"]["guards"].remove("exact_route_effect_plan_aggregation")

    # Act
    report = checker.validate_contract(contract, _artifacts())

    # Assert
    assert report["ok"] is False
    assert "phi.guards must equal the closed required list" in report["errors"]


def test_missing_asset_module_output_slice_rejects() -> None:
    artifacts = _artifacts()
    artifacts["world_model"]["slices"] = [
        item
        for item in artifacts["world_model"]["slices"]
        if item["slice_id"] != checker.ASSET_MODULE_SLICE_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "world model must contain exactly one asset-module output slice" in report["errors"]


def test_missing_managed_lifecycle_output_slice_rejects() -> None:
    artifacts = _artifacts()
    artifacts["world_model"]["slices"] = [
        item
        for item in artifacts["world_model"]["slices"]
        if item["slice_id"] != checker.MANAGED_LIFECYCLE_SLICE_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "world model must contain exactly one managed-lifecycle output slice" in report["errors"]


def test_missing_release_route_binding_slice_rejects() -> None:
    artifacts = _artifacts()
    artifacts["world_model"]["slices"] = [
        item
        for item in artifacts["world_model"]["slices"]
        if item["slice_id"] != checker.RELEASE_ROUTE_SLICE_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "world model must contain exactly one release-route output slice" in report["errors"]


def test_missing_module_receipt_verification_slice_rejects() -> None:
    artifacts = _artifacts()
    artifacts["world_model"]["slices"] = [
        item
        for item in artifacts["world_model"]["slices"]
        if item["slice_id"] != checker.MODULE_RECEIPT_SLICE_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "world model must contain exactly one module-receipt output slice" in report["errors"]


def test_missing_receipt_backed_lane_composition_slice_rejects() -> None:
    artifacts = _artifacts()
    artifacts["world_model"]["slices"] = [
        item
        for item in artifacts["world_model"]["slices"]
        if item["slice_id"] != checker.RECEIPT_BACKED_LANE_SLICE_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert (
        "world model must contain exactly one receipt-backed-lane output slice" in report["errors"]
    )


def test_missing_route_composition_receipt_slice_rejects() -> None:
    # Arrange: remove only the governed route-receipt evidence slice.
    artifacts = _artifacts()
    artifacts["world_model"]["slices"] = [
        item
        for item in artifacts["world_model"]["slices"]
        if item["slice_id"] != checker.ROUTE_COMPOSITION_SLICE_ID
    ]

    # Act: validate the otherwise exact artifact family.
    report = checker.validate_contract(_contract(), artifacts)

    # Assert: the closed implemented-delta registry rejects the omission.
    assert report["ok"] is False
    assert "world model must contain exactly one route-composition output slice" in report["errors"]


def test_synthetic_structural_journal_negative_knowledge_is_required() -> None:
    artifacts = _artifacts()
    artifacts["negative_knowledge"]["records"] = [
        item
        for item in artifacts["negative_knowledge"]["records"]
        if item["hypothesis_id"] != checker.HYPOTHESIS_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "negative knowledge must contain exactly one required hypothesis" in " ".join(
        report["errors"]
    )


def test_host_fixture_rebinding_negative_knowledge_is_required() -> None:
    artifacts = _artifacts()
    artifacts["negative_knowledge"]["records"] = [
        item
        for item in artifacts["negative_knowledge"]["records"]
        if item["hypothesis_id"] != checker.ASSET_MODULE_HYPOTHESIS_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "negative knowledge must contain exactly one asset-module hypothesis" in report["errors"]


def test_managed_lifecycle_rebinding_negative_knowledge_is_required() -> None:
    artifacts = _artifacts()
    artifacts["negative_knowledge"]["records"] = [
        item
        for item in artifacts["negative_knowledge"]["records"]
        if item["hypothesis_id"] != checker.MANAGED_LIFECYCLE_HYPOTHESIS_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert (
        "negative knowledge must contain exactly one managed-lifecycle hypothesis"
        in report["errors"]
    )


def test_occurrence_only_release_route_negative_knowledge_is_required() -> None:
    artifacts = _artifacts()
    artifacts["negative_knowledge"]["records"] = [
        item
        for item in artifacts["negative_knowledge"]["records"]
        if item["hypothesis_id"] != checker.RELEASE_ROUTE_HYPOTHESIS_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert (
        "negative knowledge must contain exactly one release-route hypothesis" in report["errors"]
    )


def test_structural_binding_module_receipt_negative_knowledge_is_required() -> None:
    artifacts = _artifacts()
    artifacts["negative_knowledge"]["records"] = [
        item
        for item in artifacts["negative_knowledge"]["records"]
        if item["hypothesis_id"] != checker.MODULE_RECEIPT_HYPOTHESIS_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert (
        "negative knowledge must contain exactly one module-receipt hypothesis" in report["errors"]
    )


def test_valid_receipt_wrong_lane_journal_negative_knowledge_is_required() -> None:
    artifacts = _artifacts()
    artifacts["negative_knowledge"]["records"] = [
        item
        for item in artifacts["negative_knowledge"]["records"]
        if item["hypothesis_id"] != checker.RECEIPT_BACKED_LANE_HYPOTHESIS_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert (
        "negative knowledge must contain exactly one receipt-backed-lane hypothesis"
        in report["errors"]
    )


def test_valid_lane_witness_wrong_route_journal_negative_knowledge_is_required() -> None:
    # Arrange: delete the exact substitution world that motivates route binding.
    artifacts = _artifacts()
    artifacts["negative_knowledge"]["records"] = [
        item
        for item in artifacts["negative_knowledge"]["records"]
        if item["hypothesis_id"] != checker.ROUTE_COMPOSITION_HYPOTHESIS_ID
    ]

    # Act: validate the incomplete negative frontier.
    report = checker.validate_contract(_contract(), artifacts)

    # Assert: contract promotion cannot silently lose the falsifier.
    assert report["ok"] is False
    assert (
        "negative knowledge must contain exactly one route-composition hypothesis"
        in report["errors"]
    )


def test_development_import_must_mirror_tactic_and_scenario() -> None:
    artifacts = _artifacts()
    artifacts["development_import"]["scenario_seeds"] = [
        item
        for item in artifacts["development_import"]["scenario_seeds"]
        if item["scenario_id"] != checker.CORPUS_SCENARIO_ID
    ]

    report = checker.validate_contract(_contract(), artifacts)

    assert report["ok"] is False
    assert "development import must mirror the required scenario exactly" in report["errors"]


def test_source_hash_drift_rejects() -> None:
    contract = _contract()
    contract["source_pins"][0]["sha256"] = "0" * 64

    report = checker.validate_contract(contract, _artifacts())

    assert report["ok"] is False
    assert "source_pins[0] sha256 mismatch" in " ".join(report["errors"])


def test_duplicate_contract_key_rejects_before_validation(tmp_path: Path) -> None:
    contract_path = tmp_path / "duplicate.json"
    contract_path.write_text(
        '{"schema":"first","schema":"second"}',
        encoding="utf-8",
    )

    try:
        checker.load_json(contract_path)
    except checker.ContractError as exc:
        assert "duplicate JSON key: schema" in str(exc)
    else:  # pragma: no cover - required fail-closed branch
        raise AssertionError("duplicate key was accepted")


def test_cli_report_is_stable_json(capsys: Any) -> None:
    assert checker.main(["--contract", str(checker.DEFAULT_CONTRACT)]) == 0
    report = json.loads(capsys.readouterr().out)

    assert report["ok"] is True
    assert report["slice_id"] == "global_epoch_receipt_admission"
    assert report["implemented_slice_id"] == "asset_transfer_lane_module_output"
    assert report["managed_lifecycle_slice_id"] == "managed_asset_lifecycle_lane_module_output"
    assert report["release_route_slice_id"] == "lane_module_release_route_binding"
    assert report["module_receipt_slice_id"] == "lane_module_receipt_verification"
    assert report["receipt_backed_lane_slice_id"] == "receipt_backed_asset_lane_composition"
    assert report["route_composition_slice_id"] == "route_composition_receipt_verification"
    assert report["production_authority"] is False
