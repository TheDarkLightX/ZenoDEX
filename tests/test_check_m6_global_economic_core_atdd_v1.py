from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest

from tools import check_m6_global_economic_core_atdd_v1 as checker

CONTRACT_PATH = checker.REPO_ROOT / "docs/research/m6_global_economic_core_atdd_bdd_v1.json"


def _contract() -> dict[str, Any]:
    return copy.deepcopy(dict(checker.load_contract(CONTRACT_PATH)))


def test_exact_contract_is_closed_and_source_bound() -> None:
    report = checker.validate_contract(_contract())

    assert report == {
        "schema": "zenodex/m6-global-economic-core-atdd-bdd-check/v1",
        "ok": True,
        "contract_schema": "zenodex/m6-global-economic-core-atdd-bdd/v1",
        "contract_status": "RESEARCH_ONLY_DRAFT",
        "production_promotion": False,
        "source_pin_count": 38,
        "workflow_count": 18,
        "scenario_count": 81,
        "errors": [],
        "nonclaim": (
            "structural closure and source binding do not prove economic laws or runtime safety"
        ),
    }


def test_missing_workflow_cannot_preserve_completeness_claim() -> None:
    contract = _contract()
    contract["workflows"] = contract["workflows"][:-1]

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "workflow IDs must be exactly WF-01 through WF-18" in " ".join(report["errors"])


def test_missing_required_scenario_class_rejects() -> None:
    contract = _contract()
    contract["workflows"][0]["scenarios"] = contract["workflows"][0]["scenarios"][:-1]

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "scenario classes differ" in " ".join(report["errors"])


def test_vacuous_scenario_text_cannot_count_as_atdd_evidence() -> None:
    contract = _contract()
    scenario = contract["workflows"][0]["scenarios"][0]
    scenario["given"] = scenario["when"] = scenario["then"] = "x"

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "is vacuous" in " ".join(report["errors"])


def test_unknown_invariant_reference_rejects() -> None:
    contract = _contract()
    contract["workflows"][0]["scenarios"][0]["requirements"] = ["INV-999"]

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "unknown IDs: ['INV-999']" in " ".join(report["errors"])


def test_rejection_invariant_must_declare_both_commit_partitions() -> None:
    contract = _contract()
    rejection = next(item for item in contract["invariants"] if item["id"] == "INV-005")
    rejection["name"] = "reject_is_no_commit"

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert any(
        "name must equal 'rejection_partition'" in error
        for error in report["errors"]
    )


def test_source_hash_drift_rejects() -> None:
    contract = _contract()
    contract["source_pins"][0]["sha256"] = "0" * 64

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "sha256 mismatch" in " ".join(report["errors"])


def test_source_pin_omission_rejects() -> None:
    contract = _contract()
    contract["source_pins"] = [
        pin for pin in contract["source_pins"] if not pin["path"].endswith("m6_core_v1.rs")
    ]

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "source_pins paths must equal the mandatory M6 source set" in report["errors"]


def test_writer_inventory_is_mandatory_source_bound_evidence() -> None:
    contract = _contract()
    contract["source_pins"] = [
        pin
        for pin in contract["source_pins"]
        if pin["path"] not in {
            "tools/check_m6_writer_inventory.py",
            "tools/m6_writer_inventory_manifest_v1.json",
        }
    ]

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "source_pins paths must equal the mandatory M6 source set" in report["errors"]


def test_base_commit_must_match_the_inspected_repository_head() -> None:
    contract = _contract()
    contract["base_commit"] = "0" * 40

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "base_commit must equal current repository HEAD" in " ".join(report["errors"])


def test_tracked_clean_mode_rejects_untracked_promotion_candidate() -> None:
    report = checker.validate_contract(
        _contract(),
        contract_path=CONTRACT_PATH,
        require_tracked_clean=True,
    )

    assert report["ok"] is False
    assert any("untracked paths" in error for error in report["errors"])


def test_production_promotion_cannot_be_enabled_by_metadata_edit() -> None:
    contract = _contract()
    contract["production_promotion"] = True

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "production_promotion must be the JSON boolean false" in report["errors"]


def test_shutdown_extension_must_remain_explicitly_unmounted() -> None:
    contract = _contract()
    contract["workflows"][15]["owner"] = "zusd_shutdown_extension"

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "WF-16 shutdown must remain explicitly unmounted" in report["errors"]


def test_managed_asset_policy_cannot_drop_named_burn_authority() -> None:
    contract = _contract()
    contract["managed_asset_policy"] = contract["managed_asset_policy"][:-1]

    report = checker.validate_contract(contract)

    assert report["ok"] is False
    assert "managed_asset_policy must equal the closed expected asset-class set" in report[
        "errors"
    ]


def test_duplicate_json_key_is_rejected_before_validation(tmp_path: Path) -> None:
    path = tmp_path / "duplicate.json"
    path.write_text(
        '{"schema":"first","schema":"second"}',
        encoding="utf-8",
    )

    with pytest.raises(checker.ContractError, match="duplicate JSON key: schema"):
        checker.load_contract(path)


def test_cli_report_is_stable_json(capsys: pytest.CaptureFixture[str]) -> None:
    assert checker.main(["--contract", str(CONTRACT_PATH)]) == 0
    output = capsys.readouterr().out

    report = json.loads(output)
    assert report["ok"] is True
    assert report["scenario_count"] == 81
