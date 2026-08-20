from __future__ import annotations

import hashlib
import json
from copy import deepcopy
from pathlib import Path

from tools import check_proof_market_game_theory_v2 as checker
from tools.proof_market_game_theory_checks_v2 import EXPECTED_RESERVE_WORK_KEY_V2

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_PATH = REPO_ROOT / "docs/research/PROOF_MARKET_GAME_THEORY_V2.json"


def _artifact() -> dict[str, object]:
    value = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_saved_artifact_is_exact_checker_output() -> None:
    assert ARTIFACT_PATH.read_bytes() == checker._canonical_bytes(checker._document())


def test_all_source_pins_match_exact_bytes() -> None:
    artifact = _artifact()
    subject = artifact["source_subject"]
    assert isinstance(subject, dict)
    pins = subject["source_pins"]
    assert isinstance(pins, list) and pins
    for pin in pins:
        assert isinstance(pin, dict)
        path = REPO_ROOT / str(pin["path"])
        assert hashlib.sha256(path.read_bytes()).hexdigest() == pin["sha256"]


def test_v1_counterexamples_are_preserved_with_exact_values() -> None:
    artifact = _artifact()
    attacks = artifact["attack_query"]
    assert isinstance(attacks, dict)
    assert attacks["saved_reported_average_payment_atoms"] == 6_624_003
    assert attacks["floor_corrected_average_payment_atoms"] == 6_718_880
    assert attacks["unilateral_wait_average_payment_atoms"] == 8_092_995
    assert attacks["first_attempt_success_bps"] == 9_660
    assert attacks["saved_eligibility_fulfillment_bps"] == 10_000
    assert attacks["saved_collusive_uplift_bps"] == 15_762
    floor_defects = attacks["floor_defects"]
    assert isinstance(floor_defects, list)
    assert [row["scenario_id"] for row in floor_defects] == [
        "LARGE_5_GCYCLE_EFFICIENT",
        "VERY_LARGE_50_GCYCLE_EFFICIENT",
    ]


def test_decision_keeps_market_failure_out_of_settlement_authority() -> None:
    artifact = _artifact()
    decision = artifact["decision"]
    promotion = artifact["promotion_boundary"]
    assert isinstance(decision, dict)
    assert isinstance(promotion, dict)
    assert decision["normal_lane"] == (
        "BENCHMARK_POSTED_PRICE_SEALED_ACCEPT_CAPACITY_TICKET"
    )
    assert decision["terminal_fallback"] == "FUNDED_DIRECT_EXECUTION"
    assert decision["reverse_dutch_default"] == "REJECTED"
    assert decision["critical_price_launch"] == "REJECTED_COALITION_MANIPULATION"
    assert promotion["selected"] is False
    assert promotion["implemented"] is False
    assert promotion["mounted"] is False
    assert promotion["production_ready"] is False


def test_reference_reserve_claim_is_single_consumption_and_scoped() -> None:
    artifact = _artifact()
    bounded_model = artifact["bounded_model"]
    promotion = artifact["promotion_boundary"]
    assert isinstance(bounded_model, dict)
    assert isinstance(promotion, dict)
    reserve = bounded_model["proof_reserve"]
    assert isinstance(reserve, dict)
    encoding = reserve["economic_work_key_encoding"]
    assert isinstance(encoding, dict)
    assert encoding["key"] == EXPECTED_RESERVE_WORK_KEY_V2
    assert encoding["changed_field_changes_key"] is True
    stateful = reserve["stateful_claim"]
    assert isinstance(stateful, dict)
    assert stateful["first_bonus_atoms"] == 60
    assert stateful["economic_work_key"] == EXPECTED_RESERVE_WORK_KEY_V2
    assert stateful["reserve_remaining_after_first_atoms"] == 40
    assert stateful["owner_epoch_remaining_after_first_atoms"] == 20
    assert stateful["claimed_work_keys_after_first"] == [
        EXPECTED_RESERVE_WORK_KEY_V2
    ]
    assert stateful["duplicate_rejection"] == "WORK_KEY_ALREADY_CLAIMED"
    assert stateful["duplicate_was_accepted"] is False
    assert (
        "immutable reserve claim consumes one exact EconomicWorkKey once"
        in promotion["tested_in_reference_subject"]
    )


def test_formal_receipts_and_claim_ceiling_are_fail_closed() -> None:
    artifact = _artifact()
    formal = artifact["formal_evidence"]
    checks = artifact["checks"]
    subject = artifact["source_subject"]
    assert isinstance(formal, dict)
    assert isinstance(checks, dict)
    assert isinstance(subject, dict)
    assert formal["esso"]["result"]["passed_queries"] == 14
    assert formal["esso"]["result"]["failed_queries"] == 0
    assert formal["esso"]["model_pin_matches"] is True
    assert formal["esso"]["verification_report_pin_matches"] is True
    assert formal["esso"]["raw_bundle_result_pin_matches"] is True
    assert formal["esso"]["preserved_report_replays_verified"] is True
    assert formal["esso"]["fault_race_mutant_pins_match"] is True
    assert formal["esso"]["fault_race_mutant_replays_sat"] is True
    assert formal["esso"]["counterexample_ids"][-1] == (
        "PROVER_FAULT_WITNESS_VERIFICATION_RACE"
    )
    assert formal["lean"]["placeholder_hits"] == 0
    assert len(formal["lean"]["compiled_theorems"]) == 8
    assert formal["lean"]["source_pin_matches"] is True
    assert formal["lean"]["root_import_pin_matches"] is True
    assert all(checks.values())
    assert artifact["ok"] is True
    assert subject["checker_bootstrap"]["externally_authenticated"] is False


def test_esso_receipt_binds_reserve_claim_and_updated_replay() -> None:
    receipt_path = (
        REPO_ROOT / "docs/research/PROOF_MARKET_PROCUREMENT_ESSO_V2.json"
    )
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["model"]["esso_ir_hash"].startswith("sha256:6f599e389890")
    assert receipt["result"]["passed_queries"] == 14
    proved = receipt["proved_in_declared_model"]
    assert "proof reserve conserves across remaining and paid reserve units" in proved
    assert (
        "a positive reserve payment requires an eligible verified work claim and a fresh economic work key"
        in proved
    )


def test_tampered_artifact_fails_exact_checker(tmp_path: Path) -> None:
    path = tmp_path / "tampered.json"
    path.write_text("{}\n", encoding="utf-8")
    ok, report = checker._write_or_check(path, False)
    assert ok is False
    assert report["ok"] is False


def test_stale_formal_receipt_source_pin_fails_closed(monkeypatch) -> None:
    original_load = checker.packet.formal._load_json

    def stale_receipt(relative_path: str):
        value = deepcopy(original_load(relative_path))
        if relative_path.endswith("PROCUREMENT_ESSO_V2.json"):
            value["model"]["sha256"] = "0" * 64
        return value

    monkeypatch.setattr(checker.packet.formal, "_load_json", stale_receipt)
    document = checker._document()
    assert document["formal_evidence"]["esso"]["model_pin_matches"] is False
    assert document["checks"]["ESSO_DUAL_SOLVER_VERIFIED"] is False
    assert document["ok"] is False


def test_tampered_preserved_esso_report_fails_closed(monkeypatch) -> None:
    original_load = checker.packet.formal._load_json

    def failed_report(relative_path: str):
        value = deepcopy(original_load(relative_path))
        if relative_path == (
            "docs/research/PROOF_MARKET_PROCUREMENT_ESSO_REPORT_V2.json"
        ):
            value["verdict"] = "FAILED"
        return value

    monkeypatch.setattr(checker.packet.formal, "_load_json", failed_report)
    document = checker._document()
    assert document["formal_evidence"]["esso"][
        "preserved_report_replays_verified"
    ] is False
    assert document["checks"]["ESSO_DUAL_SOLVER_VERIFIED"] is False
    assert document["ok"] is False


def test_failed_lean_replay_receipt_fails_closed(monkeypatch) -> None:
    original_load = checker.packet.formal._load_json

    def failed_receipt(relative_path: str):
        value = deepcopy(original_load(relative_path))
        if relative_path.endswith("GAME_THEORY_LEAN_V2.json"):
            value["replay"]["exit_code"] = 1
        return value

    monkeypatch.setattr(checker.packet.formal, "_load_json", failed_receipt)
    document = checker._document()
    assert document["formal_evidence"]["lean"]["exit_code"] == 1
    assert document["checks"]["LEAN_RESTRICTED_THEOREMS_COMPILED"] is False
    assert document["ok"] is False


def test_primary_source_manifest_url_tamper_fails_closed(monkeypatch) -> None:
    original_load = checker.packet._load_json

    def tampered_manifest(relative_path: str):
        value = deepcopy(original_load(relative_path))
        if relative_path.endswith("PRIMARY_SOURCE_MANIFEST_V2.json"):
            value["sources"][0]["url"] = "https://example.invalid/self-attested"
        return value

    monkeypatch.setattr(checker.packet, "_load_json", tampered_manifest)
    document = checker._document()
    assert (
        document["checks"]["PRIMARY_SOURCE_MANIFEST_IS_EXPLICITLY_ADVISORY"]
        is False
    )
    assert document["ok"] is False


def test_primary_source_manifest_observation_tamper_fails_closed(monkeypatch) -> None:
    original_load = checker.packet._load_json

    def tampered_manifest(relative_path: str):
        value = deepcopy(original_load(relative_path))
        if relative_path.endswith("PRIMARY_SOURCE_MANIFEST_V2.json"):
            value["sources"][0]["exact_observation"] = "self-attested"
        return value

    monkeypatch.setattr(checker.packet, "_load_json", tampered_manifest)
    document = checker._document()
    assert (
        document["checks"]["PRIMARY_SOURCE_MANIFEST_IS_EXPLICITLY_ADVISORY"]
        is False
    )
    assert document["ok"] is False


def test_fallback_semantic_mutant_fails_closed(monkeypatch) -> None:
    def always_unfunded(**_kwargs):
        return checker.packet.model.FallbackAwardV2(
            checker.packet.model.AwardKindV2.UNFUNDED_REJECT,
            None,
            0,
        )

    monkeypatch.setattr(
        checker.packet.model,
        "scarcity_or_direct_award",
        always_unfunded,
    )
    document = checker._document()
    assert document["checks"]["FALLBACK_IS_SAME_CAP_AND_DIRECT_COST_AWARE"] is False
    assert document["ok"] is False
