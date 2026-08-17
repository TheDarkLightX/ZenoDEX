from __future__ import annotations

import hashlib
import json
from pathlib import Path

from tools import check_proof_market_calibration_v1 as checker

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_PATH = REPO_ROOT / "docs/research/PROOF_MARKET_CALIBRATION_V1.json"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _artifact() -> dict[str, object]:
    value = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_saved_calibration_is_exact_checker_output() -> None:
    assert ARTIFACT_PATH.read_bytes() == checker._canonical_bytes(checker._document())


def test_every_calibration_source_pin_matches_exact_bytes() -> None:
    artifact = _artifact()
    source_subject = artifact["source_subject"]
    assert isinstance(source_subject, dict)
    pins = source_subject["source_pins"]
    assert isinstance(pins, list) and pins
    for pin in pins:
        assert isinstance(pin, dict)
        assert _sha256((REPO_ROOT / pin["path"]).read_bytes()) == pin["sha256"]


def test_recommendation_is_loss_based_and_preserves_both_capacity_classes() -> None:
    artifact = _artifact()
    recommendation = artifact["recommendation"]
    assert isinstance(recommendation, dict)
    candidate = recommendation["candidate"]
    assert isinstance(candidate, dict)
    assert candidate["policy_id"] == "LOSS_P40000_W25000_F2000_C2000"
    auction = candidate["auction_metrics"]
    capacity = candidate["capacity_metrics"]
    assert isinstance(auction, dict) and isinstance(capacity, dict)
    assert auction["fulfillment_bps"] == 10_000
    assert auction["admitted_late_count"] == 0
    assert auction["average_price_to_reference_bps"] == 15_526
    assert capacity["permissionless_service_bps"] == 8_750
    assert capacity["priority_service_bps"] == 8_094
    assert capacity["utilization_bps"] == 8_250


def test_static_bond_counterexample_is_same_parameter_pair() -> None:
    artifact = _artifact()
    recommendation = artifact["recommendation"]
    assert isinstance(recommendation, dict)
    paired = recommendation["paired_bond_rule_comparison"]
    assert isinstance(paired, dict)
    loss = paired["loss_based"]["auction_metrics"]
    static = paired["static_10x"]["auction_metrics"]
    assert loss["bond_exclusion_bps"] == 166
    assert static["bond_exclusion_bps"] == 1_166
    assert loss["fulfillment_bps"] == 10_000
    assert static["fulfillment_bps"] == 7_500


def test_grid_and_claim_ceiling_remain_closed() -> None:
    artifact = _artifact()
    bounded = artifact["bounded_model"]
    evidence = artifact["evidence_lane"]
    promotion = artifact["promotion_boundary"]
    assert isinstance(bounded, dict)
    assert isinstance(evidence, dict)
    assert isinstance(promotion, dict)
    assert bounded["policy_grid_count"] == 243
    assert len(bounded["policy_rows"]) == 243
    assert evidence["auction_scenario_evaluations"] == 2_916
    assert evidence["capacity_scenario_evaluations"] == 729
    assert promotion["selected"] is False
    assert promotion["mounted"] is False
    assert promotion["production_ready"] is False


def test_source_examples_are_not_promoted_to_live_market_measurements() -> None:
    artifact = _artifact()
    evidence = artifact["evidence_lane"]
    assert isinstance(evidence, dict)
    review = evidence["source_review"]
    assert isinstance(review, dict)
    assert "not measurements" in review["interpretation"]
    assert len(review["primary_sources"]) == 6


def test_tampered_output_fails_exact_checker(tmp_path: Path) -> None:
    tampered = tmp_path / "calibration.json"
    tampered.write_text("{}\n", encoding="utf-8")
    ok, report = checker._write_or_check(tampered, False)
    assert ok is False
    assert report["ok"] is False
