from __future__ import annotations

import copy
import json

from tools.check_zenodex_batch_proof_coverage import (
    DEFAULT_MANIFEST,
    main,
    validate_batch_proof_coverage_v0,
)


def _manifest() -> dict[str, object]:
    return json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))


def _gap_lane(manifest: dict[str, object], proof_gap_id: str) -> dict[str, object]:
    lanes = manifest["proof_gap_batch_lanes"]
    assert isinstance(lanes, list)
    for lane in lanes:
        assert isinstance(lane, dict)
        if lane.get("proof_gap_id") == proof_gap_id:
            return lane
    raise AssertionError(f"missing gap lane {proof_gap_id}")


def test_batch_proof_coverage_accepts_default_manifest() -> None:
    report = validate_batch_proof_coverage_v0(_manifest())

    assert report["ok"] is True
    assert report["supported_lane_count"] == 1
    assert report["proof_gap_lane_count"] == 7
    assert report["missing_gap_lanes"] == []
    assert "uniform_batch_upba_v2_v3_real_proof" in report["covered_gap_ids"]


def test_batch_proof_coverage_rejects_missing_gap_lane() -> None:
    manifest = _manifest()
    lanes = list(manifest["proof_gap_batch_lanes"])  # type: ignore[arg-type]
    manifest["proof_gap_batch_lanes"] = [
        lane for lane in lanes if lane["proof_gap_id"] != "zusd_lifecycle_real_proof"  # type: ignore[index]
    ]

    report = validate_batch_proof_coverage_v0(manifest)

    assert report["ok"] is False
    assert "zusd_lifecycle_real_proof" in report["missing_gap_lanes"]
    assert any("missing proof_gap_batch_lanes" in err for err in report["errors"])


def test_batch_proof_coverage_rejects_production_ready_gap_claim() -> None:
    manifest = _manifest()
    lane = copy.deepcopy(_gap_lane(manifest, "perps_settlement_real_proof"))
    lane["status"] = "production_ready"
    lanes = list(manifest["proof_gap_batch_lanes"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(lanes) if item["proof_gap_id"] == lane["proof_gap_id"])  # type: ignore[index]
    lanes[index] = lane
    manifest["proof_gap_batch_lanes"] = lanes

    report = validate_batch_proof_coverage_v0(manifest)

    assert report["ok"] is False
    assert any("status must be open_real_proof_gap" in err for err in report["errors"])


def test_batch_proof_coverage_rejects_missing_public_input_field() -> None:
    manifest = _manifest()
    lane = copy.deepcopy(_gap_lane(manifest, "uniform_batch_upba_v2_v3_real_proof"))
    lane["public_input_fields"] = [
        field for field in lane["public_input_fields"] if field != "transition_batch_root"  # type: ignore[index]
    ]
    lanes = list(manifest["proof_gap_batch_lanes"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(lanes) if item["proof_gap_id"] == lane["proof_gap_id"])  # type: ignore[index]
    lanes[index] = lane
    manifest["proof_gap_batch_lanes"] = lanes

    report = validate_batch_proof_coverage_v0(manifest)

    assert report["ok"] is False
    assert any("public_input_fields missing: transition_batch_root" in err for err in report["errors"])


def test_batch_proof_coverage_rejects_prover_trust_boundary() -> None:
    manifest = _manifest()
    boundary = copy.deepcopy(manifest["claim_boundary"])
    assert isinstance(boundary, dict)
    boundary["provers_are_untrusted"] = False
    manifest["claim_boundary"] = boundary

    report = validate_batch_proof_coverage_v0(manifest)

    assert report["ok"] is False
    assert "claim_boundary.provers_are_untrusted must be true" in report["errors"]


def test_batch_proof_coverage_rejects_missing_fail_closed_rule() -> None:
    manifest = _manifest()
    policy = copy.deepcopy(manifest["fail_closed_policy"])
    assert isinstance(policy, dict)
    policy["proof_required_profile_rejects_missing_proof"] = False
    manifest["fail_closed_policy"] = policy

    report = validate_batch_proof_coverage_v0(manifest)

    assert report["ok"] is False
    assert "fail_closed_policy.proof_required_profile_rejects_missing_proof must be true" in report["errors"]


def test_batch_proof_coverage_rejects_public_hardware_details() -> None:
    manifest = _manifest()
    lane = copy.deepcopy(_gap_lane(manifest, "proof_market_reward_real_proof"))
    gate = dict(lane["performance_gate"])  # type: ignore[arg-type]
    gate["allows_private_hardware_details_public"] = True
    lane["performance_gate"] = gate
    lanes = list(manifest["proof_gap_batch_lanes"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(lanes) if item["proof_gap_id"] == lane["proof_gap_id"])  # type: ignore[index]
    lanes[index] = lane
    manifest["proof_gap_batch_lanes"] = lanes

    report = validate_batch_proof_coverage_v0(manifest)

    assert report["ok"] is False
    assert any("allows_private_hardware_details_public must be false" in err for err in report["errors"])


def test_batch_proof_coverage_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "batch_proof_coverage.json"
    manifest_path.write_text(json.dumps(_manifest(), indent=2, sort_keys=True), encoding="utf-8")

    code = main(["--manifest", str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["schema"] == "zenodex.batch_proof_coverage_report.v0"
    assert report["ok"] is True
