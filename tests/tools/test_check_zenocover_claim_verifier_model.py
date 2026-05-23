from __future__ import annotations

import copy
import json

from tools.check_zenocover_claim_verifier_model import (
    MANIFEST_SCHEMA,
    main,
    validate_zenocover_claim_verifier_model_v0,
)


def _base_evidence() -> dict[str, object]:
    return {
        "policy_active": True,
        "within_claim_window": True,
        "already_paid": False,
        "exclusion_applies": False,
        "ledger_header_body_bound": True,
        "settlement_replay_ok": True,
        "failure_certificate_valid": True,
        "invariant_breach_confirmed": True,
    }


def _manifest() -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "policy": {
            "settlement_asset": "zUSD",
            "reserve_available": 1_000,
            "min_reserve_after_payout": 300,
            "aggregate_payout_cap": 500,
            "per_claim_cap": 100,
            "verifier_bond": 250,
            "verifier_slash_amount": 150,
            "verifier_future_value_lost": 50,
            "max_invalid_claim_gain": 200,
            "allowed_failure_kinds": [
                "ledger_replay_failure",
                "oracle_policy_failure",
                "proof_metadata_binding_failure",
                "settlement_invariant_failure",
            ],
        },
        "claims": [
            {
                "id": "settlement-failure-1",
                "claim_key": "policy-1:event-1",
                "failure_kind": "settlement_invariant_failure",
                "requested_payout": 120,
                "coverage_limit": 90,
                "loss_amount": 110,
                "expected_authorized_payout": 90,
                "event_evidence": _base_evidence(),
            }
        ],
    }


def test_claim_verifier_accepts_covered_settlement_failure() -> None:
    report = validate_zenocover_claim_verifier_model_v0(_manifest())

    assert report["ok"] is True
    assert report["claims"]["facts"]["aggregate_authorized_payout"] == 90
    assert report["claims"]["items"][0]["facts"]["covered_event"] is True
    assert report["attack_query_sweep"]["ok"] is True
    assert report["attack_query_sweep"]["checked_cases"] > 0


def test_claim_verifier_rejects_invalid_event_with_positive_payout() -> None:
    manifest = copy.deepcopy(_manifest())
    evidence = manifest["claims"][0]["event_evidence"]  # type: ignore[index]
    evidence["invariant_breach_confirmed"] = False

    report = validate_zenocover_claim_verifier_model_v0(manifest)

    assert report["ok"] is False
    assert "expected_authorized_payout mismatch" in report["claims"]["items"][0]["errors"]
    assert report["claims"]["items"][0]["facts"]["computed_authorized_payout"] == 0


def test_claim_verifier_rejects_payout_above_cap() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["claims"][0]["expected_authorized_payout"] = 101  # type: ignore[index]

    report = validate_zenocover_claim_verifier_model_v0(manifest)

    assert report["ok"] is False
    assert "expected_authorized_payout mismatch" in report["claims"]["items"][0]["errors"]
    assert report["claims"]["items"][0]["facts"]["computed_authorized_payout"] == 90


def test_claim_verifier_caps_payout_by_per_claim_cap() -> None:
    manifest = copy.deepcopy(_manifest())
    claim = manifest["claims"][0]  # type: ignore[index]
    claim["requested_payout"] = 150
    claim["coverage_limit"] = 150
    claim["loss_amount"] = 150
    claim["expected_authorized_payout"] = 100

    report = validate_zenocover_claim_verifier_model_v0(manifest)

    assert report["ok"] is True
    assert report["claims"]["items"][0]["facts"]["computed_authorized_payout"] == 100
    assert report["claims"]["facts"]["aggregate_authorized_payout"] == 100


def test_claim_verifier_rejects_duplicate_paid_claim_key() -> None:
    manifest = copy.deepcopy(_manifest())
    duplicate = copy.deepcopy(manifest["claims"][0])  # type: ignore[index]
    duplicate["id"] = "settlement-failure-duplicate"
    manifest["claims"].append(duplicate)  # type: ignore[union-attr]

    report = validate_zenocover_claim_verifier_model_v0(manifest)

    assert report["ok"] is False
    assert report["claims"]["items"][1]["facts"]["duplicate_key_seen"] is True
    assert report["claims"]["items"][1]["facts"]["computed_authorized_payout"] == 0


def test_claim_verifier_rejects_aggregate_cap_excess() -> None:
    manifest = copy.deepcopy(_manifest())
    for index in range(5):
        claim = copy.deepcopy(manifest["claims"][0])  # type: ignore[index]
        claim["id"] = f"settlement-failure-extra-{index}"
        claim["claim_key"] = f"policy-1:event-extra-{index}"
        claim["expected_authorized_payout"] = 90
        manifest["claims"].append(claim)  # type: ignore[union-attr]

    report = validate_zenocover_claim_verifier_model_v0(manifest)

    assert report["ok"] is False
    assert "aggregate authorized payout exceeds aggregate_payout_cap" in report["claims"]["errors"]
    assert report["claims"]["facts"]["aggregate_authorized_payout"] == 540


def test_claim_verifier_rejects_underbonded_verifier_policy() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["policy"]["verifier_slash_amount"] = 100  # type: ignore[index]
    manifest["policy"]["verifier_future_value_lost"] = 50  # type: ignore[index]

    report = validate_zenocover_claim_verifier_model_v0(manifest)

    assert report["ok"] is False
    assert "max_invalid_claim_gain exceeds verifier downside" in report["policy"]["errors"]


def test_claim_verifier_accepts_other_narrow_failure_kinds() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["claims"] = [
        {
            "id": "ledger-replay",
            "claim_key": "policy-1:ledger",
            "failure_kind": "ledger_replay_failure",
            "requested_payout": 50,
            "coverage_limit": 80,
            "loss_amount": 60,
            "expected_authorized_payout": 50,
            "event_evidence": {
                "policy_active": True,
                "within_claim_window": True,
                "already_paid": False,
                "exclusion_applies": False,
                "accepted_header": True,
                "deterministic_replay_ok": False,
                "replay_failure_certificate_valid": True,
            },
        },
        {
            "id": "proof-binding",
            "claim_key": "policy-1:proof",
            "failure_kind": "proof_metadata_binding_failure",
            "requested_payout": 40,
            "coverage_limit": 80,
            "loss_amount": 60,
            "expected_authorized_payout": 40,
            "event_evidence": {
                "policy_active": True,
                "within_claim_window": True,
                "already_paid": False,
                "exclusion_applies": False,
                "accepted_header": True,
                "proof_metadata_present": True,
                "proof_verification_report_ok": True,
                "proof_metadata_binding_ok": False,
            },
        },
        {
            "id": "oracle-policy",
            "claim_key": "policy-1:oracle",
            "failure_kind": "oracle_policy_failure",
            "requested_payout": 30,
            "coverage_limit": 80,
            "loss_amount": 60,
            "expected_authorized_payout": 30,
            "event_evidence": {
                "policy_active": True,
                "within_claim_window": True,
                "already_paid": False,
                "exclusion_applies": False,
                "oracle_policy_id_match": True,
                "oracle_quorum_ok": True,
                "oracle_observation_fresh": True,
                "oracle_policy_violation_confirmed": True,
            },
        },
    ]

    report = validate_zenocover_claim_verifier_model_v0(manifest)

    assert report["ok"] is True
    assert report["claims"]["facts"]["aggregate_authorized_payout"] == 120


def test_claim_verifier_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "claim-verifier.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zenocover.claim_verifier_report.v0"
