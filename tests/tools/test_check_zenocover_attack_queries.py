from __future__ import annotations

import copy
import json

from tools.check_zenocover_attack_queries import (
    MANIFEST_SCHEMA,
    main,
    validate_zenocover_attack_queries_v0,
)


def _settlement_failure_evidence() -> dict[str, object]:
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
        "max_unsafe_examples": 8,
        "reserve_solvency_manifest": {
            "schema": "zenodex.zenocover.reserve_solvency_manifest.v0",
            "reserve": {
                "asset": "zUSD",
                "balance": 1_000,
                "existing_locked": 0,
                "min_surplus": 300,
            },
            "positions": [
                {
                    "id": "lp-loss-cover-devnet-v1",
                    "status": "active",
                    "bundle_dir": "docs/fire_registry/devnet_v1/lp_loss_cover_v1",
                }
            ],
        },
        "claim_verifier_model": {
            "schema": "zenodex.zenocover.claim_verifier_model.v0",
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
                    "event_evidence": _settlement_failure_evidence(),
                }
            ],
        },
        "reserve_withdrawal_safety": {
            "schema": "zenodex.zenocover.reserve_withdrawal_safety.v0",
            "pool": {
                "reserve_asset": "zUSD",
                "reserve_balance": 1_000,
                "active_liability": 80,
                "pending_claim_window_liability": 500,
                "min_surplus": 300,
            },
            "withdrawal_requests": [
                {
                    "id": "safe-withdrawal",
                    "amount": 100,
                    "cooldown_complete": True,
                    "claim_window_closed": False,
                    "expected_accepted": True,
                    "expected_post_reserve": 900,
                }
            ],
        },
    }


def test_zenocover_attack_queries_accept_composed_safe_manifest() -> None:
    report = validate_zenocover_attack_queries_v0(_manifest())

    assert report["ok"] is True
    assert report["component_status"] == {
        "reserve_solvency": "accepted",
        "claim_verifier": "accepted",
        "reserve_withdrawal": "accepted",
    }
    assert report["consistency"]["facts"]["active_required_collateral"] == 80
    assert report["cross_attack_query_sweep"]["ok"] is True
    assert report["cross_attack_query_sweep"]["checked_cases"] > 0


def test_zenocover_attack_queries_reject_withdrawal_that_starves_worst_claim() -> None:
    manifest = copy.deepcopy(_manifest())
    pool = manifest["reserve_withdrawal_safety"]["pool"]  # type: ignore[index]
    pool["active_liability"] = 80
    pool["pending_claim_window_liability"] = 0
    pool["min_surplus"] = 100

    report = validate_zenocover_attack_queries_v0(manifest)

    assert report["ok"] is False
    examples = report["cross_attack_query_sweep"]["unsafe_examples"]
    assert any(
        example["query"] == "withdraw_then_worst_claim_breaches_policy_reserve_floor"
        for example in examples
    )


def test_zenocover_attack_queries_reject_reserve_balance_mismatch() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["claim_verifier_model"]["policy"]["reserve_available"] = 999  # type: ignore[index]

    report = validate_zenocover_attack_queries_v0(manifest)

    assert report["ok"] is False
    assert "reserve balance must match claim verifier reserve_available" in report["consistency"]["errors"]


def test_zenocover_attack_queries_reject_active_liability_below_replayed_collateral() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["reserve_withdrawal_safety"]["pool"]["active_liability"] = 79  # type: ignore[index]

    report = validate_zenocover_attack_queries_v0(manifest)

    assert report["ok"] is False
    assert (
        "withdrawal active_liability is below reserve-solvency active required collateral"
        in report["consistency"]["errors"]
    )


def test_zenocover_attack_queries_reject_bad_nested_claim_model() -> None:
    manifest = copy.deepcopy(_manifest())
    claim = manifest["claim_verifier_model"]["claims"][0]  # type: ignore[index]
    claim["expected_authorized_payout"] = 91

    report = validate_zenocover_attack_queries_v0(manifest)

    assert report["ok"] is False
    assert "claim verifier component rejected" in report["errors"]


def test_zenocover_attack_queries_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "attack-queries.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zenocover.attack_query_report.v0"
