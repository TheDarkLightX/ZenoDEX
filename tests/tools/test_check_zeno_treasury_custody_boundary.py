from __future__ import annotations

import copy
import json

from tools.check_zeno_treasury_custody_boundary import (
    MANIFEST_SCHEMA,
    main,
    validate_treasury_custody_boundary_v0,
)


def _manifest() -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "status": "internal_research_only",
        "public_claims_allowed": False,
        "counsel_review_required": True,
        "counsel_review_status": "required_not_complete",
        "tau_net_multisig_wallet_maturity": "unproven",
        "full_treasury_live_funding_allowed": False,
        "custody_params": {
            "total_treasury_allocation_token": 250_000_000,
            "max_live_treasury_wallet_token": 5_000_000,
            "max_single_disbursement_token": 1_000_000,
            "max_epoch_disbursement_token": 2_000_000,
            "signer_count": 7,
            "signer_threshold": 5,
            "timelock_hours": 48,
            "emergency_freeze_threshold": 2,
            "key_rotation_days": 180,
        },
        "controls": [
            "threshold_multisig_or_threshold_signature",
            "independent_signers",
            "signer_geographic_separation",
            "hardware_or_hardened_signing",
            "transaction_simulation",
            "timelock",
            "spending_caps",
            "dual_control_release",
            "emergency_freeze",
            "signer_rotation",
            "audit_log",
            "no_demo_keys",
            "no_single_key_treasury",
            "staged_funding",
        ],
        "attack_queries": [
            {
                "id": "single_signer_compromise",
                "condition": "one signer can move funds alone",
                "mitigation": "strict-majority threshold signing",
                "expected_result": "rejected",
            },
            {
                "id": "wallet_software_bug",
                "condition": "wallet signs or displays the wrong transaction",
                "mitigation": "simulation, previews, caps, staged funding",
                "expected_result": "bounded",
            },
            {
                "id": "social_engineering",
                "condition": "signers approve a malicious transfer",
                "mitigation": "timelock and out-of-band review",
                "expected_result": "bounded",
            },
            {
                "id": "governance_capture",
                "condition": "governance attempts to drain treasury",
                "mitigation": "timelock, caps, emergency freeze",
                "expected_result": "bounded",
            },
            {
                "id": "hot_wallet_drain",
                "condition": "live treasury wallet is compromised",
                "mitigation": "max live wallet cap",
                "expected_result": "bounded",
            },
            {
                "id": "signer_collusion",
                "condition": "threshold signer coalition signs an unauthorized transfer",
                "mitigation": "independent signers, timelock, audit log",
                "expected_result": "bounded",
            },
            {
                "id": "immature_tau_wallet_dependency",
                "condition": "Tau Net threshold wallet tooling is not production proven",
                "mitigation": "full treasury live funding disabled",
                "expected_result": "bounded",
            },
        ],
        "promotion_boundary": {
            "public_claim_allowed": False,
            "claim_registry_entry_allowed": False,
            "non_claims": [
                "no_tau_net_multisig_maturity_claim",
                "no_public_treasury_launch_readiness",
                "no_custody_security_complete",
                "no_legal_clearance",
                "no_single_wallet_full_treasury",
            ],
        },
    }


def test_treasury_custody_boundary_accepts_conservative_internal_model() -> None:
    report = validate_treasury_custody_boundary_v0(_manifest())

    assert report["ok"] is True
    assert report["facts"]["tau_net_multisig_wallet_maturity"] == "unproven"
    assert report["facts"]["full_treasury_live_funding_allowed"] is False
    assert report["facts"]["signer_count"] == 7
    assert report["facts"]["signer_threshold"] == 5
    assert report["facts"]["max_live_treasury_wallet_token"] == 5_000_000


def test_treasury_custody_boundary_rejects_full_funding_when_tau_wallet_unproven() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["full_treasury_live_funding_allowed"] = True

    report = validate_treasury_custody_boundary_v0(manifest)

    assert report["ok"] is False
    assert "full live treasury funding requires production-ready Tau Net threshold custody" in report["errors"]


def test_treasury_custody_boundary_rejects_live_wallet_above_two_percent() -> None:
    manifest = copy.deepcopy(_manifest())
    params = manifest["custody_params"]
    assert isinstance(params, dict)
    params["max_live_treasury_wallet_token"] = 5_000_001

    report = validate_treasury_custody_boundary_v0(manifest)

    assert report["ok"] is False
    assert (
        "max_live_treasury_wallet_token must be <= 2% of treasury allocation while custody is unproven"
        in report["custody_params"]["errors"]
    )


def test_treasury_custody_boundary_allows_larger_live_wallet_only_when_production_ready() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["tau_net_multisig_wallet_maturity"] = "production_ready"
    manifest["full_treasury_live_funding_allowed"] = True
    params = manifest["custody_params"]
    assert isinstance(params, dict)
    params["max_live_treasury_wallet_token"] = 10_000_000

    report = validate_treasury_custody_boundary_v0(manifest)

    assert report["ok"] is True
    assert report["facts"]["tau_net_multisig_wallet_maturity"] == "production_ready"


def test_treasury_custody_boundary_rejects_non_majority_threshold() -> None:
    manifest = copy.deepcopy(_manifest())
    params = manifest["custody_params"]
    assert isinstance(params, dict)
    params["signer_threshold"] = 3

    report = validate_treasury_custody_boundary_v0(manifest)

    assert report["ok"] is False
    assert "signer_threshold must be strict majority of signer_count" in report["custody_params"]["errors"]


def test_treasury_custody_boundary_rejects_missing_immature_tau_wallet_query() -> None:
    manifest = copy.deepcopy(_manifest())
    queries = manifest["attack_queries"]
    assert isinstance(queries, list)
    queries[:] = [query for query in queries if query["id"] != "immature_tau_wallet_dependency"]

    report = validate_treasury_custody_boundary_v0(manifest)

    assert report["ok"] is False
    assert "attack_queries rejected" in report["errors"]
    assert report["attack_queries"]["facts"]["missing_required_attack_queries"] == [
        "immature_tau_wallet_dependency"
    ]


def test_treasury_custody_boundary_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "treasury-custody.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"].endswith("treasury_custody_boundary_report.v0")
