from __future__ import annotations

import copy
import json
from pathlib import Path

from tools.check_covered_user_interface_boundary import (
    MANIFEST_SCHEMA,
    main,
    validate_covered_user_interface_boundary_v0,
)
from tools.covered_ui_lint import RULES


def _manifest(tmp_path: Path) -> dict[str, object]:
    ui_dir = tmp_path / "ui"
    ui_dir.mkdir()
    (ui_dir / "README.md").write_text("Wallet users sign prepared transactions.\n", encoding="utf-8")
    return {
        "schema": MANIFEST_SCHEMA,
        "status": "internal_boundary_only",
        "public_claims_allowed": False,
        "activation_allowed": False,
        "counsel_review_required": True,
        "legal_review_complete": False,
        "ui_paths": [str(ui_dir)],
        "controls": [
            "self_custody_wallet_signing",
            "no_ui_investment_recommendations",
            "objective_route_and_price_labels",
            "no_specific_transaction_solicitation",
            "no_custody_or_fund_control",
            "no_order_flow_or_affiliate_bias",
            "covered_ui_lint_strict",
            "public_claim_scope_gate",
            "counsel_review_required",
        ],
        "non_claims": [
            "broker_dealer_registration_clearance",
            "securities_law_clearance",
            "investment_advice",
            "custody_or_fund_control",
            "transaction_recommendations",
            "public_launch_readiness",
        ],
        "lint_policy": {
            "strict": True,
            "max_findings": 0,
            "required_rule_ids": [rule.rule_id for rule in RULES],
        },
        "promotion_boundary": {
            "public_launch_allowed": False,
            "claim_registry_entry_allowed": False,
            "requires_external_legal_review": True,
            "blockers": [
                "external_counsel_review_not_complete",
                "covered_ui_lint_must_remain_clean",
                "public_claim_scope_must_remain_non_advisory",
            ],
        },
    }


def test_covered_user_interface_boundary_accepts_clean_manifest(tmp_path: Path) -> None:
    report = validate_covered_user_interface_boundary_v0(_manifest(tmp_path))

    assert report["ok"] is True
    assert report["facts"]["finding_count"] == 0


def test_covered_user_interface_boundary_rejects_public_claims(tmp_path: Path) -> None:
    manifest = _manifest(tmp_path)
    manifest["public_claims_allowed"] = True

    report = validate_covered_user_interface_boundary_v0(manifest)

    assert report["ok"] is False
    assert "public_claims_allowed must be false" in report["errors"]


def test_covered_user_interface_boundary_rejects_missing_control(tmp_path: Path) -> None:
    manifest = _manifest(tmp_path)
    controls = manifest["controls"]
    assert isinstance(controls, list)
    controls.remove("no_ui_investment_recommendations")

    report = validate_covered_user_interface_boundary_v0(manifest)

    assert report["ok"] is False
    assert "controls rejected" in report["errors"]


def test_covered_user_interface_boundary_rejects_lint_finding(tmp_path: Path) -> None:
    manifest = _manifest(tmp_path)
    ui_path = Path(str(manifest["ui_paths"][0]))  # type: ignore[index]
    (ui_path / "bad.md").write_text("Recommended route for best execution.\n", encoding="utf-8")

    report = validate_covered_user_interface_boundary_v0(manifest)

    assert report["ok"] is False
    assert "covered_ui_lint rejected" in report["errors"]
    assert report["lint"]["facts"]["finding_count"] >= 1


def test_covered_user_interface_boundary_rejects_missing_rule(tmp_path: Path) -> None:
    manifest = _manifest(tmp_path)
    policy = manifest["lint_policy"]
    assert isinstance(policy, dict)
    policy["required_rule_ids"] = [rule.rule_id for rule in RULES[:-1]]

    report = validate_covered_user_interface_boundary_v0(manifest)

    assert report["ok"] is False
    assert "lint_policy rejected" in report["errors"]


def test_covered_user_interface_boundary_cli(tmp_path: Path, capsys) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps(_manifest(tmp_path)), encoding="utf-8")

    rc = main([str(manifest_path)])

    assert rc == 0
    out = json.loads(capsys.readouterr().out)
    assert out["schema"] == "zenodex.covered_user_interface_boundary_report.v0"
    assert out["ok"] is True


def test_covered_user_interface_boundary_rejects_bad_promotion(tmp_path: Path) -> None:
    manifest = copy.deepcopy(_manifest(tmp_path))
    promo = manifest["promotion_boundary"]
    assert isinstance(promo, dict)
    promo["public_launch_allowed"] = True

    report = validate_covered_user_interface_boundary_v0(manifest)

    assert report["ok"] is False
    assert "promotion_boundary rejected" in report["errors"]
