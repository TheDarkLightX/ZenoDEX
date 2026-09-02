from __future__ import annotations

from pathlib import Path

import yaml


REPO_ROOT = Path(__file__).resolve().parents[2]
CAL_PACKAGE = REPO_ROOT / "docs" / "papers" / "fire-certified-financial-objects" / "cal_fire_logic_package"


def test_cal_fire_logic_package_names_full_receipt_binding_tuple() -> None:
    required_terms = {
        "receipt.object_hash",
        "receipt.instance_hash",
        "receipt.cert_sha256",
        "receipt.witness_hash",
        "receipt.delta_hash",
        "DeltaConservationOK",
    }
    for relative_path in ("spec/CAL_v0.1_Spec.md", "spec/CAL_FireLogic_Book.md"):
        text = (CAL_PACKAGE / relative_path).read_text(encoding="utf-8")
        assert "FIREVReceiptOK(receipt) :=" in text
        for term in required_terms:
            assert term in text


def test_cal_fire_logic_package_stdlib_has_settlement_receipt_binding_rule() -> None:
    payload = yaml.safe_load((CAL_PACKAGE / "stdlib" / "cal_stdlib_rules.yaml").read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    rules = payload.get("rules")
    assert isinstance(rules, list)
    by_id = {rule["id"]: rule for rule in rules if isinstance(rule, dict) and "id" in rule}

    rule = by_id["settlement_authority_receipt_binding"]
    assert rule["kind"] == "settlement"
    assert rule["conclusion"] == {"predicate": "FIREVReceiptOK"}
    premises = rule["premises"]
    assert {"receipt_object_hash_matches_object": True} in premises
    assert {"receipt_instance_hash_matches_instance": True} in premises
    assert {"receipt_cert_sha256_matches_certificate": True} in premises
    assert {"receipt_witness_hash_matches_witness_bundle": True} in premises
    assert {"receipt_delta_hash_matches_delta": True} in premises
    assert {"receipt_delta_conservation_ok": True} in premises
    assert {"verifier_receipt_hash_valid": True} in premises

    reject_if = set(rule["reject_if"])
    assert {
        "object_hash_mismatch",
        "instance_hash_mismatch",
        "cert_sha256_mismatch",
        "witness_hash_mismatch",
        "delta_hash_mismatch",
        "delta_nonzero_sum",
        "receipt_hash_mismatch",
    }.issubset(reject_if)
