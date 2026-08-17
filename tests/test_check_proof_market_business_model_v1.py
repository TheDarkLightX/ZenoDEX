from __future__ import annotations

import hashlib
import json
from pathlib import Path

from tools import check_proof_market_business_model_v1 as checker

REPO_ROOT = Path(__file__).resolve().parents[1]


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def test_saved_business_model_is_exact_checker_output() -> None:
    expected = checker._canonical_bytes(checker._document())
    actual = (REPO_ROOT / "docs/research/PROOF_MARKET_BUSINESS_MODEL_V1.json").read_bytes()
    assert actual == expected


def test_every_business_model_source_pin_matches_exact_bytes() -> None:
    artifact = json.loads(
        (REPO_ROOT / "docs/research/PROOF_MARKET_BUSINESS_MODEL_V1.json").read_text(
            encoding="utf-8"
        )
    )
    pins = artifact["source_subject"]["source_pins"]
    assert pins
    for pin in pins:
        assert _sha256((REPO_ROOT / pin["path"]).read_bytes()) == pin["sha256"]


def test_bmse_frontier_certificates_are_hash_consistent_and_non_authoritative() -> None:
    receipt = json.loads(
        (REPO_ROOT / "docs/research/PROOF_MARKET_BMSE_EVALUATION_V1.json").read_text(
            encoding="utf-8"
        )
    )
    assert receipt["certificate_ok"] is True
    assert receipt["promotion_boundary"]["selected"] is False
    assert receipt["promotion_boundary"]["production_ready"] is False
    for row in receipt["rows"]:
        certificate = row["certificate"]
        assert _sha256(certificate["payload_json"].encode("utf-8")) == certificate[
            "payload_hash"
        ]


def test_formal_receipts_bind_the_current_model_and_lean_sources() -> None:
    esso_receipt = json.loads(
        (REPO_ROOT / "docs/research/PROOF_MARKET_LIFECYCLE_ESSO_V1.json").read_text(
            encoding="utf-8"
        )
    )
    esso_model = REPO_ROOT / esso_receipt["model"]["path"]
    assert _sha256(esso_model.read_bytes()) == esso_receipt["model"]["sha256"]
    assert esso_receipt["result"]["verdict"] == "VERIFIED"
    assert esso_receipt["result"]["solvers_agreed"] is True
    assert esso_receipt["result"]["total_queries"] == 13
    counterexample_ids = {
        row["id"] for row in esso_receipt["preserved_counterexamples"]
    }
    assert "PAYMENT_WITHOUT_DURABLE_WORK_RECEIPT" in counterexample_ids
    assert "CALLBACK_REDELIVERY_AFTER_COMMITTED_PAYMENT" in counterexample_ids

    lean_receipt = json.loads(
        (REPO_ROOT / "docs/research/PROOF_MARKET_LEAN_EVIDENCE_V1.json").read_text(
            encoding="utf-8"
        )
    )
    assert lean_receipt["replay"]["result"] == "PASS"
    for pin in lean_receipt["source_subject"]["files"]:
        assert _sha256((REPO_ROOT / pin["path"]).read_bytes()) == pin["sha256"]


def test_artifact_preserves_raw_volume_counterexample_and_claim_ceiling() -> None:
    artifact = json.loads(
        (REPO_ROOT / "docs/research/PROOF_MARKET_BUSINESS_MODEL_V1.json").read_text(
            encoding="utf-8"
        )
    )
    game = artifact["bounded_model"]["game_theory"]
    assert game["raw_volume_counterexample_profit_atoms"] > 0
    assert game["contribution_locked_self_dealing_profit_atoms"] <= 0
    assert artifact["promotion_boundary"]["selected"] is False
    assert artifact["promotion_boundary"]["production_ready"] is False


def test_boundless_review_preserves_source_statuses_and_guard_counterexamples() -> None:
    artifact = checker._document()
    review = artifact["external_primary_source_review"]
    findings = {row["id"]: row for row in review["documented_findings"]}
    assert findings["REQUEST_ID_NOT_BOUND_TO_REQUEST_DIGEST"]["source_status"] == (
        "FIXED_IN_REVIEWED_VERSION"
    )
    assert findings["DUPLICATE_CALLBACK_ON_RESUBMITTED_REQUEST_ID"]["source_status"] == (
        "ACKNOWLEDGED_IN_REVIEWED_VERSION"
    )
    assert review["inferences"][0]["claim_ceiling"].startswith("strategic inference")
    pdf_sources = [
        row for row in review["sources"] if "observed_pdf_sha256" in row
    ]
    assert len(pdf_sources) == 4
    assert all(len(row["observed_pdf_sha256"]) == 64 for row in pdf_sources)

    guards = artifact["bounded_model"]["boundless_derived_guards"]
    assert guards["safe_lock_example"]["admissible"] is True
    assert guards["late_lock_counterexample"]["admissible"] is False
    assert guards["underfunded_claims_example"]["residual_burn_atoms"] == 0
    assert guards["protected_capacity_example"]["admissible"] is True
    assert guards["starvation_capacity_counterexample"]["admissible"] is False


def test_settlement_sweep_includes_every_boundless_derived_commit_guard() -> None:
    settlement = checker._document()["bounded_model"]["settlement"]
    assert settlement["exhaustive_boolean_cases"] == 2**14
    assert settlement["duplicate_work_example"]["seller_payment_atoms"] == 0
    assert settlement["duplicate_work_example"]["seller_bond_reprocurement_atoms"] == 10_000


def test_proof_market_projects_the_complete_service_funding_registry() -> None:
    artifact = checker._document()
    funding = artifact["bounded_model"]["protocol_service_funding"]
    assert funding["participant_count"] == 22
    assert funding["budget_eligible_role_count"] == 12
    assert funding["selected_budget_count"] == 0
    assert len(funding["participant_funding_registry"]) == 22
    assert set(funding["selected_role_budgets"]) == set(
        funding["allowed_funding_sources"]
    )
    assert all(value is None for value in funding["selected_role_budgets"].values())
