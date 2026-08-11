from __future__ import annotations

import copy
from pathlib import Path
from typing import Any

import pytest

from tools import check_m6_global_economic_core_atdd_v1 as contract_checker
from tools import check_m6_global_economic_core_luna_review_v1 as checker

REVIEW_PATH = (
    checker.REPO_ROOT / "docs/research/m6_global_economic_core_luna_completeness_review_v1.json"
)


def _review() -> dict[str, Any]:
    return copy.deepcopy(dict(contract_checker.load_contract(REVIEW_PATH)))


def test_exact_luna_review_packet_is_source_bound_and_fail_closed() -> None:
    report = checker.validate_review(_review())

    assert report == {
        "schema": "zenodex/m6-global-economic-core-luna-completeness-review-check/v1",
        "ok": False,
        "review_schema": "zenodex/m6-global-economic-core-luna-completeness-review/v1",
        "review_status": "RESEARCH_ONLY_REVIEWED_WITH_BLOCKERS",
        "production_promotion": False,
        "source_pin_count": 7,
        "finding_count": 8,
        "required_spec_expansion_count": 11,
        "scope_decision_count": 6,
        "errors": [
            "current_revision.contract_sha256 mismatch: expected=4a05e1e9d82c9b4a806d71b3ed33673e338777c4503bc4489d08fbb81514c6c8, actual=8ea4484eea347e161f2a8da890c8cb4353ea88e0ef9931e8a5f0404b0d1777c0"
        ],
        "nonclaim": "review closure and reproductions do not prove or mount M6",
    }


def test_missing_confirmed_finding_rejects() -> None:
    review = _review()
    review["confirmed_findings"] = review["confirmed_findings"][:-1]

    report = checker.validate_review(review)

    assert report["ok"] is False
    assert "finding IDs must be exactly CE-001 through CE-008" in report["errors"]


def test_unknown_invariant_reference_rejects() -> None:
    review = _review()
    review["confirmed_findings"][0]["affected_requirements"] = ["INV-999"]

    report = checker.validate_review(review)

    assert report["ok"] is False
    assert "unknown invariant IDs: ['INV-999']" in " ".join(report["errors"])


def test_current_model_hash_drift_rejects() -> None:
    review = _review()
    review["current_revision"]["esso_model_sha256"] = "0" * 64

    report = checker.validate_review(review)

    assert report["ok"] is False
    assert "current_revision.esso_model_sha256 mismatch" in " ".join(report["errors"])


def test_required_spec_expansion_cannot_be_dropped() -> None:
    review = _review()
    review["required_spec_expansions"] = review["required_spec_expansions"][:-1]

    report = checker.validate_review(review)

    assert report["ok"] is False
    assert "expansion IDs must be exactly RSE-001 through RSE-011" in report["errors"]


def test_scope_decision_cannot_be_silently_removed() -> None:
    review = _review()
    review["scope_decisions"] = review["scope_decisions"][:-1]

    report = checker.validate_review(review)

    assert report["ok"] is False
    assert "scope_decisions must equal the closed expected feature set" in report["errors"]


def test_review_cannot_enable_production_promotion() -> None:
    review = _review()
    review["production_promotion"] = True

    report = checker.validate_review(review)

    assert report["ok"] is False
    assert "production_promotion must be the JSON boolean false" in report["errors"]


def test_duplicate_review_key_rejects_before_validation(tmp_path: Path) -> None:
    path = tmp_path / "duplicate-review.json"
    path.write_text('{"schema":"one","schema":"two"}', encoding="utf-8")

    with pytest.raises(contract_checker.ContractError, match="duplicate JSON key: schema"):
        contract_checker.load_contract(path)
