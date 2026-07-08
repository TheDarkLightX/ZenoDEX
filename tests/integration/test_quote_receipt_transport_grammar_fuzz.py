from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.quote_receipt_transport_grammar_fuzz import (
    explore_all_targets,
    explore_target,
    minimize_case,
)

ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def test_quote_receipt_transport_grammar_fuzz_transport_discovers_stable_boundary_paths() -> None:
    report = explore_target("quote_receipt_transport")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 12
    assert report.unique_outcome_count == 12
    assert report.unique_path_count == 12
    assert "reject:bad_receipt_type" in labels
    assert "reject:missing_body" in labels
    assert "reject:bad_schema" in labels
    assert "reject:missing_receipt_hash" in labels
    assert "reject:hash_mismatch" in labels
    assert "reject:bad_kind" in labels
    assert "reject:unexpected_canonical_route_certificate" in labels
    assert "reject:bad_body_assets" in labels
    assert "reject:bad_quote_epoch" in labels
    assert "reject:bad_pools" in labels
    assert "reject:bad_legs" in labels
    assert "ok" in labels
    assert derivations == {
        "QuoteReceipt->ExactOut ; Body->BadBodyAssets",
        "QuoteReceipt->ExactOut ; Body->BadKind",
        "QuoteReceipt->ExactOut ; Body->BadLegsShape",
        "QuoteReceipt->ExactOut ; Body->BadPoolsShape",
        "QuoteReceipt->ExactOut ; Body->BadQuoteEpoch",
        "QuoteReceipt->ExactOut ; Body->BadSchema",
        "QuoteReceipt->ExactOut ; Body->UnexpectedCanonicalCertificate",
        "QuoteReceipt->ExactOut ; ReceiptHash->Mismatch",
        "QuoteReceipt->ExactOut ; ReceiptHash->Missing",
        "QuoteReceipt->MissingBody",
        "QuoteReceipt->NonDict",
        "repair:receipt->restore-valid-exact-out",
    }


def test_quote_receipt_transport_grammar_fuzz_exact_in_certificate_discovers_stable_boundary_paths() -> None:
    report = explore_target("quote_receipt_exact_in_certificate")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 5
    assert report.unique_outcome_count == 4
    assert report.unique_path_count == 3
    assert "ok" in labels
    assert "reject:bad_canonical_route_certificate:certificate payload mismatch" in labels
    assert "reject:bad_canonical_route_certificate:certificate payload must be a dict" in labels
    assert "reject:bad_canonical_route_certificate:certificate payload must include non-empty candidates" in labels
    assert derivations == {
        "QuoteReceiptExactIn->Valid",
        "QuoteReceiptExactIn->TamperedCanonicalCertificate",
        "QuoteReceiptExactIn->CertificateWrongType",
        "QuoteReceiptExactIn->CertificateMissingWinnerQuote",
        "repair:cert->drop-canonical-certificate",
    }


def test_quote_receipt_transport_grammar_fuzz_all_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {"quote_receipt_transport", "quote_receipt_exact_in_certificate"}
    assert by_name["quote_receipt_transport"].total_cases == 12
    assert by_name["quote_receipt_exact_in_certificate"].total_cases == 5


def test_quote_receipt_transport_grammar_fuzz_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/quote_receipt_transport_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/quote-receipt-transport-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {
        "quote_receipt_transport",
        "quote_receipt_exact_in_certificate",
    }


def test_quote_receipt_transport_minimizer_removes_dead_blob_without_changing_path() -> None:
    witness = minimize_case("quote_receipt_transport", "QuoteReceipt->ExactOut ; ReceiptHash->MissingWithDeadBlob")
    assert witness.outcome_label == "reject:missing_receipt_hash"
    assert witness.path_id == "931507be994d2628"
    assert witness.original_size > witness.minimized_size
    assert witness.original_size == 741
    assert witness.minimized_size == 104
    assert isinstance(witness.payload, tuple)
    receipt, pools = witness.payload
    assert isinstance(receipt, dict)
    assert isinstance(pools, dict)
    assert pools == {}
    assert sorted(receipt) == ["body"]
    assert sorted(receipt["body"]) == ["asset_in", "asset_out", "quote_epoch", "schema"]


def test_quote_receipt_transport_minimizer_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [
            sys.executable,
            str(ROOT_DIR / "tools/quote_receipt_transport_grammar_fuzz.py"),
            "--target",
            "quote_receipt_transport",
            "--minimize-derivation",
            "QuoteReceipt->ExactOut ; ReceiptHash->MissingWithDeadBlob",
            "--format",
            "json",
        ],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/quote-receipt-transport-minimized-witness/v1"
    witness = payload["witness"]
    assert witness["target"] == "quote_receipt_transport"
    assert witness["derivation"] == "QuoteReceipt->ExactOut ; ReceiptHash->MissingWithDeadBlob"
    assert witness["outcome_label"] == "reject:missing_receipt_hash"
    assert witness["path_id"] == "931507be994d2628"
    assert witness["original_size"] > witness["minimized_size"]
    assert witness["original_size"] == 741
    assert witness["minimized_size"] == 104
