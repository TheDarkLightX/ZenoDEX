from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.dex_engine_quote_receipt_sequence_grammar_fuzz import explore_all_targets, explore_target, minimize_case


ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def test_dex_engine_quote_receipt_sequence_direct_paths_are_stable() -> None:
    report = explore_target("direct_quote_receipt_sequence")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 5
    assert report.unique_outcome_count == 5
    assert report.unique_path_count == 5
    assert "ok:pools=2:nonces=aaaaaaaa=1" in labels
    assert "ok:pools=2:nonces=aaaaaaaa=2" in labels
    assert any("invalid quote receipt:" in label and "verifier_error='pool_snapshot_mismatch'" in label for label in labels)
    assert any("missing quote receipt witness:" in label for label in labels)
    assert any("quote receipt hash mismatch:" in label for label in labels)
    assert "DirectSeq->SingleValidAb" in derivations
    assert "DirectSeq->ValidThenIndependentValidCd" in derivations
    assert "DirectSeq->ValidThenStaleSamePool" in derivations
    assert "DirectSeq->ValidThenIndependentMissingWitness" in derivations
    assert "DirectSeq->ValidThenIndependentHashMismatch" in derivations


def test_dex_engine_quote_receipt_sequence_split_paths_are_stable() -> None:
    report = explore_target("split_quote_receipt_sequence")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 3
    assert report.unique_outcome_count == 3
    assert report.unique_path_count == 3
    assert "ok:pools=3:nonces=aaaaaaaa=3" in labels
    assert any("duplicate quote receipt leg binding:" in label for label in labels)
    assert any("incomplete quote receipt leg coverage:" in label for label in labels)
    assert "SplitSeq->WarmupThenSplitValid" in derivations
    assert "SplitSeq->WarmupThenSplitDuplicateLeg" in derivations
    assert "SplitSeq->WarmupThenSplitIncompleteCoverage" in derivations


def test_dex_engine_quote_receipt_sequence_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {"direct_quote_receipt_sequence", "split_quote_receipt_sequence"}
    assert by_name["direct_quote_receipt_sequence"].total_cases == 5
    assert by_name["split_quote_receipt_sequence"].total_cases == 3


def test_dex_engine_quote_receipt_sequence_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/dex_engine_quote_receipt_sequence_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/dex-engine-quote-receipt-sequence-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {
        "direct_quote_receipt_sequence",
        "split_quote_receipt_sequence",
    }


def test_dex_engine_quote_receipt_sequence_minimizer_removes_dead_tail_without_changing_path() -> None:
    witness = minimize_case("direct_quote_receipt_sequence", "DirectSeq->ValidThenStaleSamePoolWithDeadTail")
    assert "invalid quote receipt:" in witness.outcome_label
    assert "verifier_error='pool_snapshot_mismatch'" in witness.outcome_label
    assert witness.path_id == "a2854f791e42c2ee"
    assert witness.original_size == 3570
    assert witness.minimized_size == 2390
    assert witness.original_size > witness.minimized_size
    assert isinstance(witness.payload, dict)
    assert witness.payload["initial"] == "direct"
    steps = witness.payload["steps"]
    assert isinstance(steps, list)
    assert len(steps) == 2


def test_dex_engine_quote_receipt_sequence_minimizer_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [
            sys.executable,
            str(ROOT_DIR / "tools/dex_engine_quote_receipt_sequence_grammar_fuzz.py"),
            "--target",
            "direct_quote_receipt_sequence",
            "--minimize-derivation",
            "DirectSeq->ValidThenStaleSamePoolWithDeadTail",
            "--format",
            "json",
        ],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/dex-engine-quote-receipt-sequence-minimized-witness/v1"
    witness = payload["witness"]
    assert witness["target"] == "direct_quote_receipt_sequence"
    assert witness["derivation"] == "DirectSeq->ValidThenStaleSamePoolWithDeadTail"
    assert "invalid quote receipt:" in witness["outcome_label"]
    assert witness["path_id"] == "a2854f791e42c2ee"
    assert witness["original_size"] == 3570
    assert witness["minimized_size"] == 2390
