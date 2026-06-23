from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.dex_engine_settlement_sequence_grammar_fuzz import explore_all_targets, explore_target, minimize_case


ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def test_dex_engine_settlement_sequence_grammar_fuzz_discovers_stateful_settlement_paths() -> None:
    report = explore_target("dex_engine_settlement_sequence")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 6
    assert report.unique_outcome_count == 6
    assert report.unique_path_count == 6
    assert "ok:pools=2:nonces=aaaaaaaa=1" in labels
    assert "ok:pools=2:nonces=aaaaaaaa=2" in labels
    assert "reject:step=1:missing settlement" in labels
    assert "reject:step=1:settlement mismatch" in labels
    assert "reject:step=1:settlement provided without intents" in labels
    assert "reject:step=1:too many settlement fills: 2 > 1" in labels
    assert "SettlementSeq->SingleProvidedAb" in derivations
    assert "SettlementSeq->WarmupThenStatefulProvidedAb" in derivations
    assert "SettlementSeq->WarmupThenStaleProvidedAb" in derivations
    assert "SettlementSeq->WarmupThenMissingSettlementRequired" in derivations
    assert "SettlementSeq->WarmupThenSettlementWithoutIntents" in derivations
    assert "SettlementSeq->WarmupThenTooManySettlementFills" in derivations


def test_dex_engine_settlement_sequence_grammar_fuzz_all_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {"dex_engine_settlement_sequence"}
    assert by_name["dex_engine_settlement_sequence"].total_cases == 6


def test_dex_engine_settlement_sequence_grammar_fuzz_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/dex_engine_settlement_sequence_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/dex-engine-settlement-sequence-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {"dex_engine_settlement_sequence"}


def test_dex_engine_settlement_sequence_minimizer_preserves_stale_settlement_reject() -> None:
    witness = minimize_case(
        "dex_engine_settlement_sequence",
        "SettlementSeq->WarmupThenStaleProvidedAbWithDeadTail",
    )
    assert witness.outcome_label == "reject:step=1:settlement mismatch"
    assert len(str(witness.path_id)) == 16
    assert witness.original_size > witness.minimized_size
    assert isinstance(witness.payload, dict)
    assert len(witness.payload["steps"]) == 2
