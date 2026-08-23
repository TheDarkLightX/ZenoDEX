from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.nonce_replay_sequence_grammar_fuzz import (
    explore_all_targets,
    explore_target,
    minimize_case,
)

ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def test_nonce_replay_sequence_grammar_fuzz_discovers_stateful_replay_paths() -> None:
    report = explore_target("nonce_replay_sequence")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 12
    assert report.unique_outcome_count == 9
    assert report.unique_path_count == 12
    assert "ok:11111111=1" in labels
    assert "ok:11111111=2" in labels
    assert "ok:11111111=4" in labels
    assert "ok:11111111=7" in labels
    assert "ok:11111111=2|22222222=2" in labels
    assert "reject:step=0:Missing/invalid nonce" in labels
    assert "reject:step=0:nonce presence must be consistent across batch" in labels
    assert "reject:step=1:nonce sequence invalid" in labels
    assert any(label.startswith("reject:step=1:invalid sender_pubkey for nonce accounting:") for label in labels)
    assert "Seq->EmptyBatchThenAdvance" in derivations
    assert "Seq->BackwardCompatNoOpThenAdvance" in derivations
    assert "Seq->TwoContiguousBatches" in derivations
    assert "Seq->MultiSenderIndependentProgress" in derivations
    assert "Seq->CanonicalizedSenderAcrossSteps" in derivations
    assert "Seq->CrossBatchGap" in derivations
    assert "Seq->CrossBatchReplay" in derivations


def test_nonce_replay_sequence_grammar_fuzz_all_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {"nonce_replay_sequence"}
    assert by_name["nonce_replay_sequence"].total_cases == 12


def test_nonce_replay_sequence_grammar_fuzz_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/nonce_replay_sequence_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/nonce-replay-sequence-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {"nonce_replay_sequence"}


def test_nonce_replay_sequence_minimizer_removes_dead_tail_without_changing_path() -> None:
    witness = minimize_case("nonce_replay_sequence", "Seq->CrossBatchReplayWithDeadTail")
    assert witness.outcome_label == "reject:step=1:nonce sequence invalid"
    assert witness.path_id == "86f985a0a75b6573"
    assert witness.original_size > witness.minimized_size
    assert isinstance(witness.payload, dict)
    steps = witness.payload["steps"]
    assert isinstance(steps, list)
    assert len(steps) == 2
    assert len(steps[0]["intents"]) == 2
    assert len(steps[1]["intents"]) == 1


def test_nonce_replay_sequence_minimizer_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [
            sys.executable,
            str(ROOT_DIR / "tools/nonce_replay_sequence_grammar_fuzz.py"),
            "--target",
            "nonce_replay_sequence",
            "--minimize-derivation",
            "Seq->CrossBatchReplayWithDeadTail",
            "--format",
            "json",
        ],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/nonce-replay-sequence-minimized-witness/v1"
    witness = payload["witness"]
    assert witness["target"] == "nonce_replay_sequence"
    assert witness["derivation"] == "Seq->CrossBatchReplayWithDeadTail"
    assert witness["outcome_label"] == "reject:step=1:nonce sequence invalid"
    assert witness["path_id"] == "86f985a0a75b6573"
    assert witness["original_size"] > witness["minimized_size"]
