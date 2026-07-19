from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.dex_engine_sequence_grammar_fuzz import (
    explore_all_targets,
    explore_target,
    minimize_case,
)

ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def test_dex_engine_sequence_grammar_fuzz_discovers_stable_stateful_paths() -> None:
    report = explore_target("dex_engine_sequence")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 8
    assert report.unique_outcome_count == 7
    assert report.unique_path_count == 8
    assert "ok:pools=1:nonces=aaaaaaaa=1" in labels
    assert "ok:pools=2:nonces=aaaaaaaa=2" in labels
    assert "ok:pools=2:nonces=aaaaaaaa=2" in labels
    assert "reject:step=1:nonce sequence invalid" in labels
    assert (
        "reject:step=1:intent sender mismatch: "
        "0x0303030303030303030303030303030303030303030303030303030303030303"
    ) in labels
    assert "reject:step=1:invalid intents: operations['2'] must be a list, got <class 'str'>" in labels
    assert "reject:step=1:operations['3'] must be an object" in labels
    assert "DexSeq->NoOpThenValidPool" in derivations
    assert "DexSeq->DuplicatePoolFreshNonce" in derivations
    assert "DexSeq->ReplayPoolAfterSuccess" in derivations


def test_dex_engine_sequence_grammar_fuzz_all_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {"dex_engine_sequence"}
    assert by_name["dex_engine_sequence"].total_cases == 8


def test_dex_engine_sequence_grammar_fuzz_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/dex_engine_sequence_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/dex-engine-sequence-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {"dex_engine_sequence"}


def test_dex_engine_sequence_minimizer_removes_dead_tail_without_changing_path() -> None:
    witness = minimize_case("dex_engine_sequence", "DexSeq->ReplayPoolAfterSuccessWithDeadTail")
    assert witness.outcome_label == "reject:step=1:nonce sequence invalid"
    assert witness.path_id == "198b52b92fc6f655"
    assert witness.original_size > witness.minimized_size
    assert witness.original_size == 1601
    assert witness.minimized_size == 1076
    assert isinstance(witness.payload, dict)
    assert witness.payload["initial"] == "ab"
    steps = witness.payload["steps"]
    assert isinstance(steps, list)
    assert len(steps) == 2
    assert all(isinstance(step, dict) for step in steps)


def test_dex_engine_sequence_minimizer_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [
            sys.executable,
            str(ROOT_DIR / "tools/dex_engine_sequence_grammar_fuzz.py"),
            "--target",
            "dex_engine_sequence",
            "--minimize-derivation",
            "DexSeq->ReplayPoolAfterSuccessWithDeadTail",
            "--format",
            "json",
        ],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/dex-engine-sequence-minimized-witness/v1"
    witness = payload["witness"]
    assert witness["target"] == "dex_engine_sequence"
    assert witness["derivation"] == "DexSeq->ReplayPoolAfterSuccessWithDeadTail"
    assert witness["outcome_label"] == "reject:step=1:nonce sequence invalid"
    assert witness["path_id"] == "198b52b92fc6f655"
    assert witness["original_size"] == 1601
    assert witness["minimized_size"] == 1076
