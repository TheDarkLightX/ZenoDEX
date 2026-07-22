from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.operations_grammar_fuzz import explore_all_targets, explore_target, minimize_case

ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def test_operations_grammar_fuzz_signed_intents_discovers_stable_boundary_paths() -> None:
    report = explore_target("signed_intents")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 25
    assert report.unique_outcome_count == 16
    assert report.unique_path_count == 25
    assert "ok:0" in labels
    assert "ok:1" in labels
    assert "ValueError:operations['2'] must be a list, got <class 'str'>" in labels
    assert "ValueError:Failed to parse signed intent 0: Missing required field: module" in labels
    assert "ValueError:Failed to parse signed intent 0: Invalid module: BadSwap" in labels
    assert "ValueError:Failed to parse signed intent 0: Invalid intent kind: UNKNOWN" in labels
    assert "ValueError:Failed to parse signed intent 0: signature provided twice (envelope + field)" in labels
    assert "ValueError:Failed to parse signed intent 0: quote_receipt provided twice (envelope + field)" in labels
    assert "ValueError:Failed to parse signed intent 1: Missing required field: module" in labels
    assert "repair:signed_ops->drop-envelope-signature" in derivations
    assert "repair:signed_ops->drop-envelope-receipt" in derivations
    assert "repair:signed_ops->fill-signature" in derivations
    assert "repair:signed_ops->fix-receipt-body" in derivations


def test_operations_grammar_fuzz_settlement_envelope_discovers_stable_boundary_paths() -> None:
    report = explore_target("settlement_envelope")
    labels = _labels(report)
    assert report.total_cases == 17
    assert report.unique_outcome_count == 16
    assert report.unique_path_count == 17
    assert "ok:none" in labels
    assert "ok:proof=0" in labels
    assert "ok:proof=1" in labels
    assert "ValueError:operations['3'] must be a dict, got <class 'str'>" in labels
    assert "ValueError:settlement proof provided twice (proof + zk_proof)" in labels
    assert "ValueError:settlement proof must be an object" in labels
    assert "ValueError:Invalid module: BadSwap" in labels
    assert "ValueError:Invalid version: 0.2" in labels
    assert "ValueError:included_intents entries must be [intent_id, action]" in labels
    assert "ValueError:fills entries must be objects" in labels


def test_operations_grammar_fuzz_all_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {"signed_intents", "settlement_envelope"}
    assert by_name["signed_intents"].total_cases == 25
    assert by_name["settlement_envelope"].total_cases == 17


def test_operations_grammar_fuzz_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/operations_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/operations-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {"signed_intents", "settlement_envelope"}


def test_operations_minimizer_collapses_duplicate_signature_dead_tail() -> None:
    witness = minimize_case("signed_intents", "SignedOps->OneEntry ; Entry->DuplicateSignatureSameWithDeadTail")
    assert witness.outcome_label == "ValueError:Failed to parse signed intent 0: signature provided twice (envelope + field)"
    assert witness.path_id == "6d2631d647554d13"
    assert witness.original_size > witness.minimized_size
    assert witness.payload == {
        "2": [
            [
                {
                    "amount_in": 5,
                    "asset_in": "asset-a",
                    "asset_out": "asset-b",
                    "deadline": 1,
                    "intent_id": "0x1111111111111111111111111111111111111111111111111111111111111111",
                    "kind": "SWAP_EXACT_IN",
                    "min_amount_out": 0,
                    "module": "TauSwap",
                    "pool_id": "pool-1",
                    "sender_pubkey": "pk1",
                    "signature": "sig-1",
                    "version": "0.1",
                },
                "sig-1",
            ]
        ]
    }


def test_operations_minimizer_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [
            sys.executable,
            str(ROOT_DIR / "tools/operations_grammar_fuzz.py"),
            "--target",
            "signed_intents",
            "--minimize-derivation",
            "SignedOps->OneEntry ; Entry->DuplicateSignatureSameWithDeadTail",
            "--format",
            "json",
        ],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/operations-minimized-witness/v1"
    witness = payload["witness"]
    assert witness["target"] == "signed_intents"
    assert witness["derivation"] == "SignedOps->OneEntry ; Entry->DuplicateSignatureSameWithDeadTail"
    assert witness["outcome_label"] == "ValueError:Failed to parse signed intent 0: signature provided twice (envelope + field)"
    assert witness["path_id"] == "6d2631d647554d13"
    assert witness["original_size"] > witness["minimized_size"]
