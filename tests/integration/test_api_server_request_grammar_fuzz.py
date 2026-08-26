from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.api_server_request_grammar_fuzz import explore_all_targets, explore_target, minimize_case

ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def test_api_server_request_grammar_fuzz_cors_origins_discovers_stable_paths() -> None:
    report = explore_target("cors_origins")
    labels = _labels(report)
    assert report.total_cases == 6
    assert report.unique_outcome_count == 3
    assert report.unique_path_count == 6
    assert "ok:none" in labels
    assert "ok:https://a.example" in labels
    assert "ok:https://a.example|https://b.example" in labels


def test_api_server_request_grammar_fuzz_demo_auth_discovers_stable_paths() -> None:
    report = explore_target("demo_auth")
    labels = _labels(report)
    assert report.total_cases == 5
    assert report.unique_outcome_count == 2
    assert report.unique_path_count == 4
    assert labels == {"ok:0", "ok:1"}


def test_api_server_request_grammar_fuzz_raw_and_json_body_discovers_stable_paths() -> None:
    raw = explore_target("raw_body")
    raw_labels = _labels(raw)
    assert raw.total_cases == 8
    assert raw.unique_outcome_count == 8
    assert raw.unique_path_count == 5
    assert "ok:none:close=0" in raw_labels
    assert "ok:0:close=0" in raw_labels
    assert "ok:1:close=0" in raw_labels
    assert "ok:2:close=0" in raw_labels
    assert "ok:7:close=0" in raw_labels
    assert "ok:8:close=0" in raw_labels
    assert "err:400:invalid_content_length:close=0" in raw_labels
    assert "err:413:body_too_large:close=1" in raw_labels

    body = explore_target("json_body")
    body_labels = _labels(body)
    assert body.total_cases == 7
    assert body.unique_outcome_count == 3
    assert body.unique_path_count == 6
    assert "ok:none" in body_labels
    assert "ok:x" in body_labels
    assert "ok:a|b" in body_labels


def test_api_server_request_grammar_fuzz_dex_request_envelope_discovers_stable_paths() -> None:
    report = explore_target("dex_request_envelope")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 16
    assert report.unique_outcome_count == 10
    assert report.unique_path_count == 16
    assert "pass:false" in labels
    assert "handled:200:ok" in labels
    assert "handled:400:bad_json" in labels
    assert "handled:400:bad_body" in labels
    assert "handled:400:missing_body" in labels
    assert "handled:400:bad_amount_in" in labels
    assert "handled:400:impact_preview_error" in labels
    assert "handled:401:unauthorized" in labels
    assert "handled:405:method_not_allowed" in labels
    assert "handled:404:not_found" in labels
    assert "repair:dex_req->authorized" in derivations
    assert "sweep:dex_req->bad-reserve-out" in derivations
    assert "sweep:dex_req->bad-amount-in" in derivations
    assert "sweep:dex_req->bad-fee-bps" in derivations
    assert "sweep:dex_req->bad-pending-same-dir" in derivations
    assert "sweep:dex_req->bad-confidence-bps" in derivations


def test_api_server_request_grammar_fuzz_all_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {
        "cors_origins",
        "demo_auth",
        "raw_body",
        "json_body",
        "dex_request_envelope",
    }
    assert by_name["cors_origins"].total_cases == 6
    assert by_name["demo_auth"].total_cases == 5
    assert by_name["raw_body"].total_cases == 8
    assert by_name["json_body"].total_cases == 7
    assert by_name["dex_request_envelope"].total_cases == 16


def test_api_server_request_grammar_fuzz_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/api_server_request_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/api-server-request-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {
        "cors_origins",
        "demo_auth",
        "raw_body",
        "json_body",
        "dex_request_envelope",
    }


def test_api_server_request_minimizer_collapses_unauthorized_dead_fields() -> None:
    witness = minimize_case("dex_request_envelope", "DexReq->UnauthorizedWithDeadFields")
    assert witness.outcome_label == "handled:401:unauthorized"
    assert witness.path_id == "fd03b173b6c4b0ca"
    assert witness.original_size > witness.minimized_size
    assert witness.payload == {"token": "sekret"}


def test_api_server_request_minimizer_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [
            sys.executable,
            str(ROOT_DIR / "tools/api_server_request_grammar_fuzz.py"),
            "--target",
            "dex_request_envelope",
            "--minimize-derivation",
            "DexReq->UnauthorizedWithDeadFields",
            "--format",
            "json",
        ],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/api-server-request-minimized-witness/v1"
    witness = payload["witness"]
    assert witness["target"] == "dex_request_envelope"
    assert witness["derivation"] == "DexReq->UnauthorizedWithDeadFields"
    assert witness["outcome_label"] == "handled:401:unauthorized"
    assert witness["path_id"] == "fd03b173b6c4b0ca"
    assert witness["payload"] == {"token": "sekret"}
    assert witness["original_size"] > witness["minimized_size"]
