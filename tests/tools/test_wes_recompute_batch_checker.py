from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]


def _load_cases() -> list[dict]:
    corpus_path = REPO_ROOT / "tools" / "wes" / "recompute_batch_v4_cases.json"
    corpus = json.loads(corpus_path.read_text(encoding="utf-8"))
    assert corpus["schema"] == "zenodex.wes.recompute_batch_v4_cases.v1"
    return list(corpus["cases"])


def _candidate(mutation: str, *, base_case: str = "create_pool") -> dict:
    return {
        "schema": "witness_candidate.v1",
        "system_id": "zenodex_recompute_batch_v4",
        "candidate_id": f"test:{base_case}:{mutation}",
        "source_lane": "valid_control" if mutation == "valid_baseline" else "commitment_binding",
        "state_features": {"base_case": base_case},
        "trace_features": {},
        "action_features": {"mutation_operator": mutation},
        "constraint_features": {},
        "checker_budget_cost": 1.0,
        "expected_checker": "zenodex_recompute_batch_v4_wes_checker",
        "target_predicates": ["zenodex_recompute_batch_v4_binding_rejects_invalid"],
        "deterministic_seed": "test",
        "parent_candidate_hash": None,
    }


def _run_checker(tmp_path: Path, mutation: str, *, base_case: str = "create_pool") -> dict:
    checker = REPO_ROOT / "tools" / "wes" / "recompute_batch_v4_wes_checker.py"
    candidate_path = tmp_path / f"{base_case}-{mutation}.json"
    candidate_path.write_text(json.dumps(_candidate(mutation, base_case=base_case), sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(checker), str(candidate_path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    return json.loads(proc.stdout.decode("utf-8"))


@pytest.mark.parametrize("case", _load_cases(), ids=lambda case: case["mutation_operator"])
def test_wes_recompute_batch_checker_expected_mutation_outcomes(
    tmp_path: Path,
    case: dict,
) -> None:
    mutation = case["mutation_operator"]
    result = _run_checker(tmp_path, mutation)

    assert result["result"] == case["expected_result"]
    assert result["replay_receipt"].startswith("sha256:")
    assert result["telemetry"]["engine_ok"] is case["expected_engine_ok"]
    if not case["expected_engine_ok"]:
        assert result["telemetry"]["invalid_accept"] is False
    expected_error = case.get("expected_error_contains")
    if expected_error:
        assert expected_error in result["telemetry"]["error_code"]


def test_wes_recompute_batch_checker_accepts_valid_baseline(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "valid_baseline")

    assert result["result"] == "checked_safe"
    assert result["telemetry"]["engine_ok"] is True
    assert result["replay_receipt"].startswith("sha256:")


def test_wes_recompute_batch_checker_accepts_swap_exact_in_baseline(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "valid_baseline", base_case="swap_exact_in")

    assert result["result"] == "checked_safe"
    assert result["telemetry"]["engine_ok"] is True
    assert result["replay_receipt"].startswith("sha256:")


def test_wes_recompute_batch_checker_accepts_add_liquidity_baseline(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "valid_baseline", base_case="add_liquidity")

    assert result["result"] == "checked_safe"
    assert result["telemetry"]["engine_ok"] is True
    assert result["replay_receipt"].startswith("sha256:")


def test_wes_recompute_batch_checker_rejects_swap_exact_in_snapshot_drift(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "proof_snapshot_balance_amount_mutation", base_case="swap_exact_in")

    assert result["result"] == "near_miss"
    assert result["telemetry"]["engine_ok"] is False
    assert "pre_state_commitment does not match snapshot" in result["telemetry"]["error_code"]


def test_wes_recompute_batch_checker_rejects_add_liquidity_snapshot_drift(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "proof_snapshot_balance_amount_mutation", base_case="add_liquidity")

    assert result["result"] == "near_miss"
    assert result["telemetry"]["engine_ok"] is False
    assert "pre_state_commitment does not match snapshot" in result["telemetry"]["error_code"]


def test_wes_recompute_batch_checker_rejects_pre_state_commitment_mismatch(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "proof_pre_state_commitment_zero")

    assert result["result"] == "near_miss"
    assert result["violated_predicate"] == "zenodex_recompute_batch_v4_binding_rejects_invalid"
    assert result["telemetry"]["engine_ok"] is False
    assert "pre_state_commitment mismatch" in result["telemetry"]["error_code"]


def test_wes_recompute_batch_checker_gets_structured_malformed_rejection(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "proof_snapshot_corrupt_base64")

    assert result["result"] == "malformed"
    assert result["telemetry"]["engine_ok"] is False
    assert "proof verifier failed" not in result["telemetry"]["error_code"]
    assert "invalid base64" in result["telemetry"]["error_code"]


def test_wes_recompute_batch_checker_gets_structured_zlib_rejection(tmp_path: Path) -> None:
    result = _run_checker(tmp_path, "proof_operations_corrupt_zlib")

    assert result["result"] == "malformed"
    assert result["telemetry"]["engine_ok"] is False
    assert "proof verifier failed" not in result["telemetry"]["error_code"]
    assert "operations invalid zlib" in result["telemetry"]["error_code"]
