"""Bounded ESSO evidence for the atomic ZDEX buy-and-burn lifecycle.

The model is research-only. A local multi-solver replay proves its finite
transition system, while the implementation tests and Lean proofs cover
different refinement obligations. None of these tests mount settlement
authority or prove the external verifier premises represented as booleans.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "zdex_atomic_buyback_lifecycle_v1.yaml"
PYTHON_CORE = ROOT / "src" / "core" / "zdex_atomic_buyback_v1.py"
RUST_ROUTE = ROOT / "zk" / "global_settlement_abi_v1" / "src" / "zdex_atomic_buyback.rs"

RECORDED_IR_HASH = "sha256:ca7af47d90a5b8477d1534a9101e337817436573e2d25b7e2a17c21a8dcbd8a5"
RECORDED_SOURCE_SHA256 = "000fe51c99a969ca46719420478bb5f7a99a9fcdc08d8d7f6d32abe7df4b219d"
RECORDED_FINGERPRINT = "d1f8fea9b161d7eb75d74315ed8f370b7e4ab17f555ec6a0d28ea59d354d0459"
RECORDED_ESSO_CODE_HASH = "7f80c6216be85c827e8d1cc2fa08ee3107a74588"
EXPECTED_ACTIONS = {"prepare", "commit", "discard"}
EXPECTED_INVARIANTS = {
    "inv_quote_conservation",
    "inv_zdex_owned_equals_supply",
    "inv_pending_does_not_consume_occurrence",
    "inv_pending_is_unpublished_and_exact",
    "inv_empty_has_no_pending_value_or_obligation",
    "inv_noncommit_preserves_committed_projection",
    "inv_commit_requires_all_authorities",
    "inv_commit_is_exact_atomic_purchase_and_burn",
    "inv_consumption_monotone",
}


def _document() -> dict[str, object]:
    value = yaml.safe_load(MODEL.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _esso_python() -> str | None:
    configured = os.environ.get("ZENO_ESSO_PYTHON")
    if configured:
        return configured
    if importlib.util.find_spec("ESSO") is not None:
        return sys.executable
    return None


def _run_esso(python: str, *args: str) -> tuple[int, dict[str, object]]:
    proc = subprocess.run(
        [python, "-m", "ESSO", *args],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    raw = proc.stdout if proc.stdout.strip() else proc.stderr
    value = json.loads(raw)
    assert isinstance(value, dict)
    return proc.returncode, value


def test_model_hash_action_set_and_obligations_are_exact() -> None:
    # Arrange
    document = _document()

    # Act
    actual_hash = f"sha256:{hashlib.sha256(MODEL.read_bytes()).hexdigest()}"
    actions = {row["id"] for row in document["actions"]}
    invariants = {row["id"] for row in document["invariants"]}

    # Assert
    assert actual_hash == f"sha256:{RECORDED_SOURCE_SHA256}"
    assert actions == EXPECTED_ACTIONS
    assert invariants == EXPECTED_INVARIANTS
    assert document["meta"]["model_id"] == "zdex_atomic_buyback_lifecycle_v1"


def test_model_scope_is_finite_and_claim_ceiling_is_explicit() -> None:
    # Arrange
    document = _document()
    state_vars = {row["id"]: row for row in document["state_vars"]}
    notes = " ".join(document["meta"]["notes"].split())

    # Act
    occurrence_max = state_vars["pending_occurrence"]["type"]["max"]
    amount_max = state_vars["pending_spend"]["type"]["max"]

    # Assert
    assert occurrence_max == 1
    assert amount_max == 4
    assert not any("budget" in state_id for state_id in state_vars)
    assert "No persistent fee-budget object exists" in notes
    for nonclaim in (
        "does not prove the booleans",
        "runtime refinement",
        "cryptographic receipt verification",
        "production",
        "settlement authority",
    ):
        assert nonclaim in notes


def test_oracle_observation_is_a_reusable_authenticated_read() -> None:
    # Arrange
    document = _document()
    state_ids = {row["id"] for row in document["state_vars"]}
    prepare = next(row for row in document["actions"] if row["id"] == "prepare")
    prepare_source = json.dumps(prepare, sort_keys=True)

    # Act
    stale_one_shot_state = {state_id for state_id in state_ids if "oracle_used" in state_id}

    # Assert
    assert stale_one_shot_state == set()
    assert '"param": "oracle_finalized"' in prepare_source
    assert '"param": "oracle_fresh"' in prepare_source
    assert "authenticated reusable read" in document["meta"]["notes"]


def test_model_contract_names_the_runtime_commit_and_reject_obligations() -> None:
    # Arrange
    python_source = PYTHON_CORE.read_text(encoding="utf-8")
    rust_source = RUST_ROUTE.read_text(encoding="utf-8")
    model_source = MODEL.read_text(encoding="utf-8")

    # Act / Assert
    assert "prepare_zdex_atomic_buyback_v1" in python_source
    assert "finalize_zdex_atomic_buyback_v1" in python_source
    assert "atomic buyback rejection must be an exact no-effect no-op" in python_source
    assert "prepare_zdex_atomic_buyback_v1" in rust_source
    assert "finalize_zdex_atomic_buyback_v1" in rust_source
    assert "terminal_obligations_root" in rust_source
    assert "inv_noncommit_preserves_committed_projection" in model_source
    assert "inv_commit_is_exact_atomic_purchase_and_burn" in model_source


@pytest.mark.skipif(_esso_python() is None, reason="ESSO unavailable; formal replay is INCOMPLETE")
def test_esso_two_solver_replay_is_exact_and_deterministic(tmp_path: Path) -> None:
    # Arrange
    python = _esso_python()
    assert python is not None

    # Act
    validate_rc, validate = _run_esso(python, "validate", str(MODEL))
    verify_rc, verify = _run_esso(
        python,
        "verify-multi",
        str(MODEL),
        "--solvers",
        "z3,cvc5",
        "--determinism-trials",
        "2",
        "--timeout-ms",
        "10000",
        "--output",
        str(tmp_path / "esso"),
    )

    # Assert
    assert validate_rc == 0 and validate["ok"] is True
    assert validate["ir_hash"] == RECORDED_IR_HASH
    assert verify_rc == 0 and verify["ok"] is True
    assert verify["determinism"] is True
    assert verify["fingerprints"] == [RECORDED_FINGERPRINT, RECORDED_FINGERPRINT]
    report = verify["report"]
    assert report["verdict"] == "VERIFIED"
    assert report["failed_queries"] == 0
    assert report["inconclusive_queries"] == 0
    assert report["solvers_agreed"] is True
    assert report["tool_versions"]["esso_code_hash"] == RECORDED_ESSO_CODE_HASH


@pytest.mark.parametrize(
    ("needle", "replacement", "named_disaster"),
    (
        pytest.param(
            'then: { op: "-", args: [{ var: "zdex_supply" }, { var: "pending_out" }] }',
            'then: { var: "zdex_supply" }',
            "purchase_without_exact_supply_burn",
            id="purchase_without_exact_supply_burn",
        ),
        pytest.param(
            '- { param: "burn_receipt_ok" }',
            '- { bool: true }',
            "commit_without_burn_receipt_authority",
            id="commit_without_burn_receipt_authority",
        ),
        pytest.param(
            '- { param: "tokenomics_lane_receipt_ok" }',
            '- { bool: true }',
            "commit_without_tokenomics_lane_receipt",
            id="commit_without_tokenomics_lane_receipt",
        ),
        pytest.param(
            '- { param: "profile_route_ok" }',
            '- { bool: true }',
            "prepare_without_profile_route_binding",
            id="prepare_without_profile_route_binding",
        ),
        pytest.param(
            '- { op: "<=", args: [{ param: "spend" }, { param: "safe_limit" }] }',
            '- { bool: true }',
            "prepare_above_safe_spend_limit",
            id="prepare_above_safe_spend_limit",
        ),
        pytest.param(
            '- { param: "oracle_fresh" }',
            '- { bool: true }',
            "prepare_with_stale_oracle_observation",
            id="prepare_with_stale_oracle_observation",
        ),
    ),
)
@pytest.mark.skipif(_esso_python() is None, reason="ESSO unavailable; mutation replay is INCOMPLETE")
def test_esso_named_semantic_mutants_produce_counterexamples(
    tmp_path: Path,
    needle: str,
    replacement: str,
    named_disaster: str,
) -> None:
    # Arrange: Reach/infect by changing one load-bearing semantic expression.
    source = MODEL.read_text(encoding="utf-8")
    assert source.count(needle) == 1, named_disaster
    mutant = tmp_path / f"{named_disaster}.yaml"
    mutant.write_text(source.replace(needle, replacement), encoding="utf-8")
    python = _esso_python()
    assert python is not None

    # Act: Propagate through ESSO's inductive query and reveal as SAT.
    rc, result = _run_esso(
        python,
        "verify-multi",
        str(mutant),
        "--solvers",
        "z3,cvc5",
        "--determinism-trials",
        "2",
        "--timeout-ms",
        "10000",
    )

    # Assert
    assert rc != 0
    assert result["ok"] is False
    assert result["report"]["verdict"] == "FAILED"
    assert result["report"]["failed_queries"] >= 1
    assert result["report"]["inconclusive_queries"] == 0
    assert result["report"]["solvers_agreed"] is True
