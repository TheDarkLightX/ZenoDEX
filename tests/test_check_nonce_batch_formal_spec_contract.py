"""Negative suite for the nonces batch-sequencing formal-spec contract checker.

Proves teeth: rejects claim drift, source-hash drift (incl. a LIVE ESSO model or Lean edit), missing
spec tokens, unexpected envelope keys, and a missing ESSO/Lean attestation id. Committed contract
must verify ok=True.
"""

from __future__ import annotations

import json
from pathlib import Path

import tools.check_nonce_batch_formal_spec_contract as contract_mod

CONTRACT = contract_mod.DEFAULT_CONTRACT


def _load() -> dict:
    return json.loads(CONTRACT.read_text(encoding="utf-8"))


def _write_tmp(tmp_path: Path, obj: dict) -> Path:
    p = tmp_path / "contract.json"
    p.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return p


def test_committed_contract_verifies() -> None:
    report = contract_mod.check_contract()
    assert report["ok"] is True, report["errors"]


def test_claim_drift_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["claim"] = obj["claim"] + " (tampered)"
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("claim mismatch" in e for e in report["errors"])


def test_esso_model_source_drift_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["source_hashes"]["src/kernels/dex/nonce_batch_sequencing_v1.yaml"] = "0" * 64
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("source hash mismatch" in e for e in report["errors"])


def test_unexpected_key_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["local_note"] = "nope"
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("unexpected public field" in e for e in report["errors"])


def test_missing_esso_attestation_id_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["required_esso_spot_proof_ids"] = ["nope"]
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("required_esso_spot_proof_ids mismatch" in e for e in report["errors"])


def test_missing_lean_attestation_id_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["required_lean_kernel_assurance_proof_ids"] = ["nope"]
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("required_lean_kernel_assurance_proof_ids mismatch" in e for e in report["errors"])


def test_forbidden_spec_ref_outside_list_fails(tmp_path: Path, monkeypatch) -> None:
    obj = _load()
    bad_reason = obj["grade_reason"] + " see src/tau_specs/recommended/nonce_replay_guard_v1.tau"
    obj["grade_reason"] = bad_reason
    monkeypatch.setattr(contract_mod, "EXPECTED_GRADE_REASON", bad_reason)

    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))

    assert report["ok"] is False
    assert any("forbidden superseded spec ref appears outside" in e for e in report["errors"])


def test_renamed_lean_theorem_token_fails(tmp_path: Path, monkeypatch) -> None:
    obj = _load()
    bad = json.loads(json.dumps(contract_mod.EXPECTED_FORMAL_ITEMS))
    bad[1]["tokens"][3] = "theorem batch_accept_decision_implies_safety_RENAMED"
    obj["formal_items"] = bad
    monkeypatch.setattr(contract_mod, "EXPECTED_FORMAL_ITEMS", bad)
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("missing spec token" in e for e in report["errors"])


def test_workflow_gate_token_missing_fails(monkeypatch) -> None:
    monkeypatch.setattr(contract_mod, "EXPECTED_WORKFLOW_TOKENS", ["missing nonce formal-spec workflow token"])
    errors: list[str] = []
    contract_mod._check_workflows(errors)
    assert any("workflow is missing nonce formal-spec gate token" in e for e in errors)
