"""Negative suite for the balances settlement-supply formal-spec contract checker.

Proves the checker has TEETH: it rejects claim drift, source-hash drift, missing/renamed Lean
declaration tokens, unexpected envelope keys, a missing kernel-assurance proof id, a forbidden
bounded-spec ref, and a tautology-regression (loss of the Σdelta=0 gate hypothesis). The committed
contract must verify ok=True.
"""

from __future__ import annotations

import json
from pathlib import Path

import yaml

import tools.check_settlement_supply_formal_spec_contract as contract_mod

CONTRACT = contract_mod.DEFAULT_CONTRACT


def _load() -> dict:
    return json.loads(CONTRACT.read_text(encoding="utf-8"))


def _write_tmp(tmp_path: Path, obj: dict) -> Path:
    p = tmp_path / "contract.json"
    p.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return p


def _load_workflow(rel: str) -> dict:
    workflow = yaml.safe_load((contract_mod.ROOT / rel).read_text(encoding="utf-8"))
    assert isinstance(workflow, dict)
    return workflow


def _workflow_on(workflow: dict) -> dict:
    on_section = workflow.get("on", workflow.get(True))
    assert isinstance(on_section, dict)
    return on_section


def _mutate_run_blocks(workflow: dict, needle: str, replacement: str) -> int:
    changed = 0
    jobs = workflow.get("jobs", {})
    assert isinstance(jobs, dict)
    for job in jobs.values():
        assert isinstance(job, dict)
        for step in job.get("steps", []):
            if not isinstance(step, dict) or not isinstance(step.get("run"), str):
                continue
            run = step["run"]
            if needle in run:
                step["run"] = run.replace(needle, replacement)
                changed += 1
    return changed


def test_committed_contract_verifies() -> None:
    report = contract_mod.check_contract()
    assert report["ok"] is True, report["errors"]


def test_claim_drift_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["claim"] = obj["claim"] + " (tampered)"
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("claim mismatch" in e for e in report["errors"])


def test_source_hash_drift_fails(tmp_path: Path) -> None:
    obj = _load()
    # corrupt one pinned hash
    key = "lean-mathlib/Proofs/SettlementSupplyConservation.lean"
    obj["source_hashes"][key] = "0" * 64
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("source hash mismatch" in e for e in report["errors"])


def test_unexpected_key_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["local_note"] = "should not ride along"
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("unexpected public field" in e for e in report["errors"])


def test_missing_kernel_proof_id_fails(tmp_path: Path) -> None:
    obj = _load()
    obj["required_kernel_assurance_proof_ids"] = ["something_else"]
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    # mismatch against EXPECTED is caught at the field level
    assert any("required_kernel_assurance_proof_ids mismatch" in e for e in report["errors"])


def test_renamed_theorem_token_fails(tmp_path: Path, monkeypatch) -> None:
    # If a formal_item token (a pinned Lean declaration) no longer appears in the source, fail.
    obj = _load()
    bad_items = json.loads(json.dumps(contract_mod.EXPECTED_FORMAL_ITEMS))
    bad_items[1]["tokens"][1] = "theorem accepted_preserves_supply_RENAMED"
    obj["formal_items"] = bad_items
    monkeypatch.setattr(contract_mod, "EXPECTED_FORMAL_ITEMS", bad_items)
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    assert any("missing Lean declaration token" in e for e in report["errors"])


def test_forbidden_spec_ref_outside_list_fails(tmp_path: Path) -> None:
    obj = _load()
    # smuggle a bounded-spec ref into the claim (outside the forbidden_spec_refs list)
    obj["claim"] = obj["claim"] + " see src/tau_specs/balance_transition_v1.tau"
    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))
    assert report["ok"] is False
    # claim mismatch OR the explicit forbidden-ref-outside-list error
    assert any(
        ("forbidden bounded spec ref appears outside" in e) or ("claim mismatch" in e)
        for e in report["errors"]
    )


def test_forbidden_spec_ref_guard_has_independent_teeth(tmp_path: Path, monkeypatch) -> None:
    obj = _load()
    bad_reason = obj["grade_reason"] + " see src/tau_specs/balance_transition_v1.tau"
    obj["grade_reason"] = bad_reason
    monkeypatch.setattr(contract_mod, "EXPECTED_GRADE_REASON", bad_reason)

    report = contract_mod.check_contract(_write_tmp(tmp_path, obj))

    assert report["ok"] is False
    assert any("forbidden bounded spec ref appears outside" in e for e in report["errors"])


def test_tautology_regression_guarded(monkeypatch) -> None:
    # If the Lean spec loses its Σdelta=0 gate hypothesis, the nontautology guard must fire.
    monkeypatch.setattr(contract_mod, "REQUIRED_NONTAUTOLOGY_TOKEN", "this token is absent xyzzy")
    errors: list[str] = []
    contract_mod._check_nontautology(errors)
    assert any("Σdelta=0 gate" in e or "gate hypothesis" in e for e in errors)


def test_tautology_guard_rejects_comment_only_gate_text(monkeypatch) -> None:
    lean_path = contract_mod.ROOT / "lean-mathlib" / "Proofs" / "SettlementSupplyConservation.lean"
    original = lean_path.read_text(encoding="utf-8")
    weakened = original.replace(
        "def accepted (balDeltas resDeltas : Ledger) : Prop :=\n    supply balDeltas + supply resDeltas = 0",
        "def accepted (balDeltas resDeltas : Ledger) : Prop :=\n    True\n"
        "-- stale comment: supply balDeltas + supply resDeltas = 0",
    )
    assert weakened != original

    original_read_text = Path.read_text

    def fake_read_text(self: Path, *, encoding: str | None = None, errors: str | None = None) -> str:
        if self == lean_path:
            assert encoding == "utf-8"
            return weakened
        return original_read_text(self, encoding=encoding, errors=errors)

    monkeypatch.setattr(Path, "read_text", fake_read_text)
    errors: list[str] = []
    contract_mod._check_nontautology(errors)
    assert any("Σdelta=0 gate" in e or "gate hypothesis" in e for e in errors)


def test_workflow_gate_token_missing_fails(monkeypatch) -> None:
    monkeypatch.setattr(contract_mod, "EXPECTED_WORKFLOW_TOKENS", ["missing settlement supply workflow token"])
    errors: list[str] = []
    contract_mod._check_workflows(errors)
    assert any("workflow is missing active settlement-supply formal-spec gate token" in e for e in errors)


def test_settlement_formal_spec_contract_workflow_rejects_comment_only_command(monkeypatch) -> None:
    runtime_shadow = _load_workflow(".github/workflows/runtime-shadow.yml")
    release_integrity = _load_workflow(".github/workflows/release-integrity.yml")
    workflows = {
        ".github/workflows/runtime-shadow.yml": runtime_shadow,
        ".github/workflows/release-integrity.yml": release_integrity,
    }
    token = "tools/check_settlement_supply_formal_spec_contract.py check --pretty"
    changed = sum(
        _mutate_run_blocks(workflow, token, f"# {token}") for workflow in workflows.values()
    )
    assert changed > 0
    monkeypatch.setattr(contract_mod, "_load_workflow", lambda rel: workflows[rel])

    errors: list[str] = []
    contract_mod._check_workflows(errors)

    assert any("missing active settlement-supply formal-spec gate token" in e for e in errors)


def test_settlement_formal_spec_contract_workflow_rejects_comment_only_path_filter(
    monkeypatch,
) -> None:
    runtime_shadow = _load_workflow(".github/workflows/runtime-shadow.yml")
    release_integrity = _load_workflow(".github/workflows/release-integrity.yml")
    contract_path = "docs/assurance/settlement_supply_formal_spec_contract.json"
    for event in ("pull_request", "push"):
        event_cfg = _workflow_on(runtime_shadow)[event]
        assert isinstance(event_cfg, dict)
        event_cfg["paths"] = [path for path in event_cfg["paths"] if path != contract_path]
    # REVIEW [B -> A-]: raw YAML search accepted path names in comments. This
    # regression requires the balances formal-spec CI trigger to be an active
    # path filter, matching the stricter checker semantics.
    changed = _mutate_run_blocks(
        runtime_shadow,
        "python3 tools/check_settlement_supply_formal_spec_contract.py check --pretty",
        (
            "# docs/assurance/settlement_supply_formal_spec_contract.json\n"
            "          python3 tools/check_settlement_supply_formal_spec_contract.py check --pretty"
        ),
    )
    assert changed > 0
    workflows = {
        ".github/workflows/runtime-shadow.yml": runtime_shadow,
        ".github/workflows/release-integrity.yml": release_integrity,
    }
    monkeypatch.setattr(contract_mod, "_load_workflow", lambda rel: workflows[rel])

    errors: list[str] = []
    contract_mod._check_workflows(errors)

    assert any("paths missing settlement-supply formal-spec filters" in e for e in errors)
