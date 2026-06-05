from __future__ import annotations

import json
from pathlib import Path

import yaml

import tools.check_cpmm_swap_formal_spec_contract as checker


def _load_contract() -> dict:
    return json.loads(checker.DEFAULT_CONTRACT.read_text(encoding="utf-8"))


def _write(tmp_path: Path, contract: dict) -> Path:
    path = tmp_path / "cpmm_swap_formal_spec_contract.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    return path


def _load_workflow(rel: str) -> dict:
    workflow = yaml.safe_load((checker.ROOT / rel).read_text(encoding="utf-8"))
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


def test_committed_cpmm_formal_spec_contract_checks() -> None:
    result = checker.check_contract()
    assert result["ok"], result


def test_cpmm_formal_spec_contract_claim_tamper_fails(tmp_path: Path) -> None:
    contract = _load_contract()
    contract["claim"] = "Tau placeholder spec clears cpmm_swap.formal_spec."

    # REVIEW [blocked -> A]: the cpmm formal-spec row previously depended on an
    # unresolved owner/matrix interpretation. The contract now records the
    # decision in a source-pinned artifact and rejects claim text edits, so a
    # registry-only flip cannot quietly redefine what counts as the spec.
    result = checker.check_contract(_write(tmp_path, contract))
    assert not result["ok"]
    assert any("claim mismatch" in err for err in result["errors"])


def test_cpmm_formal_spec_contract_source_hash_tamper_fails(tmp_path: Path) -> None:
    contract = _load_contract()
    first = next(iter(contract["source_hashes"]))
    contract["source_hashes"][first] = "0" * 64

    result = checker.check_contract(_write(tmp_path, contract))
    assert not result["ok"]
    assert any("source hash mismatch" in err for err in result["errors"])


def test_cpmm_formal_spec_contract_extra_top_level_field_fails(tmp_path: Path) -> None:
    contract = _load_contract()
    contract["private_path"] = "/private/workspace/secret"

    result = checker.check_contract(_write(tmp_path, contract))

    assert not result["ok"]
    assert any("unexpected public field" in err for err in result["errors"])


def test_cpmm_formal_spec_contract_spot_receipt_dependency_fails(monkeypatch, tmp_path: Path) -> None:
    contract = _load_contract()
    monkeypatch.setattr(
        checker.spot_receipt,
        "check_receipt_file",
        lambda: {"ok": False, "errors": ["forced spot receipt failure"]},
    )

    result = checker.check_contract(_write(tmp_path, contract))
    assert not result["ok"]
    assert any("spot proof public receipt failed" in err for err in result["errors"])


def test_cpmm_formal_spec_contract_missing_lean_item_fails(monkeypatch, tmp_path: Path) -> None:
    contract = _load_contract()
    contract["formal_items"] = list(contract["formal_items"])
    contract["formal_items"][0] = dict(contract["formal_items"][0])
    contract["formal_items"][0]["tokens"] = list(contract["formal_items"][0]["tokens"]) + [
        "theorem does_not_exist"
    ]
    monkeypatch.setattr(checker, "EXPECTED_FORMAL_ITEMS", contract["formal_items"])

    result = checker.check_contract(_write(tmp_path, contract))
    assert not result["ok"]
    assert any("missing Lean declaration token" in err for err in result["errors"])


def test_cpmm_formal_spec_contract_rejects_placeholder_spec_role(tmp_path: Path) -> None:
    contract = _load_contract()
    contract["formal_items"] = list(contract["formal_items"]) + [
        {
            "id": "withdrawn_placeholder",
            "path": "src/kernels/dex/cpmm_output_amount_v2.yaml",
            "tokens": ["dummy"],
        }
    ]

    result = checker.check_contract(_write(tmp_path, contract))
    assert not result["ok"]
    assert any("formal_items mismatch" in err for err in result["errors"])


def test_cpmm_formal_spec_contract_forbidden_ref_outside_list_fails(
    tmp_path: Path, monkeypatch
) -> None:
    contract = _load_contract()
    bad_reason = contract["grade_reason"] + " see src/kernels/dex/cpmm_output_amount_v2.yaml"
    contract["grade_reason"] = bad_reason
    monkeypatch.setattr(checker, "EXPECTED_GRADE_REASON", bad_reason)

    result = checker.check_contract(_write(tmp_path, contract))

    assert not result["ok"]
    assert any("forbidden placeholder spec ref appears outside" in err for err in result["errors"])


def test_cpmm_formal_spec_contract_workflow_rejects_comment_only_command(monkeypatch) -> None:
    runtime_shadow = _load_workflow(".github/workflows/runtime-shadow.yml")
    release_integrity = _load_workflow(".github/workflows/release-integrity.yml")
    workflows = {
        ".github/workflows/runtime-shadow.yml": runtime_shadow,
        ".github/workflows/release-integrity.yml": release_integrity,
    }
    token = "tools/check_cpmm_swap_formal_spec_contract.py check --pretty"
    changed = sum(
        _mutate_run_blocks(workflow, token, f"# {token}") for workflow in workflows.values()
    )
    assert changed > 0
    monkeypatch.setattr(checker, "_load_workflow", lambda rel: workflows[rel])

    errors: list[str] = []
    checker._check_workflows(errors)

    assert any("missing active CPMM formal-spec gate token" in err for err in errors)


def test_cpmm_formal_spec_contract_workflow_rejects_comment_only_path_filter(monkeypatch) -> None:
    runtime_shadow = _load_workflow(".github/workflows/runtime-shadow.yml")
    release_integrity = _load_workflow(".github/workflows/release-integrity.yml")
    contract_path = "docs/assurance/cpmm_swap_formal_spec_contract.json"
    for event in ("pull_request", "push"):
        event_cfg = _workflow_on(runtime_shadow)[event]
        assert isinstance(event_cfg, dict)
        event_cfg["paths"] = [path for path in event_cfg["paths"] if path != contract_path]
    # REVIEW [B -> A-]: a path filter mentioned only in a shell comment is not
    # CI coverage. This regression keeps the workflow checker tied to active
    # `on.*.paths` entries instead of raw YAML text.
    changed = _mutate_run_blocks(
        runtime_shadow,
        "python3 tools/check_cpmm_swap_formal_spec_contract.py check --pretty",
        (
            "# docs/assurance/cpmm_swap_formal_spec_contract.json\n"
            "          python3 tools/check_cpmm_swap_formal_spec_contract.py check --pretty"
        ),
    )
    assert changed > 0
    workflows = {
        ".github/workflows/runtime-shadow.yml": runtime_shadow,
        ".github/workflows/release-integrity.yml": release_integrity,
    }
    monkeypatch.setattr(checker, "_load_workflow", lambda rel: workflows[rel])

    errors: list[str] = []
    checker._check_workflows(errors)

    assert any("paths missing CPMM formal-spec filters" in err for err in errors)
