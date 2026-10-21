from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from tools.check_test_hygiene_v1 import ChangedPathV1
from tools.check_test_quality_v2 import check_test_quality_repository
from tools.test_hygiene_model_v1 import TestHygieneError
from tools.test_quality_model_v2 import (
    DEFAULT_CONTRACT,
    DEFAULT_EVIDENCE_DIR,
    load_quality_contract,
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def _hygiene_contract() -> dict[str, object]:
    return {
        "schema": "zenodex/test-hygiene-contract/v1",
        "evidence_schema": "zenodex/test-hygiene-evidence/v1",
        "evidence_path_prefix": "tests/evidence/test_hygiene/",
        "allowed_change_kinds": ["assurance_infrastructure"],
        "allowed_evidence_families": [
            "negative_regression",
            "boundary",
            "mutation",
        ],
        "strong_evidence_families": ["mutation"],
        "critical_path_rules": [
            {
                "id": "assurance",
                "include_globs": ["tools/**", "tests/test_*.py"],
                "exclude_globs": [],
                "required_families": [
                    "negative_regression",
                    "boundary",
                    "mutation",
                ],
                "minimum_strong_families": 1,
            }
        ],
    }


def _quality_contract() -> dict[str, object]:
    return {
        "schema": "zenodex/test-quality-contract/v2",
        "evidence_schema": "zenodex/test-quality-evidence/v2",
        "evidence_path_prefix": "tests/evidence/test_quality/",
        "hygiene_contract_path": "tools/test_hygiene_contract_v1.json",
        "allowed_authority_tiers": ["assurance"],
        "allowed_techniques": ["mutation", "bva_bve", "example"],
        "allowed_falsifier_kinds": ["mutation", "counterexample"],
        "allowed_falsifier_statuses": ["killed", "reproduced"],
        "quality_requirements": [
            {
                "rule_id": "assurance",
                "minimum_oracle_grade": 2,
                "required_falsifier_kinds": ["mutation"],
            }
        ],
    }


def _hygiene_packet(repo: Path) -> dict[str, object]:
    source_path = "tools/example_gate.py"
    test_path = "tests/test_example_gate.py"
    node_id = f"{test_path}::test_missing_oracle_rejects"
    return {
        "schema": "zenodex/test-hygiene-evidence/v1",
        "evidence_id": "THV1-20260806-quality-example",
        "created_date": "2026-08-06",
        "claim_scope": "The example checker rejects missing quality obligations.",
        "change_kind": "assurance_infrastructure",
        "risk_class": "assurance",
        "invariant_ids": ["TEST-QUALITY-V2-CLOSED"],
        "failure_modes": ["critical change proceeds without quality evidence"],
        "source_pins": [{"path": source_path, "sha256": _sha256(repo / source_path)}],
        "removed_paths": [],
        "test_pins": [
            {
                "path": test_path,
                "sha256": _sha256(repo / test_path),
                "node_ids": [node_id],
            }
        ],
        "evidence_families": [
            "negative_regression",
            "boundary",
            "mutation",
        ],
        "aaa": {
            "status": "applied",
            "reason": "The focused checker test has one setup and exact rejection.",
        },
        "reject_is_noop": {
            "status": "applied",
            "reason": "The checker does not mutate repository evidence on rejection.",
        },
        "boundary_dimensions": [{"name": "oracle grade", "points": ["one", "two", "three"]}],
        "mutations": [
            {
                "description": "omit the linked V2 quality obligation",
                "killed_by": node_id,
            }
        ],
        "nonclaims": ["This fixture does not establish production readiness."],
    }


def _quality_packet() -> dict[str, object]:
    node_id = "tests/test_example_gate.py::test_missing_oracle_rejects"
    return {
        "schema": "zenodex/test-quality-evidence/v2",
        "evidence_id": "TQV2-20260806-quality-example",
        "created_date": "2026-08-06",
        "hygiene_evidence_id": "THV1-20260806-quality-example",
        "claim": "Every selected critical path has a linked obligation-quality record.",
        "promotion_scope": "The diff gate may report structural V2 quality compliance.",
        "authority_tier": "assurance",
        "authority_surface": ["tools/example_gate.py"],
        "failure_model": [
            {
                "id": "QF-MISSING",
                "description": "An agent supplies technique labels without an executable oracle.",
                "severity": "high",
                "coordinate_changed": "Remove the V2 packet linked to selected V1 evidence.",
            }
        ],
        "ripr": {
            "reach": "Select a critical changed path through the V1 path classifier.",
            "infect": "The selected evidence lacks its required quality obligation.",
            "propagate": "The missing link reaches the V2 evidence selection result.",
            "reveal": "The checker raises the stable missing-obligation rejection.",
        },
        "representation_review": {
            "invalid_state_status": "guarded",
            "action": "Use an exact schema and one unique quality packet per hygiene packet.",
            "semantic_source_multiplicity": 1,
            "independent_oracle_exception": False,
        },
        "technique": {
            "primary": "mutation",
            "secondary": ["bva_bve"],
            "rejected_alternatives": [
                {
                    "technique": "example",
                    "reason": "A passing example would not kill an omitted-obligation guard.",
                }
            ],
        },
        "oracle": {
            "description": "Exact typed checker rejection and unchanged evidence files.",
            "independence_grade": 2,
            "independent_source": "Reviewed contract decision table and fixed fixture packet.",
            "exact_error_or_precedence": "Missing V2 obligation rejects after V1 selection succeeds.",
            "reject_is_noop": {
                "status": "applied",
                "reason": "Validation is read-only and must leave all evidence files unchanged.",
                "snapshot_fields": ["evidence file hashes", "selected V1 packet"],
            },
        },
        "falsifiers": [
            {
                "id": "MISSING-V2-LINK",
                "kind": "mutation",
                "status": "killed",
                "semantic_change": "Delete the V2 packet after V1 evidence selection succeeds.",
                "killed_by_node_ids": [node_id],
                "result": "The checker raises selected hygiene evidence lacks V2 quality obligation.",
                "smallest_witness": "One changed critical file, one V1 packet, and zero V2 packets.",
            }
        ],
        "minimal_test_inventory": {
            "added": [node_id],
            "merged_or_deleted": [],
            "protected": [],
            "rationale": "One mutation-killing regression covers the missing-link obligation.",
        },
        "counterexample": {
            "status": "not_applicable",
            "rationale": "The retained executable mutant is already the smallest witness.",
            "retained_path": None,
            "replay_command": None,
            "minimized_size": None,
        },
        "metrics": {
            "production_sloc_delta": 0,
            "test_sloc_delta": 1,
            "support_sloc_delta": 1,
            "runtime_delta": "Below one second in the isolated checker regression.",
        },
        "review_decision": {"ready": True, "blockers": []},
        "nonclaims": ["Structural V2 compliance does not prove oracle truthfulness."],
    }


def _fixture_repo(tmp_path: Path) -> tuple[Path, Path, Path]:
    repo = tmp_path / "repo"
    source = repo / "tools/example_gate.py"
    test = repo / "tests/test_example_gate.py"
    source.parent.mkdir(parents=True)
    test.parent.mkdir(parents=True)
    source.write_text("VALUE = 1\n", encoding="utf-8")
    test.write_text("def test_missing_oracle_rejects():\n    assert True\n", encoding="utf-8")
    hygiene_contract = repo / "tools/test_hygiene_contract_v1.json"
    quality_contract = repo / "tools/test_quality_contract_v2.json"
    _write_json(hygiene_contract, _hygiene_contract())
    _write_json(quality_contract, _quality_contract())
    _write_json(
        repo / "tests/evidence/test_hygiene/THV1-20260806-quality-example.json",
        _hygiene_packet(repo),
    )
    return repo, quality_contract, repo / "tests/evidence/test_quality"


def test_selected_hygiene_packet_requires_v2_quality_obligation(
    tmp_path: Path,
) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)

    with pytest.raises(TestHygieneError, match="lacks V2 quality obligation"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
            changed_paths=[ChangedPathV1(status="M", path="tools/example_gate.py")],
        )


def test_complete_obligation_links_exact_executable_killer(tmp_path: Path) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    _write_json(
        quality_evidence / "TQV2-20260806-quality-example.json",
        _quality_packet(),
    )

    report = check_test_quality_repository(
        repo_root=repo,
        quality_contract_path=quality_contract,
        quality_evidence_dir=quality_evidence,
        changed_paths=[ChangedPathV1(status="M", path="tools/example_gate.py")],
    )

    assert report["ok"] is True
    assert report["selected_quality_evidence_ids"] == ["TQV2-20260806-quality-example"]
    assert report["pytest_node_ids"] == ["tests/test_example_gate.py::test_missing_oracle_rejects"]


def test_placeholder_ripr_rejects(tmp_path: Path) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    packet = _quality_packet()
    packet["ripr"]["reveal"] = "N/A"  # type: ignore[index]
    _write_json(quality_evidence / "TQV2-20260806-quality-example.json", packet)

    with pytest.raises(TestHygieneError, match="too short|placeholder"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
        )


def test_oracle_grade_below_rule_minimum_rejects(tmp_path: Path) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    packet = _quality_packet()
    packet["oracle"]["independence_grade"] = 1  # type: ignore[index]
    _write_json(quality_evidence / "TQV2-20260806-quality-example.json", packet)

    with pytest.raises(TestHygieneError, match="below the required minimum"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
            changed_paths=[ChangedPathV1(status="M", path="tools/example_gate.py")],
        )


def test_required_executed_mutation_cannot_be_replaced_by_prose_counterexample(
    tmp_path: Path,
) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    packet = _quality_packet()
    packet["falsifiers"][0]["kind"] = "counterexample"  # type: ignore[index]
    packet["falsifiers"][0]["status"] = "reproduced"  # type: ignore[index]
    _write_json(quality_evidence / "TQV2-20260806-quality-example.json", packet)

    with pytest.raises(TestHygieneError, match="missing required executed falsifier"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
            changed_paths=[ChangedPathV1(status="M", path="tools/example_gate.py")],
        )


def test_falsifier_must_be_killed_by_selected_pinned_node(tmp_path: Path) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    packet = _quality_packet()
    packet["falsifiers"][0]["killed_by_node_ids"] = [  # type: ignore[index]
        "tests/test_example_gate.py::test_unpinned"
    ]
    _write_json(quality_evidence / "TQV2-20260806-quality-example.json", packet)

    with pytest.raises(TestHygieneError, match="not a selected pinned node"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
            changed_paths=[ChangedPathV1(status="M", path="tools/example_gate.py")],
        )


def test_quality_packets_are_append_only(tmp_path: Path) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    _write_json(
        quality_evidence / "TQV2-20260806-quality-example.json",
        _quality_packet(),
    )

    with pytest.raises(TestHygieneError, match="quality evidence packets are append-only"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
            changed_paths=[
                ChangedPathV1(
                    status="M",
                    path="tests/evidence/test_quality/TQV2-20260806-quality-example.json",
                )
            ],
        )


def test_quality_packet_must_link_existing_hygiene_evidence(tmp_path: Path) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    packet = _quality_packet()
    packet["hygiene_evidence_id"] = "THV1-20260806-missing"
    _write_json(quality_evidence / "TQV2-20260806-quality-example.json", packet)

    with pytest.raises(TestHygieneError, match="linked hygiene evidence does not exist"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
        )


def test_default_contract_matches_all_v1_rule_ids() -> None:
    contract = load_quality_contract(DEFAULT_CONTRACT)

    rule_ids = {item.rule_id for item in contract.requirements}

    assert rule_ids == {
        "economic_and_proof_core",
        "authority_and_runtime_adapters",
        "assurance_and_promotion_tooling",
        "critical_test_evidence",
    }


def test_quality_contract_cannot_omit_a_hygiene_rule(tmp_path: Path) -> None:
    repo, quality_contract, quality_evidence = _fixture_repo(tmp_path)
    contract = _quality_contract()
    contract["quality_requirements"] = []
    _write_json(quality_contract, contract)

    with pytest.raises(TestHygieneError, match="expected non-empty list|exactly match"):
        check_test_quality_repository(
            repo_root=repo,
            quality_contract_path=quality_contract,
            quality_evidence_dir=quality_evidence,
        )


def test_repository_v2_contract_and_bootstrap_packet_are_structurally_valid() -> None:
    report = check_test_quality_repository(
        quality_contract_path=DEFAULT_CONTRACT,
        quality_evidence_dir=DEFAULT_EVIDENCE_DIR,
    )

    assert report["ok"] is True
    assert report["contract_schema"] == "zenodex/test-quality-contract/v2"
    packet_count = report["quality_packet_count"]
    assert isinstance(packet_count, int)
    assert packet_count >= 1


def test_pull_request_workflow_runs_diff_aware_v2_gate() -> None:
    workflow = Path(".github/workflows/test-hygiene.yml").read_text(encoding="utf-8")

    assert (
        'python tools/run_test_quality_gate_v2.py --base-ref "origin/${{ github.base_ref }}"'
        in workflow
    )


def test_codeowners_protects_test_quality_authority_paths() -> None:
    codeowners = Path(".github/CODEOWNERS").read_text(encoding="utf-8")

    required_patterns = {
        "/.github/",
        "/agent_skills/",
        "/docs/",
        "/tests/",
        "/tools/",
    }
    declared_patterns = {
        line.split()[0]
        for line in codeowners.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }

    assert required_patterns <= declared_patterns


def test_critical_quality_gate_validates_v2_contract() -> None:
    gate = Path("tools/run_critical_quality_gate.sh").read_text(encoding="utf-8")

    assert '"$PY" tools/check_test_quality_v2.py' in gate
