from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from tools.check_test_hygiene_v1 import (
    DEFAULT_CONTRACT,
    DEFAULT_EVIDENCE_DIR,
    REPO_ROOT,
    ChangedPathV1,
    TestHygieneError,
    _parse_git_name_status,
    check_repository,
)
from tools.test_hygiene_model_v1 import load_contract


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _contract() -> dict[str, object]:
    return {
        "schema": "zenodex/test-hygiene-contract/v1",
        "evidence_schema": "zenodex/test-hygiene-evidence/v1",
        "evidence_path_prefix": "tests/evidence/test_hygiene/",
        "allowed_change_kinds": [
            "behavior_change",
            "bug_fix",
            "refactor",
            "assurance_infrastructure",
            "evidence_correction",
        ],
        "allowed_evidence_families": [
            "aaa_regression",
            "bdd_scenario",
            "negative_regression",
            "boundary",
            "property",
            "metamorphic",
            "differential",
            "stateful",
            "fuzz",
            "mutation",
            "formal",
            "replay",
        ],
        "strong_evidence_families": [
            "property",
            "metamorphic",
            "differential",
            "stateful",
            "fuzz",
            "mutation",
            "formal",
            "replay",
        ],
        "critical_path_rules": [
            {
                "id": "core",
                "include_globs": ["src/core/**"],
                "exclude_globs": [],
                "required_families": ["negative_regression", "boundary"],
                "minimum_strong_families": 1,
            },
            {
                "id": "critical_tests",
                "include_globs": ["tests/core/**"],
                "exclude_globs": ["tests/evidence/test_hygiene/**"],
                "required_families": ["negative_regression"],
                "minimum_strong_families": 1,
            },
        ],
    }


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def _packet(
    repo: Path,
    *,
    source_path: str = "src/core/example.py",
    test_path: str = "tests/core/test_example.py",
) -> dict[str, object]:
    return {
        "schema": "zenodex/test-hygiene-evidence/v1",
        "evidence_id": "THV1-20260805-example",
        "created_date": "2026-08-05",
        "claim_scope": "The example critical change is rejected when its invariant is violated.",
        "change_kind": "bug_fix",
        "risk_class": "critical",
        "invariant_ids": ["EXAMPLE-REJECT-IS-NOOP"],
        "failure_modes": ["invalid input mutates authoritative state"],
        "source_pins": [{"path": source_path, "sha256": _sha256(repo / source_path)}],
        "removed_paths": [],
        "test_pins": [
            {
                "path": test_path,
                "sha256": _sha256(repo / test_path),
                "node_ids": [f"{test_path}::test_invalid_input_rejects_without_mutation"],
            }
        ],
        "evidence_families": [
            "aaa_regression",
            "negative_regression",
            "boundary",
            "mutation",
        ],
        "aaa": {
            "status": "applied",
            "reason": "The focused regression has one setup, one invocation, and exact assertions.",
        },
        "reject_is_noop": {
            "status": "applied",
            "reason": "The regression asserts the exact reject and unchanged state.",
        },
        "boundary_dimensions": [
            {"name": "authorization", "points": ["missing", "invalid", "valid"]}
        ],
        "mutations": [
            {
                "description": "accept invalid authorization",
                "killed_by": (f"{test_path}::test_invalid_input_rejects_without_mutation"),
            }
        ],
        "nonclaims": ["This packet does not establish production readiness."],
    }


def _fixture_repo(tmp_path: Path) -> tuple[Path, Path, Path]:
    repo = tmp_path / "repo"
    source = repo / "src/core/example.py"
    test = repo / "tests/core/test_example.py"
    source.parent.mkdir(parents=True)
    test.parent.mkdir(parents=True)
    source.write_text("VALUE = 1\n", encoding="utf-8")
    test.write_text(
        "def test_invalid_input_rejects_without_mutation():\n    assert True\n",
        encoding="utf-8",
    )
    contract = repo / "tools/test_hygiene_contract_v1.json"
    _write_json(contract, _contract())
    evidence_dir = repo / "tests/evidence/test_hygiene"
    return repo, contract, evidence_dir


def test_changed_critical_path_requires_evidence_packet(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    changed = [ChangedPathV1(status="M", path="src/core/example.py")]

    # Act / Assert
    with pytest.raises(TestHygieneError, match="uncovered critical path"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=changed,
        )


def test_current_pins_and_strong_evidence_cover_critical_change(
    tmp_path: Path,
) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    _write_json(evidence_dir / "THV1-20260805-example.json", _packet(repo))

    # Act
    report = check_repository(
        repo_root=repo,
        contract_path=contract,
        evidence_dir=evidence_dir,
        changed_paths=[ChangedPathV1(status="M", path="src/core/example.py")],
    )

    # Assert
    assert report["ok"] is True
    assert report["covered_critical_paths"] == ["src/core/example.py"]
    assert report["evidence_by_critical_path"] == {"src/core/example.py": "THV1-20260805-example"}
    assert report["pytest_node_ids"] == [
        "tests/core/test_example.py::test_invalid_input_rejects_without_mutation"
    ]


def test_stale_source_pin_rejects_packet(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    packet = _packet(repo)
    packet["source_pins"][0]["sha256"] = "0" * 64  # type: ignore[index]
    _write_json(evidence_dir / "THV1-20260805-example.json", packet)

    # Act / Assert
    with pytest.raises(TestHygieneError, match="source sha256 drift"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=[ChangedPathV1(status="M", path="src/core/example.py")],
        )


def test_required_boundary_family_needs_boundary_inventory(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    packet = _packet(repo)
    packet["boundary_dimensions"] = []
    _write_json(evidence_dir / "THV1-20260805-example.json", packet)

    # Act / Assert
    with pytest.raises(TestHygieneError, match="boundary evidence requires dimensions"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=[ChangedPathV1(status="M", path="src/core/example.py")],
        )


def test_named_mutation_must_be_killed_by_pinned_node(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    packet = _packet(repo)
    packet["mutations"][0]["killed_by"] = (  # type: ignore[index]
        "tests/core/test_example.py::test_unpinned"
    )
    _write_json(evidence_dir / "THV1-20260805-example.json", packet)

    # Act / Assert
    with pytest.raises(TestHygieneError, match="mutation killer is not a pinned node"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=[ChangedPathV1(status="M", path="src/core/example.py")],
        )


def test_existing_evidence_packets_are_append_only(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    packet_path = "tests/evidence/test_hygiene/THV1-20260805-example.json"
    _write_json(repo / packet_path, _packet(repo))

    # Act / Assert
    with pytest.raises(TestHygieneError, match="evidence packets are append-only"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=[
                ChangedPathV1(status="M", path=packet_path),
                ChangedPathV1(status="M", path="src/core/example.py"),
            ],
        )


def test_deleted_test_requires_explicit_replacement(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    (repo / "tests/core/test_example.py").unlink()

    # Act / Assert
    with pytest.raises(TestHygieneError, match="uncovered critical path"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=[ChangedPathV1(status="D", path="tests/core/test_example.py")],
        )


def test_deleted_test_replacement_must_be_a_pinned_test(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    packet = _packet(repo)
    replacement_path = "tests/core/test_replacement.py"
    replacement = repo / replacement_path
    replacement.write_text("def test_replacement():\n    assert True\n", encoding="utf-8")
    packet["test_pins"] = [
        {
            "path": replacement_path,
            "sha256": _sha256(replacement),
            "node_ids": [f"{replacement_path}::test_replacement"],
        }
    ]
    packet["removed_paths"] = [
        {
            "path": "tests/core/test_example.py",
            "reason": "replace the old regression",
            "replacement_paths": ["src/core/example.py"],
        }
    ]
    packet["mutations"] = [
        {
            "description": "accept invalid authorization",
            "killed_by": f"{replacement_path}::test_replacement",
        }
    ]
    (repo / "tests/core/test_example.py").unlink()
    _write_json(evidence_dir / "THV1-20260805-example.json", packet)

    # Act / Assert
    with pytest.raises(TestHygieneError, match="deleted test replacement must be a pinned test"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=[ChangedPathV1(status="D", path="tests/core/test_example.py")],
        )


def test_path_traversal_in_packet_rejects(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    packet = _packet(repo)
    packet["source_pins"][0]["path"] = "../outside.py"  # type: ignore[index]
    _write_json(evidence_dir / "THV1-20260805-example.json", packet)

    # Act / Assert
    with pytest.raises(TestHygieneError, match="non-portable path"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
        )


def test_symlinked_source_pin_rejects(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    source = repo / "src/core/example.py"
    outside = tmp_path / "outside.py"
    outside.write_text("VALUE = 1\n", encoding="utf-8")
    source.unlink()
    source.symlink_to(outside)
    _write_json(evidence_dir / "THV1-20260805-example.json", _packet(repo))

    # Act / Assert
    with pytest.raises(TestHygieneError, match="pinned source path uses a symlink"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
            changed_paths=[ChangedPathV1(status="M", path="src/core/example.py")],
        )


def test_nul_git_parser_preserves_unicode_and_normalizes_rename() -> None:
    # Arrange
    output = ("A\0src/core/café.py\0R100\0src/core/old.py\0src/core/new.py\0").encode()

    # Act
    changes = _parse_git_name_status(output)

    # Assert
    assert changes == (
        ChangedPathV1(status="A", path="src/core/café.py"),
        ChangedPathV1(status="D", path="src/core/old.py"),
        ChangedPathV1(status="A", path="src/core/new.py"),
    )


def test_noncritical_document_change_needs_no_packet(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)

    # Act
    report = check_repository(
        repo_root=repo,
        contract_path=contract,
        evidence_dir=evidence_dir,
        changed_paths=[ChangedPathV1(status="M", path="docs/note.md")],
    )

    # Assert
    assert report["ok"] is True
    assert report["critical_path_count"] == 0
    assert report["pytest_node_ids"] == []


def test_unknown_contract_field_rejects_fail_closed(tmp_path: Path) -> None:
    # Arrange
    repo, contract, evidence_dir = _fixture_repo(tmp_path)
    value = _contract()
    value["allow_uncovered"] = True
    _write_json(contract, value)

    # Act / Assert
    with pytest.raises(TestHygieneError, match="unknown fields"):
        check_repository(
            repo_root=repo,
            contract_path=contract,
            evidence_dir=evidence_dir,
        )


def test_repository_contract_and_bootstrap_packet_are_structurally_valid() -> None:
    # Arrange / Act
    report = check_repository(
        contract_path=DEFAULT_CONTRACT,
        evidence_dir=DEFAULT_EVIDENCE_DIR,
    )

    # Assert
    assert report["ok"] is True
    assert report["contract_schema"] == "zenodex/test-hygiene-contract/v1"
    packet_count = report["evidence_packet_count"]
    assert isinstance(packet_count, int)
    assert packet_count >= 1


def test_default_contract_retains_mandatory_critical_path_probes() -> None:
    # Arrange
    contract = load_contract(DEFAULT_CONTRACT)
    probes = [
        "src/core/value_transition.py",
        "src/state/authoritative_state.py",
        "src/kernels/dex/model.yaml",
        "src/fire/kernel/settlement.py",
        "src/agents/intent_signer.py",
        "src/integration/zeno_ledger.py",
        "src/tau_specs/policy.tau",
        "config/proof_profiles/root.json",
        "config/verifier_contracts/root.json",
        "zk/global_settlement/src/lib.rs",
        "formal/GlobalSettlement.tla",
        "lean-mathlib/Proofs.lean",
        "tools/check_future_gate.py",
        "tools/run_future_gate.sh",
        "tools/test_hygiene_future_v1.py",
        "tools/test_quality_future_v2.py",
        ".github/workflows/future.yml",
        "agent_skills/zeno-future/SKILL.md",
        "agent_skills/zenodex-future/SKILL.md",
        "docs/testing/TEST_HYGIENE_CONTRACT_V1.md",
        "docs/testing/TEST_QUALITY_CONTRACT_V2.md",
        "docs/testing/templates/future.yaml",
        "docs/claims_registry.yaml",
        "tests/core/test_value_transition.py",
        "tests/integration/test_zeno_ledger.py",
        "tests/test_check_future_gate.py",
    ]

    # Act
    uncovered = [path for path in probes if not any(rule.matches(path) for rule in contract.rules)]

    # Assert
    assert uncovered == []


def test_pull_request_ci_runs_diff_aware_quality_overlay() -> None:
    # Arrange
    workflow = (REPO_ROOT / ".github/workflows/test-hygiene.yml").read_text(encoding="utf-8")

    # Act / Assert
    assert (
        'python tools/run_test_quality_gate_v2.py --base-ref "origin/${{ github.base_ref }}"'
        in workflow
    )


def test_critical_quality_gate_validates_static_hygiene_contract() -> None:
    # Arrange
    gate = (REPO_ROOT / "tools/run_critical_quality_gate.sh").read_text(encoding="utf-8")

    # Act / Assert
    assert '"$PY" tools/check_test_hygiene_v1.py' in gate
