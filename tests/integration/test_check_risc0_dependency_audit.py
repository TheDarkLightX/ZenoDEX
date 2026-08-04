from __future__ import annotations

import hashlib
import json
import shutil
import tomllib
from pathlib import Path

import pytest

from tools import check_risc0_dependency_audit as checker

ROOT = Path(__file__).resolve().parents[2]


def _entry(advisory_id: str, package: str, version: str) -> dict[str, object]:
    return {
        "advisory": {"id": advisory_id},
        "package": {"name": package, "version": version},
    }


def _payload(
    *,
    vulnerabilities: tuple[tuple[str, str, str], ...] = (),
    warnings: dict[str, tuple[tuple[str, str, str], ...]] | None = None,
) -> dict[str, object]:
    vulnerability_rows = [_entry(*row) for row in vulnerabilities]
    warning_rows = {
        category: [_entry(*row) for row in rows]
        for category, rows in (warnings or {}).items()
    }
    return {
        "database": {"advisory-count": 1159, "last-commit": None, "last-updated": None},
        "vulnerabilities": {
            "count": len(vulnerability_rows),
            "found": bool(vulnerability_rows),
            "list": vulnerability_rows,
        },
        "warnings": warning_rows,
    }


def _policy_payloads() -> dict[str, object]:
    vulnerabilities = (
        ("RUSTSEC-2023-0071", "rsa", "0.9.10"),
        ("RUSTSEC-2025-0055", "tracing-subscriber", "0.2.25"),
        ("RUSTSEC-2026-0220", "ruint", "1.19.0"),
    )
    state_payload = _payload(
        vulnerabilities=vulnerabilities,
        warnings={
            "unmaintained": (("RUSTSEC-2025-0141", "bincode", "1.3.3"),),
        },
    )
    recursive_v2_payload = _payload(
        vulnerabilities=vulnerabilities,
        warnings={
            "unmaintained": (("RUSTSEC-2025-0141", "bincode", "1.3.3"),),
        },
    )
    current_risc0_payload = _payload(
        vulnerabilities=(
            ("RUSTSEC-2023-0071", "rsa", "0.9.10"),
            ("RUSTSEC-2025-0055", "tracing-subscriber", "0.2.25"),
            ("RUSTSEC-2026-0220", "ruint", "1.19.0"),
        ),
        warnings={
            "unmaintained": (("RUSTSEC-2025-0141", "bincode", "1.3.3"),),
        },
    )
    return {
        "state_proof_risc0": state_payload,
        "recursive_stark_v2_risc0": recursive_v2_payload,
        "recursive_stark_v2_active_reproof_risc0": recursive_v2_payload,
        "zrpf_risc0": current_risc0_payload,
        "zrpf_protocol": _payload(),
    }


def _dispositions() -> frozenset[checker.DispositionKey]:
    policy, _ = checker.load_policy()
    return checker._disposition_keys(policy)


def _copy_registered_locks(destination_root: Path) -> None:
    for spec in checker.REVIEWED_WORKSPACES:
        destination = destination_root / spec.lockfile
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / spec.lockfile, destination)


def test_accepts_clean_well_formed_audit() -> None:
    report = checker.evaluate_audit_payload(
        _payload(),
        workspace_id="zrpf_protocol",
        dispositions=_dispositions(),
    )

    assert report["ok"] is True
    assert report["errors"] == []
    assert report["vulnerabilities"] == []
    assert report["warnings"] == []


@pytest.mark.parametrize(
    "payload",
    [
        {},
        {"database": {}, "vulnerabilities": {}, "warnings": {}},
        {
            "database": {"advisory-count": True},
            "vulnerabilities": {"count": False, "found": 0, "list": []},
            "warnings": {},
        },
    ],
)
def test_rejects_empty_or_malformed_audit(payload: object) -> None:
    report = checker.evaluate_audit_payload(
        payload,
        workspace_id="zrpf_protocol",
        dispositions=_dispositions(),
    )

    assert report["ok"] is False
    assert report["errors"]


def test_rejects_vulnerability_without_exact_disposition() -> None:
    report = checker.evaluate_audit_payload(
        _payload(
            vulnerabilities=(("RUSTSEC-2026-0185", "quinn-proto", "0.11.14"),)
        ),
        workspace_id="state_proof_risc0",
        dispositions=_dispositions(),
    )

    assert report["ok"] is False
    assert report["errors"] == [
        "undisposed vulnerability: RUSTSEC-2026-0185 quinn-proto 0.11.14"
    ]


def test_accepts_only_workspace_package_and_version_exact_disposition() -> None:
    payload = _payload(vulnerabilities=(("RUSTSEC-2023-0071", "rsa", "0.9.10"),))
    accepted = checker.evaluate_audit_payload(
        payload,
        workspace_id="zrpf_risc0",
        dispositions=_dispositions(),
    )
    wrong_workspace = checker.evaluate_audit_payload(
        payload,
        workspace_id="zrpf_protocol",
        dispositions=_dispositions(),
    )
    wrong_version = checker.evaluate_audit_payload(
        _payload(vulnerabilities=(("RUSTSEC-2023-0071", "rsa", "0.9.9"),)),
        workspace_id="zrpf_risc0",
        dispositions=_dispositions(),
    )

    assert accepted["ok"] is True
    assert accepted["applied_dispositions"] == [
        ["zrpf_risc0", "vulnerability", "RUSTSEC-2023-0071", "rsa", "0.9.10"]
    ]
    assert wrong_workspace["ok"] is False
    assert wrong_version["ok"] is False


@pytest.mark.parametrize("category", ["unsound", "yanked"])
def test_denied_warning_categories_fail_closed(category: str) -> None:
    if category == "yanked":
        warning: dict[str, object] = {
            "package": {"name": "removed-crate", "version": "1.0.0"}
        }
        payload = _payload()
        payload["warnings"] = {category: [warning]}
    else:
        payload = _payload(
            warnings={category: (("RUSTSEC-2026-0190", "anyhow", "1.0.101"),)}
        )

    report = checker.evaluate_audit_payload(
        payload,
        workspace_id="recursive_stark_v2_risc0",
        dispositions=_dispositions(),
    )

    assert report["ok"] is False
    assert any(f"denied {category} warning" in error for error in report["errors"])


def test_yanked_spin_disposition_requires_lock_bound_authority() -> None:
    payload = _payload()
    payload["warnings"] = {
        "yanked": [{"package": {"name": "spin", "version": "0.9.8"}}]
    }
    unbound = checker.evaluate_audit_payload(
        payload,
        workspace_id="zrpf_risc0",
        dispositions=_dispositions(),
    )
    wrong_workspace = checker.evaluate_audit_payload(
        payload,
        workspace_id="zrpf_protocol",
        dispositions=_dispositions(),
    )
    wrong_version = _payload()
    wrong_version["warnings"] = {
        "yanked": [{"package": {"name": "spin", "version": "0.9.7"}}]
    }
    rejected_version = checker.evaluate_audit_payload(
        wrong_version,
        workspace_id="zrpf_risc0",
        dispositions=_dispositions(),
    )

    assert unbound["ok"] is False
    assert unbound["applied_dispositions"] == []
    assert unbound["errors"] == [
        "denied yanked warning: no-advisory-id spin 0.9.8"
    ]
    assert wrong_workspace["ok"] is False
    assert rejected_version["ok"] is False


def test_public_payload_evaluator_exposes_no_lock_authority_parameter() -> None:
    with pytest.raises(TypeError):
        checker.evaluate_audit_payload(
            _payload(),
            workspace_id="zrpf_risc0",
            dispositions=_dispositions(),
            lock_bound_yanked_dispositions=frozenset(),  # type: ignore[call-arg]
        )


def test_duplicate_cargo_findings_reject() -> None:
    duplicated_vulnerability = _payload(
        vulnerabilities=(
            ("RUSTSEC-2023-0071", "rsa", "0.9.10"),
            ("RUSTSEC-2023-0071", "rsa", "0.9.10"),
        )
    )
    duplicated_warning = _payload()
    duplicated_warning["warnings"] = {
        "yanked": [
            {"package": {"name": "spin", "version": "0.9.8"}},
            {"package": {"name": "spin", "version": "0.9.8"}},
        ]
    }

    vulnerability_report = checker.evaluate_audit_payload(
        duplicated_vulnerability,
        workspace_id="zrpf_risc0",
        dispositions=_dispositions(),
    )
    warning_report = checker.evaluate_audit_payload(
        duplicated_warning,
        workspace_id="zrpf_risc0",
        dispositions=_dispositions(),
    )

    assert vulnerability_report["ok"] is False
    assert vulnerability_report["errors"] == [
        "duplicate cargo-audit vulnerability finding: RUSTSEC-2023-0071 rsa 0.9.10"
    ]
    assert warning_report["ok"] is False
    assert warning_report["errors"] == [
        "denied yanked warning: no-advisory-id spin 0.9.8",
        "duplicate cargo-audit warning finding: yanked no-advisory-id spin 0.9.8",
    ]


def test_unmaintained_warning_is_recorded_without_authority() -> None:
    report = checker.evaluate_audit_payload(
        _payload(
            warnings={
                "unmaintained": (("RUSTSEC-2025-0141", "bincode", "1.3.3"),)
            }
        ),
        workspace_id="state_proof_risc0",
        dispositions=_dispositions(),
    )

    assert report["ok"] is True
    assert report["warnings"] == [
        {
            "advisory_id": "RUSTSEC-2025-0141",
            "category": "unmaintained",
            "disposition_applied": False,
            "package": "bincode",
            "version": "1.3.3",
        }
    ]


def test_unknown_warning_category_rejects() -> None:
    report = checker.evaluate_audit_payload(
        _payload(warnings={"future-category": (("RUSTSEC-2099-0001", "x", "1.0.0"),)}),
        workspace_id="state_proof_risc0",
        dispositions=_dispositions(),
    )

    assert report["ok"] is False
    assert report["errors"] == ["unknown cargo-audit warning category: 'future-category'"]


def test_policy_pins_exact_workspaces_and_scoped_advisories() -> None:
    policy, policy_sha256 = checker.load_policy()

    assert policy["workspaces"] == checker._workspace_rows()
    assert checker._disposition_keys(policy) == checker.PERMITTED_DISPOSITION_KEYS
    assert len(policy["dispositions"]) == 16
    assert {row["category"] for row in policy["dispositions"]} == {
        "vulnerability",
        "yanked",
    }
    ruint_dispositions = [
        row
        for row in policy["dispositions"]
        if row["advisory_id"] == "RUSTSEC-2026-0220"
    ]
    assert {row["workspace_id"] for row in ruint_dispositions} == {
        "state_proof_risc0",
        "recursive_stark_v2_risc0",
        "recursive_stark_v2_active_reproof_risc0",
        "zrpf_risc0",
    }
    for row in ruint_dispositions:
        assert row["scope"] == "experimental_risc0_dependency_audit_only"
        assert row["production_authority"] is False
        assert "risc0-binfmt 3.0.4" in row["reachability"]
        assert "no calls to the advisory's affected" in row["reachability"]
        assert "fresh image IDs" in row["reachability"]
    spin_dispositions = [
        row for row in policy["dispositions"] if row["category"] == "yanked"
    ]
    assert {row["workspace_id"] for row in spin_dispositions} == {
        "state_proof_risc0",
        "recursive_stark_v2_risc0",
        "recursive_stark_v2_active_reproof_risc0",
        "zrpf_risc0",
    }
    for row in spin_dispositions:
        assert row["advisory_id"] == ""
        assert row["package"] == "spin"
        assert row["version"] == "0.9.8"
        assert row["lockfile_source"] == checker.CRATES_IO_REGISTRY_SOURCE
        assert row["lockfile_checksum"] == checker.SPIN_0_9_8_CHECKSUM
        assert row["production_authority"] is False
        assert "8/8 ZRPF guest ELF hashes and image IDs" in row["reachability"]
        assert "fresh image IDs" in row["reachability"]
    assert policy["production_authority"] is False
    assert len(policy_sha256) == 64


def test_policy_rejects_advisory_identity_shape_drift(tmp_path: Path) -> None:
    policy = json.loads(checker.DEFAULT_POLICY.read_bytes())
    vulnerability = next(
        row for row in policy["dispositions"] if row["category"] == "vulnerability"
    )
    yanked = next(row for row in policy["dispositions"] if row["category"] == "yanked")
    vulnerability["advisory_id"] = ""
    yanked["advisory_id"] = "RUSTSEC-2099-0001"
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(policy), encoding="utf-8")

    with pytest.raises(checker.AuditInputError):
        checker.load_policy(path)


@pytest.mark.parametrize(
    ("field", "replacement"),
    [
        ("lockfile_source", "registry+https://example.invalid/index"),
        ("lockfile_checksum", "0" * 64),
    ],
)
def test_policy_rejects_yanked_lock_identity_drift(
    tmp_path: Path,
    field: str,
    replacement: str,
) -> None:
    policy = json.loads(checker.DEFAULT_POLICY.read_bytes())
    yanked = next(row for row in policy["dispositions"] if row["category"] == "yanked")
    yanked[field] = replacement
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(policy), encoding="utf-8")

    with pytest.raises(checker.AuditInputError):
        checker.load_policy(path)


def test_spin_only_proof_identity_comparison_is_closed() -> None:
    path = ROOT / "docs/research/RISC0_SPIN_099_PROOF_IDENTITY_COMPARISON_20260804.json"
    comparison = json.loads(path.read_bytes())

    assert comparison["schema"] == "zenodex/risc0_spin_proof_identity_comparison/v1"
    assert comparison["source"] == {
        "commit": "c09ef94eb63ec2f1ff7e3ff4f6ce26fc0607eb6c",
        "tree": "6f166af77589efa1855363a14f5acdbfafa05ec4",
    }
    assert comparison["baseline"]["version"] == "0.9.8"
    assert comparison["trial"]["version"] == "0.9.9"
    assert comparison["lock_delta"]["unchanged_ruint_version"] == "1.19.0"
    patch_path = ROOT / comparison["lock_delta"]["patch_path"]
    assert hashlib.sha256(patch_path.read_bytes()).hexdigest() == comparison["lock_delta"][
        "patch_sha256"
    ]
    assert comparison["claims"]["compared_program_count"] == 8
    assert comparison["claims"]["all_compared_elf_hashes_changed"] is True
    assert comparison["claims"]["all_compared_image_ids_changed"] is True
    assert comparison["claims"]["production_authority"] is False
    assert len(comparison["programs"]) == 8
    assert {row["role"] for row in comparison["programs"]} == {
        "ordinary_spot_settlement",
        "semantic_epoch",
        "spot_value_leaf_v4",
        "structural_aggregate_l1",
        "structural_aggregate_l2",
        "v1_leaf_adapter",
        "value_aggregate_l1",
        "value_aggregate_l2",
    }
    assert all(
        row["baseline_elf_sha256"] != row["spin_0_9_9_elf_sha256"]
        and row["baseline_image_id"] != row["spin_0_9_9_image_id"]
        for row in comparison["programs"]
    )
    baseline_spin = (
        b'name = "spin"\n'
        b'version = "0.9.8"\n'
        b'source = "registry+https://github.com/rust-lang/crates.io-index"\n'
        b'checksum = "6980e8d7511241f8acf4aebddbb1ff938df5eebe98691418c4468d0b72a96a67"\n'
    )
    trial_spin = (
        b'name = "spin"\n'
        b'version = "0.9.9"\n'
        b'source = "registry+https://github.com/rust-lang/crates.io-index"\n'
        b'checksum = "3763264f6b73151db08c50ff20d7d8a0b8796e021cdea7ceedad07b80155fa0e"\n'
    )
    for lock_row in comparison["lock_delta"]["workspace_lockfiles"]:
        baseline = (ROOT / lock_row["path"]).read_bytes()
        assert baseline.count(baseline_spin) == 1
        assert hashlib.sha256(baseline).hexdigest() == lock_row["baseline_sha256"]
        trial = baseline.replace(baseline_spin, trial_spin, 1)
        assert hashlib.sha256(trial).hexdigest() == lock_row["trial_sha256"]


@pytest.mark.parametrize(
    ("field", "replacement"),
    [
        ("no_secret_input", 1),
        ("no_raw_untrusted_terminal_logging", 1),
        ("production_authority", True),
    ],
)
def test_policy_rejects_control_or_boolean_drift(
    tmp_path: Path,
    field: str,
    replacement: object,
) -> None:
    policy = json.loads(checker.DEFAULT_POLICY.read_bytes())
    policy["dispositions"][0][field] = replacement
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(policy), encoding="utf-8")

    with pytest.raises(checker.AuditInputError):
        checker.load_policy(path)


@pytest.mark.parametrize(
    "lockfile",
    [
        "zk/state_proof_risc0/Cargo.lock",
        "zk/recursive_stark_v2_risc0/Cargo.lock",
        "zk/recursive_stark_v2_active_reproof_risc0/Cargo.lock",
    ],
)
def test_active_risc0_workspaces_pin_patched_anyhow(lockfile: str) -> None:
    document = tomllib.loads((ROOT / lockfile).read_text(encoding="utf-8"))
    versions = {
        package["version"]
        for package in document["package"]
        if package["name"] == "anyhow"
    }

    assert versions == {"1.0.103"}


def test_five_workspace_report_records_lock_hashes_and_database_revision() -> None:
    revision = "1" * 40
    report = checker.check_audit_payloads(
        _policy_payloads(),
        advisory_database_revision=revision,
    )

    assert report["ok"] is True, report
    assert report["advisory_database_revision"] == revision
    assert report["production_authority"] is False
    assert [row["workspace_id"] for row in report["workspaces"]] == [
        spec.workspace_id for spec in checker.REVIEWED_WORKSPACES
    ]
    for row in report["workspaces"]:
        lockfile = ROOT / row["lockfile"]
        assert row["lockfile_sha256"] == hashlib.sha256(lockfile.read_bytes()).hexdigest()
        assert row["lockfile_size_bytes"] == lockfile.stat().st_size
        yanked = [
            warning for warning in row["warnings"] if warning["category"] == "yanked"
        ]
        if row["workspace_id"] in checker.RISC0_WORKSPACE_IDS:
            assert yanked == [
                {
                    "advisory_id": "",
                    "category": "yanked",
                    "disposition_applied": True,
                    "evidence_source": "policy_and_cargo_lock",
                    "package": "spin",
                    "version": "0.9.8",
                }
            ]
        else:
            assert yanked == []
    boundary_status = {
        row["workspace_id"]: row["retained_unsound_boundary_verified"]
        for row in report["workspaces"]
    }
    assert boundary_status == {
        workspace_id: False
        for workspace_id in (
            "state_proof_risc0",
            "recursive_stark_v2_risc0",
            "recursive_stark_v2_active_reproof_risc0",
            "zrpf_risc0",
            "zrpf_protocol",
        )
    }


def test_hosted_yanked_warning_deduplicates_against_lock_identity() -> None:
    payloads = _policy_payloads()
    state_payload = payloads["state_proof_risc0"]
    assert isinstance(state_payload, dict)
    warnings = state_payload["warnings"]
    assert isinstance(warnings, dict)
    warnings["yanked"] = [{"package": {"name": "spin", "version": "0.9.8"}}]

    report = checker.check_audit_payloads(
        payloads,
        advisory_database_revision="4" * 40,
    )

    assert report["ok"] is True, report
    state_report = next(
        row for row in report["workspaces"] if row["workspace_id"] == "state_proof_risc0"
    )
    assert [
        warning
        for warning in state_report["warnings"]
        if warning["category"] == "yanked"
    ] == [
        {
            "advisory_id": "",
            "category": "yanked",
            "disposition_applied": True,
            "evidence_source": "policy_and_cargo_lock",
            "package": "spin",
            "version": "0.9.8",
        }
    ]


@pytest.mark.parametrize(
    ("field", "original", "replacement"),
    [
        (
            "source",
            checker.CRATES_IO_REGISTRY_SOURCE,
            "registry+https://example.invalid/index",
        ),
        ("checksum", checker.SPIN_0_9_8_CHECKSUM, "0" * 64),
    ],
)
def test_lock_bound_yanked_identity_rejects_drift(
    tmp_path: Path,
    field: str,
    original: str,
    replacement: str,
) -> None:
    _copy_registered_locks(tmp_path)
    lockfile = tmp_path / "zk/state_proof_risc0/Cargo.lock"
    source = lockfile.read_text(encoding="utf-8")
    spin_block = (
        'name = "spin"\n'
        'version = "0.9.8"\n'
        f'source = "{checker.CRATES_IO_REGISTRY_SOURCE}"\n'
        f'checksum = "{checker.SPIN_0_9_8_CHECKSUM}"\n'
    )
    assert source.count(spin_block) == 1
    changed_block = spin_block.replace(original, replacement, 1)
    lockfile.write_text(source.replace(spin_block, changed_block, 1), encoding="utf-8")

    report = checker.check_audit_payloads(
        _policy_payloads(),
        advisory_database_revision="5" * 40,
        root=tmp_path,
    )

    assert report["ok"] is False
    state_report = next(
        row for row in report["workspaces"] if row["workspace_id"] == "state_proof_risc0"
    )
    assert state_report["ok"] is False
    assert state_report["errors"] == [
        "lock-bound yanked package identity mismatch: spin 0.9.8"
    ]
    assert field in {"source", "checksum"}


def test_unregistered_top_level_zk_lockfile_rejects(tmp_path: Path) -> None:
    _copy_registered_locks(tmp_path)
    unknown = tmp_path / "zk/unreviewed_prover/Cargo.lock"
    unknown.parent.mkdir(parents=True)
    unknown.write_text("version = 4\n", encoding="utf-8")

    report = checker.check_audit_payloads(
        _policy_payloads(),
        advisory_database_revision="2" * 40,
        root=tmp_path,
    )

    assert report["ok"] is False
    assert report["errors"] == ["reviewed workspace lockfile inventory mismatch"]


def test_payload_workspace_omission_rejects() -> None:
    payloads = _policy_payloads()
    payloads.pop("zrpf_protocol")

    report = checker.check_audit_payloads(
        payloads,
        advisory_database_revision="3" * 40,
    )

    assert report["ok"] is False
    assert "cargo-audit payload workspace set mismatch" in report["errors"]
    protocol = next(row for row in report["workspaces"] if row["workspace_id"] == "zrpf_protocol")
    assert protocol["ok"] is False


def test_dependency_workflow_pins_actions_and_preserves_no_secret_posture() -> None:
    workflow = (ROOT / ".github/workflows/dependency-assurance.yml").read_text(encoding="utf-8")

    assert "actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10" in workflow
    assert "actions/setup-python@ece7cb06caefa5fff74198d8649806c4678c61a1" in workflow
    assert "actions/setup-node@48b55a011bda9f5d6aeb4c2d9c7362e8dae4041e" in workflow
    assert "actions/upload-artifact@330a01c490aca151604b8cf639adc76d48f6c5d4" in workflow
    assert workflow.count("persist-credentials: false") == 3
    assert "secrets." not in workflow
    assert "pull_request_target" not in workflow
    assert "--output internal/risc0_dependency_audit.json" in workflow
