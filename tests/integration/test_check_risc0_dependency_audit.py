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
    assert len(policy["dispositions"]) == 8
    assert {row["category"] for row in policy["dispositions"]} == {
        "vulnerability"
    }
    assert policy["production_authority"] is False
    assert len(policy_sha256) == 64


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


def test_unregistered_top_level_zk_lockfile_rejects(tmp_path: Path) -> None:
    for spec in checker.REVIEWED_WORKSPACES:
        destination = tmp_path / spec.lockfile
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / spec.lockfile, destination)
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
