from __future__ import annotations

import copy
import importlib.util
import sys
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_proof_toolchain_lock", ROOT / "tools/check_proof_toolchain_lock.py"
)
assert SPEC is not None and SPEC.loader is not None
check_proof_toolchain_lock = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check_proof_toolchain_lock
SPEC.loader.exec_module(check_proof_toolchain_lock)


def _write_risc0_workspace(
    root: Path,
    *,
    workspace_name: str = "candidate_risc0",
    dependency_path: str = "host",
    requirement: str = "=3.0.6",
    resolved_versions: tuple[str, ...] = ("3.0.6",),
    include_checksum: bool = True,
    inherited: bool = False,
    host_disable_dev_mode: bool = True,
    guest_default_features_false: bool = True,
) -> Path:
    workspace = root / "zk" / workspace_name
    package = workspace / dependency_path
    package.mkdir(parents=True)

    feature_parts: list[str] = []
    if dependency_path == "host" and host_disable_dev_mode:
        feature_parts.append('features = ["disable-dev-mode"]')
    if dependency_path != "host" and guest_default_features_false:
        feature_parts.append("default-features = false")
    feature_suffix = ", " + ", ".join(feature_parts) if feature_parts else ""
    dependency_spec = f'{{ version = "{requirement}"{feature_suffix} }}'

    workspace_lines = [
        "[workspace]",
        'resolver = "2"',
        f'members = ["{dependency_path}"]',
    ]
    if inherited:
        workspace_lines.extend(("", "[workspace.dependencies]", f"risc0-zkvm = {dependency_spec}"))
        package_dependency = "{ workspace = true }"
    else:
        package_dependency = dependency_spec
    (workspace / "Cargo.toml").write_text("\n".join(workspace_lines) + "\n", encoding="utf-8")
    (package / "Cargo.toml").write_text(
        "\n".join(
            (
                "[package]",
                f'name = "{workspace_name}-{dependency_path.replace("/", "-")}"',
                'version = "0.1.0"',
                'edition = "2021"',
                "",
                "[dependencies]",
                f"risc0-zkvm = {package_dependency}",
            )
        )
        + "\n",
        encoding="utf-8",
    )

    lock_lines = ['version = 4', ""]
    for resolved_version in resolved_versions:
        lock_lines.extend(
            (
                "[[package]]",
                'name = "risc0-zkvm"',
                f'version = "{resolved_version}"',
                'source = "registry+https://github.com/rust-lang/crates.io-index"',
            )
        )
        if include_checksum:
            lock_lines.append('checksum = "' + "a" * 64 + '"')
        lock_lines.append("")
    (workspace / "Cargo.lock").write_text("\n".join(lock_lines), encoding="utf-8")
    return workspace


def _error_codes(report: dict[str, Any]) -> set[str]:
    return {finding["code"] for finding in report["findings"]}


def test_repo_proof_toolchain_lock_reports_known_legacy_quarantine() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)

    assert report["inventory_ok"], report["errors"]
    assert not report["ok"]
    assert report["status"] == "blocked_quarantined_legacy"
    assert not report["activation_eligible"]
    assert report["lock_hash"].startswith("0x")
    assert report["lock_hash"] != "0x" + "00" * 32
    assert {"python", "docker", "lean", "rust-risc0", "rust-tee"} <= set(report["groups"])
    assert "zk/state_proof_risc0/Cargo.lock" in report["paths"]
    assert "zk/state_proof_risc0/methods/perps_np_leaf/Cargo.toml" in report["paths"]
    assert "zk/global_economic_epoch_risc0/Cargo.lock" in report["paths"]
    assert "zk/zdex_hyperdeflation_burn_risc0/methods/guest/Cargo.toml" in report["paths"]
    assert "lean-mathlib/lean-toolchain" in report["paths"]
    assert "lean-mathlib/Proofs.lean" in report["paths"]
    assert "lean-mathlib/Proofs/ZenoLedgerZkTeeProofComposition.lean" in report["paths"]
    assert "lean-mathlib/proof_receipts/zeno_ledger_zk_tee_proof_composition_v1.md" in report["paths"]
    assert "Dockerfile" in report["paths"]
    policy = report["risc0_dependency_policy"]
    assert policy["ok"], policy["findings"]
    assert policy["status"] == "inventory_valid_quarantined"
    assert policy["governed_requirement"] == "=3.0.6"
    assert {row["workspace"] for row in policy["quarantines"]} == {"zk/state_proof_risc0"}
    assert all(row["authority"] == "NONE" for row in policy["quarantines"])
    assert all(row["activation_eligible"] is False for row in policy["quarantines"])
    committed_paths = set(report["paths"])
    assert all(row["manifest"] in committed_paths for row in policy["dependencies"])
    assert all(f"{row['workspace']}/Cargo.lock" in committed_paths for row in policy["dependencies"])
    committed_digests = {
        entry["path"]: entry["sha256"]
        for entry in report["manifest"]["files"]
        if entry["group"] == "rust-risc0"
    }
    assert policy["policy_input_sha256"] == committed_digests


def test_policy_verdict_digest_drift_blocks_inventory(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    policy = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(ROOT)
    path = sorted(policy["policy_input_sha256"])[0]
    policy["policy_input_sha256"][path] = "sha256:" + "0" * 64
    monkeypatch.setattr(
        check_proof_toolchain_lock,
        "audit_risc0_dependency_policy_v1",
        lambda _root: policy,
    )

    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)

    assert not report["inventory_ok"]
    assert f"RISC0 policy input digest/group mismatch: {path}" in report["errors"]


def test_dynamic_lock_discovery_commits_new_risc0_workspace(tmp_path: Path) -> None:
    workspace = _write_risc0_workspace(tmp_path)

    groups = dict(check_proof_toolchain_lock.toolchain_lock_paths_v0(tmp_path))

    expected = {
        (workspace / "Cargo.toml").relative_to(tmp_path).as_posix(),
        (workspace / "Cargo.lock").relative_to(tmp_path).as_posix(),
        (workspace / "host" / "Cargo.toml").relative_to(tmp_path).as_posix(),
    }
    assert expected <= set(groups["rust-risc0"])


def test_governed_exact_dependency_and_lock_are_activation_eligible(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path)

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert report["ok"], report["findings"]
    assert report["activation_eligible"]
    assert report["governed_dependency_count"] == 1
    assert report["quarantines"] == []


def test_caret_shorthand_is_rejected_even_when_lock_resolves_3_0_6(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path, requirement="3.0.6")

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert not report["ok"]
    assert "non_exact_governed_requirement" in _error_codes(report)


def test_affected_version_outside_named_quarantine_is_rejected(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path, requirement="1.2", resolved_versions=("1.2.6",))

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert not report["ok"]
    assert "non_exact_governed_requirement" in _error_codes(report)
    assert "wrong_governed_lock_version" in _error_codes(report)


def test_workspace_inherited_exact_requirement_is_resolved(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path, inherited=True)

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert report["ok"], report["findings"]
    assert report["activation_eligible"]
    assert report["dependencies"][0]["requirement"] == "=3.0.6"


def test_package_alias_for_risc0_zkvm_is_audited_and_committed(tmp_path: Path) -> None:
    workspace = _write_risc0_workspace(tmp_path)
    manifest = workspace / "host" / "Cargo.toml"
    source = manifest.read_text(encoding="utf-8")
    manifest.write_text(
        source.replace(
            "risc0-zkvm = {",
            'zkvm_alias = { package = "risc0-zkvm",',
        ),
        encoding="utf-8",
    )

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)
    groups = dict(check_proof_toolchain_lock.toolchain_lock_paths_v0(tmp_path))

    assert report["ok"], report["findings"]
    assert report["dependencies"][0]["dependency"] == "zkvm_alias"
    assert report["dependencies"][0]["package"] == "risc0-zkvm"
    assert manifest.relative_to(tmp_path).as_posix() in groups["rust-risc0"]


def test_host_dependency_without_disable_dev_mode_is_rejected(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path, host_disable_dev_mode=False)

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert not report["ok"]
    assert "host_disable_dev_mode_missing" in _error_codes(report)


def test_guest_dependency_with_default_features_enabled_is_rejected(tmp_path: Path) -> None:
    _write_risc0_workspace(
        tmp_path,
        dependency_path="methods/guest",
        guest_default_features_false=False,
    )

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert not report["ok"]
    assert "guest_default_features_enabled" in _error_codes(report)


def test_unknown_zkvm_dependency_role_is_rejected(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path, dependency_path="verifier")

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert not report["ok"]
    assert "unknown_zkvm_dependency_role" in _error_codes(report)


def test_lock_package_without_checksum_is_rejected(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path, include_checksum=False)

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert not report["ok"]
    assert "registry_checksum_missing" in _error_codes(report)


def test_mixed_core_package_versions_are_rejected(tmp_path: Path) -> None:
    _write_risc0_workspace(tmp_path, resolved_versions=("3.0.6", "3.0.5"))

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert not report["ok"]
    assert "mixed_core_package_versions" in _error_codes(report)
    assert "duplicate_core_lock_package" in _error_codes(report)


def test_exact_legacy_workspace_is_inventory_valid_and_activation_blocked(tmp_path: Path) -> None:
    _write_risc0_workspace(
        tmp_path,
        workspace_name="state_proof_risc0",
        requirement="1.2",
        resolved_versions=("1.2.6",),
        host_disable_dev_mode=False,
    )

    report = check_proof_toolchain_lock.audit_risc0_dependency_policy_v1(tmp_path)

    assert report["ok"], report["findings"]
    assert not report["activation_eligible"]
    assert report["quarantines"] == [
        {
            "workspace": "zk/state_proof_risc0",
            "authority": "NONE",
            "activation_eligible": False,
            "advisory": "GHSA-jqq4-c7wq-36h7",
            "nonclaim": (
                "Historical regression source only. This workspace has authority NONE and is "
                "ineligible for governed release, settlement, claim promotion, or production "
                "admission."
            ),
        }
    ]


def test_manifest_rejects_missing_risc0_lock_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"] = [
        entry
        for entry in manifest["files"]
        if entry["path"] != "zk/state_proof_risc0/Cargo.lock"
    ]

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert "missing lock paths: zk/state_proof_risc0/Cargo.lock" in validation["errors"]


def test_manifest_rejects_unexpected_toolchain_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    extra = dict(manifest["files"][0])
    extra["path"] = "requirements.txt"
    manifest["files"].append(extra)

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("requirements.txt" in error for error in validation["errors"])


def test_manifest_rejects_duplicate_toolchain_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"].append(dict(manifest["files"][0]))

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("is duplicated" in error for error in validation["errors"])


def test_manifest_rejects_wrong_group_for_toolchain_path() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"][0]["group"] = "docker"

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("group mismatch" in error for error in validation["errors"])


def test_manifest_rejects_malformed_sha() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"][0]["sha256"] = "not-a-sha"

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert "files[0].sha256 must be sha256:<64 hex>" in validation["errors"]


def test_manifest_rejects_sha_mismatch() -> None:
    report = check_proof_toolchain_lock.check_proof_toolchain_lock_v0(ROOT)
    manifest = copy.deepcopy(report["manifest"])
    manifest["files"][0]["sha256"] = "sha256:" + "1" * 64

    validation = check_proof_toolchain_lock.validate_proof_toolchain_lock_manifest_v0(
        manifest,
        root=ROOT,
    )

    assert not validation["ok"]
    assert any("sha256 mismatch" in error for error in validation["errors"])
