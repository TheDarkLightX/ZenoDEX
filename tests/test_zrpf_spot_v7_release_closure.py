from __future__ import annotations

import copy
import hashlib
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as v6_planner
from tools import zrpf_spot_v7_release_closure as release
from tools import zrpf_spot_v7_release_inventory as inventory
from tools import zrpf_v6_v7_post_pin_governance as governance


@dataclass(frozen=True)
class _Candidate:
    root: Path
    c0: str
    c1: str
    c2: str
    g: str
    child_raw: bytes


def _git(root: Path, *arguments: str) -> bytes:
    completed = subprocess.run(
        ["/usr/bin/git", "-C", str(root), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    assert completed.returncode == 0, completed.stderr.decode(errors="replace")
    return completed.stdout


def _write(root: Path, relative: str, raw: bytes) -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def _commit(root: Path, message: str) -> str:
    _git(root, "add", "--all")
    _git(
        root,
        "-c",
        "user.name=ZRPF Release Test",
        "-c",
        "user.email=zrpf-release@example.invalid",
        "commit",
        "--quiet",
        "-m",
        message,
    )
    return _git(root, "rev-parse", "HEAD").decode("ascii").strip()


def _candidate(
    tmp_path: Path,
    *,
    omit_dependency_lock: bool = False,
    override_mode: str = "valid",
    replace_mode: str = "valid",
    ambiguous_cargo_config: bool = False,
    nested_compiler_mode: str = "valid",
) -> _Candidate:
    root = tmp_path / "repo"
    root.mkdir(mode=0o700)
    _git(root, "init", "--quiet")

    override_specs = {
        "valid": 'override-crate = { path = "../override_workspace/override" }',
        "missing": 'override-crate = { path = "../missing/override" }',
        "malformed": "override-crate = { path = 7 }",
    }
    override = override_specs[override_mode]
    replace_specs = {
        "valid": '{ path = "../replace_workspace/replace" }',
        "missing": '{ path = "../missing/replacement" }',
        "malformed": "{ path = 7 }",
    }
    replacement = replace_specs[replace_mode]
    _write(
        root,
        release.V7_WORKSPACE_MANIFEST,
        (
            '[workspace]\nmembers = ["child_policy", "shared"]\nresolver = "2"\n'
            f"[patch.crates-io]\n{override}\n"
            '[patch."https://example.invalid/index"]\n'
            'override-crate-url = { path = "../override_workspace/override" }\n'
            f'[replace]\n"replace-crate:0.1.0" = {replacement}\n'
        ).encode("utf-8"),
    )
    _write(root, "zk/spot_settlement_v7_risc0/Cargo.lock", b"# v7 lock\n")
    _write(
        root,
        release.V7_CHILD_POLICY_PATH,
        (
            f"pub const {release.V7_CHILD_POLICY_SYMBOL}: [u32; 8] = [0, 0, 0, 0, 0, 0, 0, 0];\n"
        ).encode("ascii"),
    )
    _write(
        root,
        "zk/spot_settlement_v7_risc0/child_policy/Cargo.toml",
        b'[package]\nname = "child-policy"\nversion = "0.1.0"\nedition = "2021"\n',
    )
    _write(
        root,
        "zk/spot_settlement_v7_risc0/shared/Cargo.toml",
        (
            b'[package]\nname = "v7-shared"\nversion = "0.1.0"\n'
            b'edition = "2021"\n[dependencies]\n'
            b'dep-shared = { path = "../../dep_workspace/shared" }\n'
        ),
    )
    _write(
        root,
        "zk/spot_settlement_v7_risc0/shared/src/lib.rs",
        b"pub fn v7() {}\n",
    )
    _write(
        root,
        "zk/dep_workspace/Cargo.toml",
        b'[workspace]\nmembers = ["shared"]\nresolver = "2"\n',
    )
    if not omit_dependency_lock:
        _write(root, "zk/dep_workspace/Cargo.lock", b"# dependency lock\n")
    _write(root, "zk/dep_workspace/.cargo/config.toml", b"[build]\nincremental = false\n")
    _write(
        root,
        "zk/dep_workspace/shared/Cargo.toml",
        b'[package]\nname = "dep-shared"\nversion = "0.1.0"\nedition = "2021"\n',
    )
    _write(
        root,
        "zk/dep_workspace/shared/src/lib.rs",
        (
            b'#[path = "../../../../tests/fixtures/v7-release-stage.rs"]\n'
            b"mod v7_release_stage;\n"
            b'pub const FIXTURE: &str = include_str!("../../../../tests/fixtures/v7-release.txt");\n'
        ),
    )
    _write(root, "tests/fixtures/v7-release.txt", b"compiler-visible fixture\n")
    nested_sources = {
        "valid": b'pub const NESTED: &str = include_str!("v7-release-nested.txt");\n',
        "cycle": b'include!("v7-release-cycle.rs");\n',
        "unknown": b'pub const NESTED: &str = include_str!(concat!("nested", ".txt"));\n',
    }
    _write(
        root,
        "tests/fixtures/v7-release-stage.rs",
        nested_sources[nested_compiler_mode],
    )
    if nested_compiler_mode == "cycle":
        _write(
            root,
            "tests/fixtures/v7-release-cycle.rs",
            b'include!("v7-release-stage.rs");\n',
        )
    _write(root, "tests/fixtures/v7-release-nested.txt", b"nested compiler input\n")
    _write(root, ".cargo/config.toml", b"[net]\noffline = true\n")
    if ambiguous_cargo_config:
        _write(root, ".cargo/config", b"[net]\noffline = true\n")
    _write(
        root,
        "zk/override_workspace/Cargo.toml",
        b'[workspace]\nmembers = ["override"]\nresolver = "2"\n',
    )
    _write(root, "zk/override_workspace/Cargo.lock", b"# override lock\n")
    _write(
        root,
        "zk/override_workspace/override/Cargo.toml",
        b'[package]\nname = "override-crate"\nversion = "0.1.0"\nedition = "2021"\n',
    )
    _write(root, "zk/override_workspace/override/src/lib.rs", b"pub fn patched() {}\n")
    _write(
        root,
        "zk/replace_workspace/Cargo.toml",
        b'[workspace]\nmembers = ["replace"]\nresolver = "2"\n',
    )
    _write(root, "zk/replace_workspace/Cargo.lock", b"# replacement lock\n")
    _write(
        root,
        "zk/replace_workspace/replace/Cargo.toml",
        b'[package]\nname = "replace-crate"\nversion = "0.1.0"\nedition = "2021"\n',
    )
    _write(root, "zk/replace_workspace/replace/src/lib.rs", b"pub fn replaced() {}\n")
    c0 = _commit(root, "C0")

    _write(root, "zk/spot_settlement_v7_risc0/identity.txt", b"C1 identity\n")
    c1 = _commit(root, "C1")

    words = list(range(1, 9))
    child_raw = (
        f"pub const {release.V7_CHILD_POLICY_SYMBOL}: "
        f"[u32; 8] = [{', '.join(str(word) for word in words)}];\n"
    ).encode("ascii")
    _write(root, release.V7_CHILD_POLICY_PATH, child_raw)
    c2 = _commit(root, "C2")

    _write(root, "evidence/post-pin-governance.json", b"{}\n")
    g = _commit(root, "G")
    return _Candidate(root=root, c0=c0, c1=c1, c2=c2, g=g, child_raw=child_raw)


def _tree(candidate: _Candidate, commit: str) -> str:
    return _git(candidate.root, "rev-parse", f"{commit}^{{tree}}").decode().strip()


def _governance_result(candidate: _Candidate) -> dict:
    words = list(range(1, 9))
    image_id = b"".join(word.to_bytes(4, "little") for word in words).hex()
    return {
        "schema": governance.CHECK_SCHEMA,
        "status": "committed_post_pin_governance_binding_checked",
        "c0_commit": candidate.c0,
        "c1_commit": candidate.c1,
        "c2_commit": candidate.c2,
        "governance_commit": candidate.g,
        "plan_sha256": "1" * 64,
        "observations_sha256": "2" * 64,
        "candidate_report_sha256": "3" * 64,
        "materialization_manifest_sha256": "4" * 64,
        "v6_settlement_image_id": image_id,
        "v6_settlement_image_id_words": words,
        "v7_child_policy_tree": _tree(candidate, candidate.c2),
        "v7_child_policy_sha256": hashlib.sha256(candidate.child_raw).hexdigest(),
        "validated_facts": {
            "governance_checkout_is_clean_and_exact": True,
            "c1_is_literal_direct_child_of_c0": True,
            "c1_matches_exact_v6_materialization": True,
            "c2_is_literal_direct_child_of_c1": True,
            "c2_contains_only_exact_v7_child_pin": True,
            "governance_commit_is_literal_direct_child_of_c2": True,
            "governance_commit_adds_only_fixed_canonical_evidence": True,
            "manifest_recomposes_from_committed_evidence": True,
            "v6_settlement_image_id_is_nonzero_and_exact": True,
            "committed_v7_policy_matches_manifest_and_c2_tree": True,
        },
        "authority": {field: False for field in governance.AUTHORITY_FIELDS},
        "non_claims": list(governance.NON_CLAIMS),
    }


def _runtime_identity() -> dict:
    return {
        "schema": release.RUNTIME_IDENTITY_SCHEMA,
        "container_engine": {
            "name": "docker",
            "client_executable_sha256": "5" * 64,
            "client_executable_bytes": 12_345,
            "client_version": "Docker version 28.3.2",
            "server_version": "28.3.2",
            "server_api_version": "1.51",
            "oci_runtime_name": "runc",
            "oci_runtime_version": "1.3.0",
            "server_architecture": "x86_64",
            "server_os": "linux",
            "kernel_release": "6.14.0-test",
            "cgroup_mode": "v2",
        },
        "build_image": {
            "image_id": v6_planner.BUILD_IMAGE,
            "parent_digest": v6_planner.BUILD_IMAGE_PARENT,
        },
        "cargo_registry": {
            "schema": v6_planner.CARGO_REGISTRY_IDENTITY_SCHEMA,
            "root_sha256": "6" * 64,
            "file_count": 100,
            "total_bytes": 1_000_000,
            "components": ["cache", "index", "src"],
            "maximum_files": v6_planner.MAX_CARGO_REGISTRY_FILES,
            "maximum_total_bytes": v6_planner.MAX_CARGO_REGISTRY_BYTES,
            "maximum_file_bytes": v6_planner.MAX_CARGO_REGISTRY_FILE_BYTES,
        },
        "observation": {
            "network_disabled_before_build": True,
            "clean_target_verified": True,
            "cargo_locked": True,
            "cargo_offline": True,
            "runtime_observation_is_live_attested": False,
        },
    }


def _install_governance(monkeypatch: pytest.MonkeyPatch, candidate: _Candidate) -> None:
    result = _governance_result(candidate)
    monkeypatch.setattr(
        release.governance,
        "check_post_pin_governance",
        lambda _root: copy.deepcopy(result),
    )


def test_plan_binds_ancestry_recursive_workspaces_lockfiles_and_external_includes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    _install_governance(monkeypatch, candidate)

    plan = release.build_release_closure_plan(candidate.root, _runtime_identity())

    assert plan["ancestry"]["ordered_commits"] == [
        candidate.c0,
        candidate.c1,
        candidate.c2,
        candidate.g,
    ]
    assert plan["v7_child_pin"]["nonzero"] is True
    closure = plan["source_closure"]
    assert closure["workspace_roots"] == [
        "zk/dep_workspace",
        "zk/override_workspace",
        "zk/replace_workspace",
        "zk/spot_settlement_v7_risc0",
    ]
    assert [row["path"] for row in closure["lockfiles"]] == [
        "zk/dep_workspace/Cargo.lock",
        "zk/override_workspace/Cargo.lock",
        "zk/replace_workspace/Cargo.lock",
        "zk/spot_settlement_v7_risc0/Cargo.lock",
    ]
    assert any(
        edge["dependency_kind"] == "patch:crates-io"
        and edge["to_manifest"] == "zk/override_workspace/override/Cargo.toml"
        for edge in closure["local_path_dependency_edges"]
    )
    assert any(
        edge["dependency_kind"] == "patch:https://example.invalid/index"
        and edge["to_manifest"] == "zk/override_workspace/override/Cargo.toml"
        for edge in closure["local_path_dependency_edges"]
    )
    assert any(
        edge["dependency_kind"] == "replace"
        and edge["to_manifest"] == "zk/replace_workspace/replace/Cargo.toml"
        for edge in closure["local_path_dependency_edges"]
    )
    assert [row["path"] for row in closure["ancestor_cargo_configs"]] == [
        ".cargo/config.toml",
        "zk/dep_workspace/.cargo/config.toml",
    ]
    assert ".cargo/config.toml" in closure["supplemental_compiler_inputs"]
    assert "tests/fixtures/v7-release.txt" in closure["supplemental_compiler_inputs"]
    assert "tests/fixtures/v7-release-stage.rs" in closure["supplemental_compiler_inputs"]
    assert "tests/fixtures/v7-release-nested.txt" in closure["supplemental_compiler_inputs"]
    assert any(
        edge["source_path"] == "tests/fixtures/v7-release-stage.rs"
        and edge["target_path"] == "tests/fixtures/v7-release-nested.txt"
        for edge in closure["literal_compiler_input_edges"]
    )
    assert closure["all_recursive_local_path_dependencies_inventoried"] is True
    assert closure["literal_compiler_inputs_reached_fixed_point"] is True
    assert closure["literal_compiler_source_graph_acyclic"] is True
    assert plan["build_closure"]["toolchain"] == v6_planner.TOOLCHAIN
    assert plan["build_closure"]["build_container"]["image_id"] == (v6_planner.BUILD_IMAGE)
    assert plan["authority"] == {field: False for field in release.AUTHORITY_FIELDS}
    assert all(value is False for value in plan["authority"].values())


def test_checker_recomposes_plan_and_emits_authority_neutral_evidence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    _install_governance(monkeypatch, candidate)
    runtime = _runtime_identity()
    plan = release.build_release_closure_plan(candidate.root, runtime)

    evidence = release.check_release_closure_plan(
        candidate.root,
        plan,
        runtime,
        expected_plan_sha256=release.canonical_sha256(plan),
    )

    assert evidence["status"] == "authority_neutral_v7_release_closure_checked"
    assert evidence["plan_sha256"] == release.canonical_sha256(plan)
    assert evidence["source_closure_root_sha256"] == plan["source_closure"]["inventory_root_sha256"]
    facts = evidence["validated_facts"]
    assert facts["local_cargo_patch_and_replace_overrides_checked"] is True
    assert facts["ancestor_cargo_configs_bound"] is True
    assert facts["literal_compiler_input_fixed_point_checked"] is True
    assert facts["literal_compiler_source_graph_acyclic"] is True
    assert all(value is False for value in evidence["authority"].values())


def test_rejects_nonliteral_ancestry_even_when_governance_result_claims_success(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    result = _governance_result(candidate)
    result["c1_commit"] = candidate.c0
    monkeypatch.setattr(
        release.governance,
        "check_post_pin_governance",
        lambda _root: copy.deepcopy(result),
    )

    with pytest.raises(release.ReleaseClosureError, match="literal parent"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


def test_rejects_zero_child_pin_even_when_governance_result_claims_nonzero(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    _install_governance(monkeypatch, candidate)
    _write(
        candidate.root,
        release.V7_CHILD_POLICY_PATH,
        (
            f"pub const {release.V7_CHILD_POLICY_SYMBOL}: [u32; 8] = [0, 0, 0, 0, 0, 0, 0, 0];\n"
        ).encode("ascii"),
    )
    _git(candidate.root, "add", release.V7_CHILD_POLICY_PATH)
    _git(
        candidate.root,
        "-c",
        "user.name=ZRPF Release Test",
        "-c",
        "user.email=zrpf-release@example.invalid",
        "commit",
        "--amend",
        "--no-edit",
        "--quiet",
    )
    amended_g = _git(candidate.root, "rev-parse", "HEAD").decode().strip()
    result = _governance_result(candidate)
    result["governance_commit"] = amended_g
    monkeypatch.setattr(
        release.governance,
        "check_post_pin_governance",
        lambda _root: copy.deepcopy(result),
    )

    with pytest.raises(release.ReleaseClosureError):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


def test_rejects_missing_reachable_workspace_lockfile(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path, omit_dependency_lock=True)
    _install_governance(monkeypatch, candidate)

    with pytest.raises(release.ReleaseClosureError, match="lockfile"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


@pytest.mark.parametrize("override_mode", ["missing", "malformed"])
def test_rejects_malformed_or_untracked_local_override(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    override_mode: str,
) -> None:
    candidate = _candidate(tmp_path, override_mode=override_mode)
    _install_governance(monkeypatch, candidate)

    with pytest.raises(release.ReleaseClosureError, match="override"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


@pytest.mark.parametrize("replace_mode", ["missing", "malformed"])
def test_rejects_malformed_or_untracked_local_replacement(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    replace_mode: str,
) -> None:
    candidate = _candidate(tmp_path, replace_mode=replace_mode)
    _install_governance(monkeypatch, candidate)

    with pytest.raises(release.ReleaseClosureError, match="override"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


def test_rejects_ambiguous_ancestor_cargo_config_pair(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path, ambiguous_cargo_config=True)
    _install_governance(monkeypatch, candidate)

    with pytest.raises(release.ReleaseClosureError, match="both present"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


def test_rejects_nested_compiler_source_cycle(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path, nested_compiler_mode="cycle")
    _install_governance(monkeypatch, candidate)

    with pytest.raises(release.ReleaseClosureError, match="contains a cycle"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


def test_rejects_unknown_include_form_in_nested_compiler_source(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path, nested_compiler_mode="unknown")
    _install_governance(monkeypatch, candidate)

    with pytest.raises(release.ReleaseClosureError, match="outside the governed scanner"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


def test_rejects_supplemental_compiler_input_overflow(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    _install_governance(monkeypatch, candidate)
    monkeypatch.setattr(inventory, "MAX_LITERAL_COMPILER_INPUTS", 1)

    with pytest.raises(release.ReleaseClosureError, match="set exceeds its bound"):
        release.build_release_closure_plan(candidate.root, _runtime_identity())


def test_checker_rejects_plan_or_runtime_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    _install_governance(monkeypatch, candidate)
    runtime = _runtime_identity()
    plan = release.build_release_closure_plan(candidate.root, runtime)

    mutated_plan = copy.deepcopy(plan)
    mutated_plan["source_closure"]["lockfiles"][0]["sha256"] = "0" * 64
    with pytest.raises(release.ReleaseClosureError, match="deterministic plan"):
        release.check_release_closure_plan(
            candidate.root,
            mutated_plan,
            runtime,
            expected_plan_sha256=release.canonical_sha256(mutated_plan),
        )

    mutated_runtime = copy.deepcopy(runtime)
    mutated_runtime["container_engine"]["server_version"] = "changed"
    with pytest.raises(release.ReleaseClosureError, match="runtime identity"):
        release.check_release_closure_plan(
            candidate.root,
            plan,
            mutated_runtime,
            expected_plan_sha256=release.canonical_sha256(plan),
        )


@pytest.mark.parametrize(
    "mutation",
    [
        lambda value: value.update({"unknown": True}),
        lambda value: value["container_engine"].update({"client_executable_sha256": "0" * 64}),
        lambda value: value["observation"].update({"runtime_observation_is_live_attested": True}),
    ],
)
def test_runtime_identity_is_exact_and_authority_neutral(mutation) -> None:
    value = _runtime_identity()
    mutation(value)
    with pytest.raises(release.ReleaseClosureError):
        release.validate_runtime_identity(value)


def test_unrecognized_compiler_include_form_rejects() -> None:
    with pytest.raises(release.ReleaseClosureError, match="outside the governed scanner"):
        inventory._uncovered_literal_inputs(
            "zk/example/src/lib.rs",
            b'const X: &str = include_str!(env!("UNDECLARED_INPUT"));\n',
            set(),
        )


def test_cli_help_is_available_without_pythonpath() -> None:
    for script in (
        "tools/plan_zrpf_spot_v7_release_closure.py",
        "tools/check_zrpf_spot_v7_release_closure.py",
    ):
        completed = subprocess.run(
            ["/usr/bin/python3", script, "--help"],
            cwd=release.REPO_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env={
                "HOME": "/nonexistent",
                "LC_ALL": "C",
                "PATH": "/usr/bin:/bin",
                "PYTHONDONTWRITEBYTECODE": "1",
                "TZ": "UTC",
            },
            check=False,
            timeout=30,
        )
        assert completed.returncode == 0
        assert b"authority-neutral" in completed.stdout
        assert not completed.stderr
