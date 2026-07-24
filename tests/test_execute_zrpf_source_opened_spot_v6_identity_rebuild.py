from __future__ import annotations

import copy
import hashlib
import os
import shlex
import subprocess
import sys
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path

import pytest

from tools import (
    execute_zrpf_source_opened_spot_v6_identity_rebuild as executor,
)
from tools import (
    plan_zrpf_source_opened_spot_v6_identity_rebuild as planner,
)
from tools import zrpf_v6_identity_docker_runner as docker_runner
from tools.zrpf_v6_identity_executor_types import IncompleteContainerCleanupError

SOURCE_COMMIT = subprocess.check_output(
    ["git", "-C", str(planner.REPO_ROOT), "rev-parse", "HEAD"],
    text=True,
).strip()


def _runner_security_posture() -> dict:
    return {
        "schema": planner.RUNNER_SECURITY_POSTURE_SCHEMA,
        "tool_identities": {
            "cargo": {
                "sha256": planner.TOOLCHAIN["outer_cargo_sha256"],
                "bytes": 1,
            },
            "rustc": {
                "sha256": planner.TOOLCHAIN["rustc_sha256"],
                "bytes": 1,
            },
            "r0vm": {
                "sha256": planner.TOOLCHAIN["r0vm_sha256"],
                "bytes": 1,
            },
            "cargo_risczero": {
                "sha256": planner.TOOLCHAIN["cargo_risczero_sha256"],
                "bytes": 1,
            },
        },
        "cargo_registry_identity": {
            "schema": planner.CARGO_REGISTRY_IDENTITY_SCHEMA,
            "root_sha256": "a" * 64,
            "file_count": 1,
            "total_bytes": 1,
            "components": ["cache", "index", "src"],
            "maximum_files": planner.MAX_CARGO_REGISTRY_FILES,
            "maximum_total_bytes": planner.MAX_CARGO_REGISTRY_BYTES,
            "maximum_file_bytes": planner.MAX_CARGO_REGISTRY_FILE_BYTES,
        },
        "resource_policy": dict(planner.RUNNER_RESOURCE_POLICY),
        "same_uid_resistance": False,
        "complete_build_input_closure_verified": False,
    }


class FakeRunner:
    def __init__(
        self,
        *,
        substitute_pass: str | None = None,
        symlink_pass: str | None = None,
        mutate_source_pass: str | None = None,
        extra_output_pass: str | None = None,
    ) -> None:
        self.requests: list[executor.BuildRequest] = []
        self.substitute_pass = substitute_pass
        self.symlink_pass = symlink_pass
        self.mutate_source_pass = mutate_source_pass
        self.extra_output_pass = extra_output_pass

    def security_posture(self) -> dict:
        return _runner_security_posture()

    def run(self, request: executor.BuildRequest) -> executor.BuildResult:
        self.requests.append(request)
        request.target_directory.mkdir(mode=0o700)
        request.output_directory.mkdir(mode=0o700)
        if request.kind is executor.BuildKind.HOST_VERIFIER:
            raw = b"host-verifier-v6"
            destination = request.output_directory / request.artifact_file
            destination.write_bytes(raw)
            return executor.BuildResult(
                artifact_bytes=len(raw),
                artifact_sha256=hashlib.sha256(raw).hexdigest(),
                image_id=None,
            )

        identity_seed = request.stage_id.encode("ascii")
        if request.pass_id == self.substitute_pass:
            identity_seed += b":substituted"
        raw = b"R0BF" + hashlib.sha256(identity_seed).digest() * 2
        destination = request.output_directory / request.artifact_file
        if request.pass_id == self.symlink_pass:
            backing = request.output_directory / "backing.bin"
            backing.write_bytes(raw)
            destination.symlink_to(backing.name)
        else:
            destination.write_bytes(raw)
        if request.companion_artifact_file is not None:
            (request.output_directory / request.companion_artifact_file).write_bytes(
                b"source-spot-cli"
            )
        if request.pass_id == self.extra_output_pass:
            (request.output_directory / "undeclared.bin").write_bytes(b"extra")
        if request.pass_id == self.mutate_source_pass:
            policy = request.source_snapshot / planner.STAGES[0].repins[0].path
            policy.write_bytes(policy.read_bytes() + b"\n")
        digest = hashlib.sha256(raw).hexdigest()
        image_id = hashlib.sha256(b"image-id:" + raw).hexdigest()
        return executor.BuildResult(
            artifact_bytes=len(raw),
            artifact_sha256=digest,
            image_id=image_id,
        )


def _plan(run_root: Path) -> dict:
    return planner.build_plan(SOURCE_COMMIT, run_root.as_posix())


def _execute(tmp_path: Path, runner: FakeRunner) -> tuple[dict, dict, Path]:
    run_root = tmp_path / "run"
    plan = _plan(run_root)
    observations = executor.execute_plan(plan, runner=runner)
    report = planner.check_observations(plan, observations)
    return observations, report, run_root


def test_fake_runner_executes_exact_primary_two_pass_final_and_host_order(
    tmp_path: Path,
) -> None:
    runner = FakeRunner()

    observations, report, run_root = _execute(tmp_path, runner)

    assert [request.pass_id for request in runner.requests] == [
        *(f"primary:{stage.stage_id}" for stage in planner.STAGES),
        "settlement-second-pass",
        *(f"final:{stage.stage_id}" for stage in planner.STAGES),
        "host-verifier",
    ]
    assert report["status"] == "candidate_repin_chain_observations_validated"
    assert observations["runner_security_posture"] == _runner_security_posture()
    assert report["runner_security_posture"] == _runner_security_posture()
    assert "no_same_uid_resistance" in report["non_claims"]
    assert all(value is False for value in report["authority"].values())
    assert planner.check_observations(plan=_plan(run_root), observations=observations)


def test_executor_writes_exact_v2_candidates_and_preserves_historical_v1(
    tmp_path: Path,
) -> None:
    runner = FakeRunner()
    observations, report, run_root = _execute(tmp_path, runner)
    snapshot = run_root / executor.SOURCE_SNAPSHOT_DIRECTORY

    for relative in planner.PROTECTED_HISTORICAL_ARTIFACTS:
        expected = subprocess.check_output(
            ["git", "-C", str(planner.REPO_ROOT), "show", f"{SOURCE_COMMIT}:{relative}"]
        )
        assert (snapshot / relative).read_bytes() == expected
    candidates = report["governance_candidates"]
    for key in ("current_source_anchor_v2", "v2_adapter_source_policy"):
        row = candidates[key]
        assert (snapshot / row["path"]).read_bytes() == planner.canonical_bytes(
            row["document"]
        )
    assert observations["stages"][0]["source_tree_root_sha256"] == _plan(run_root)[
        "source_guest_source_coverage"
    ]["inventory_root_sha256"]


def test_executor_records_exact_declared_repin_values(tmp_path: Path) -> None:
    observations, _report, _run_root = _execute(tmp_path, FakeRunner())

    for spec, observed in zip(planner.STAGES, observations["stages"], strict=True):
        assert [
            (row["path"], row["symbol"], row["value_kind"], row["visibility"])
            for row in observed["repins"]
        ] == [
            (row.path, row.symbol, row.value_kind, row.visibility)
            for row in spec.repins
        ]


def test_mutated_plan_rejects_before_run_root_creation(tmp_path: Path) -> None:
    run_root = tmp_path / "run"
    plan = _plan(run_root)
    plan["stages"][2]["command"][0] = "/tmp/attacker-cargo"

    with pytest.raises(planner.RebuildPlanError, match="deterministic plan"):
        executor.execute_plan(plan, runner=FakeRunner())

    assert not run_root.exists()


@pytest.mark.parametrize(
    ("mutation", "error"),
    [
        (
            lambda posture: posture.update({"same_uid_resistance": True}),
            "same-UID resistance non-claim mismatch",
        ),
        (
            lambda posture: posture.update({"production_authority": False}),
            "runner security posture fields mismatch",
        ),
        (
            lambda posture: posture["resource_policy"].update(
                {"nested_cargo_wrapper_sha256": "0" * 64}
            ),
            "runner resource policy mismatch",
        ),
    ],
)
def test_runner_posture_promotion_or_schema_drift_rejects_before_build(
    tmp_path: Path,
    mutation: Callable[[dict], None],
    error: str,
) -> None:
    class MutatedPostureRunner(FakeRunner):
        def security_posture(self) -> dict:
            posture = copy.deepcopy(_runner_security_posture())
            mutation(posture)
            return posture

    runner = MutatedPostureRunner()
    run_root = tmp_path / "run"

    with pytest.raises(planner.RebuildPlanError, match=error):
        executor.execute_plan(_plan(run_root), runner=runner)

    assert runner.requests == []
    assert not run_root.exists()


def test_undeclared_repin_path_rejects_before_execution(tmp_path: Path) -> None:
    run_root = tmp_path / "run"
    plan = _plan(run_root)
    plan["stages"][0]["repins_after_success"][0]["path"] = (
        "zk/zrpf_risc0/shared/src/source_policy_v1.rs"
    )

    with pytest.raises(planner.RebuildPlanError, match="deterministic plan"):
        executor.execute_plan(plan, runner=FakeRunner())

    assert not run_root.exists()


def test_runner_source_mutation_rejects_and_removes_partial_run(tmp_path: Path) -> None:
    run_root = tmp_path / "run"
    plan = _plan(run_root)

    with pytest.raises(executor.ExecutionError, match="source snapshot changed"):
        executor.execute_plan(
            plan,
            runner=FakeRunner(mutate_source_pass="primary:source_spot"),
        )

    assert not run_root.exists()


def test_incomplete_container_cleanup_retains_private_recovery_state(
    tmp_path: Path,
) -> None:
    class OrphaningRunner(FakeRunner):
        def run(self, request: executor.BuildRequest) -> executor.BuildResult:
            request.target_directory.mkdir(mode=0o700)
            request.output_directory.mkdir(mode=0o700)
            cid = request.target_directory / docker_runner.CONTAINER_ID_FILE
            cid.write_bytes(b"b" * 64)
            cid.chmod(0o600)
            raise IncompleteContainerCleanupError(
                "owned-container cleanup is incomplete; recovery state must be retained"
            )

    run_root = tmp_path / "run"

    with pytest.raises(
        IncompleteContainerCleanupError,
        match="recovery state must be retained",
    ):
        executor.execute_plan(_plan(run_root), runner=OrphaningRunner())

    retained = tuple(run_root.rglob(docker_runner.CONTAINER_ID_FILE))
    assert len(retained) == 1
    assert retained[0].read_bytes() == b"b" * 64


def test_repin_transition_rejects_persistent_mutation_of_another_source(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = executor.artifacts.repin_rust_constant
    poisoned = False

    def mutate_another_source(
        path: Path,
        symbol: str,
        value_kind: str,
        value: list[int],
    ) -> None:
        nonlocal poisoned
        original(path, symbol, value_kind, value)
        if not poisoned:
            poisoned = True
            sibling = path.parent / "lib.rs"
            sibling.write_bytes(sibling.read_bytes() + b"\n")

    monkeypatch.setattr(
        executor.artifacts,
        "repin_rust_constant",
        mutate_another_source,
    )
    run_root = tmp_path / "run"

    with pytest.raises(
        executor.ExecutionError,
        match="changed undeclared paths or bytes",
    ):
        executor.execute_plan(_plan(run_root), runner=FakeRunner())

    assert not run_root.exists()


def test_candidate_write_rejects_undeclared_compiler_visible_cargo_config(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = executor.artifacts.write_candidate_document

    def add_undeclared_cargo_config(
        snapshot_root: Path,
        relative: str,
        document: dict,
    ) -> None:
        original(snapshot_root, relative, document)
        cargo = snapshot_root / "zk/zrpf_risc0/.cargo"
        (cargo / "config.attacker.toml").write_text(
            "[build]\nrustc-wrapper = '/tmp/attacker'\n",
            encoding="utf-8",
        )

    monkeypatch.setattr(
        executor.artifacts,
        "write_candidate_document",
        add_undeclared_cargo_config,
    )
    run_root = tmp_path / "run"

    with pytest.raises(
        executor.ExecutionError,
        match="live inventory mismatch",
    ):
        executor.execute_plan(_plan(run_root), runner=FakeRunner())

    assert not run_root.exists()


def test_candidate_write_rejects_same_bytes_through_an_unsafe_hardlink(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = executor.artifacts.write_candidate_document
    backing = tmp_path / "attacker-backing"

    def substitute_hardlink(
        snapshot_root: Path,
        relative: str,
        document: dict,
    ) -> None:
        original(snapshot_root, relative, document)
        target = snapshot_root / relative
        backing.write_bytes(target.read_bytes())
        target.unlink()
        os.link(backing, target)

    monkeypatch.setattr(
        executor.artifacts,
        "write_candidate_document",
        substitute_hardlink,
    )
    run_root = tmp_path / "run"

    with pytest.raises(
        executor.ExecutionError,
        match="ownership or link count is unsafe",
    ):
        executor.execute_plan(_plan(run_root), runner=FakeRunner())

    assert not run_root.exists()


@pytest.mark.parametrize("unsafe_mode", [0o770, 0o707, 0o1700])
def test_run_root_rejects_group_world_writable_or_sticky_parent(
    tmp_path: Path,
    unsafe_mode: int,
) -> None:
    unsafe_parent = tmp_path / "unsafe-parent"
    unsafe_parent.mkdir(mode=0o700)
    unsafe_parent.chmod(unsafe_mode)
    run_root = unsafe_parent / "run"

    with pytest.raises(
        executor.ExecutionError,
        match="parent ownership or permissions are unsafe",
    ):
        executor.execute_plan(_plan(run_root), runner=FakeRunner())

    assert not run_root.exists()


def test_symlink_artifact_substitution_rejects(tmp_path: Path) -> None:
    run_root = tmp_path / "run"
    plan = _plan(run_root)

    with pytest.raises(executor.ExecutionError, match="bounded regular file"):
        executor.execute_plan(
            plan,
            runner=FakeRunner(symlink_pass="primary:v6_leaf"),
        )

    assert not run_root.exists()


def test_extra_output_artifact_rejects(tmp_path: Path) -> None:
    run_root = tmp_path / "run"
    plan = _plan(run_root)

    with pytest.raises(executor.ExecutionError, match="output inventory mismatch"):
        executor.execute_plan(
            plan,
            runner=FakeRunner(extra_output_pass="primary:v6_l1"),
        )

    assert not run_root.exists()


def test_runner_internal_hash_substitution_rejects(tmp_path: Path) -> None:
    class LyingRunner(FakeRunner):
        def run(self, request: executor.BuildRequest) -> executor.BuildResult:
            result = super().run(request)
            if request.pass_id == "primary:v2_adapter":
                return replace(result, artifact_sha256="0" * 64)
            return result

    run_root = tmp_path / "run"
    with pytest.raises(executor.ExecutionError, match="runner artifact SHA-256 mismatch"):
        executor.execute_plan(_plan(run_root), runner=LyingRunner())


def test_final_rebuild_substitution_rejects(tmp_path: Path) -> None:
    run_root = tmp_path / "run"
    with pytest.raises(
        planner.RebuildPlanError,
        match="final rebuild identity for v6_l2 mismatch",
    ):
        executor.execute_plan(
            _plan(run_root),
            runner=FakeRunner(substitute_pass="final:v6_l2"),
        )


def test_executor_output_is_canonical_and_checker_accepted(tmp_path: Path) -> None:
    observations, _report, run_root = _execute(tmp_path, FakeRunner())
    observation_path = run_root / executor.OBSERVATIONS_FILE
    report_path = run_root / executor.CANDIDATE_REPORT_FILE

    assert observation_path.read_bytes() == planner.canonical_bytes(observations)
    loaded = planner.load_canonical_json(observation_path, "observations")
    assert planner.check_observations(_plan(run_root), loaded)
    assert planner.load_canonical_json(report_path, "candidate report")["authority"] == {
        field: False for field in planner.AUTHORITY_FLAGS
    }


def test_repin_writer_rejects_duplicate_symbol_declarations(tmp_path: Path) -> None:
    source = tmp_path / "policy.rs"
    declaration = "pub const PIN: [u32; 8] = [0; 8];\n"
    source.write_text(declaration + declaration, encoding="utf-8")

    with pytest.raises(executor.ExecutionError, match="exactly once"):
        executor.repin_rust_constant(source, "PIN", "image_id_words_le", [1] * 8)


def test_repin_writer_rejects_wrong_width_and_noncanonical_path(tmp_path: Path) -> None:
    source = tmp_path / "policy.rs"
    source.write_text("pub const PIN: [u32; 8] = [0; 8];\n", encoding="utf-8")

    with pytest.raises(executor.ExecutionError, match="value shape"):
        executor.repin_rust_constant(source, "PIN", "image_id_words_le", [1] * 7)
    with pytest.raises(executor.ExecutionError, match="repin path"):
        executor.resolve_snapshot_path(tmp_path, "../policy.rs")


def test_docker_script_preserves_exact_command_and_guest_identity_checks(
    tmp_path: Path,
) -> None:
    request = _guest_request_for_contract_test(tmp_path)

    script = docker_runner._container_script(request)

    assert shlex.join(request.command) in script
    assert "RISC0_BUILD_LOCKED=1" in script
    assert "CARGO_NET_OFFLINE=true" in script
    assert "magic == 52304246" in script
    assert '/risc0/bin/r0vm --elf "$artifact" --id' in script
    assert "install -m 0444" in script
    assert "source_spot_cli" in script
    syntax = subprocess.run(
        ["/bin/bash", "-n"],
        input=script,
        text=True,
        capture_output=True,
        check=False,
    )
    assert syntax.returncode == 0, syntax.stderr


def test_docker_mount_contract_is_read_only_except_fresh_target_and_output(
    tmp_path: Path,
) -> None:
    request = _guest_request_for_contract_test(tmp_path)
    toolchain = tmp_path / "toolchain"
    extension = tmp_path / "extension"
    registry = tmp_path / "registry"

    arguments = docker_runner._mount_arguments(
        request,
        toolchain,
        extension,
        registry,
    )

    mounts = arguments[1::2]
    assert len(mounts) == 6
    assert all(mount.endswith(",readonly") for mount in mounts[:4])
    assert all(not mount.endswith(",readonly") for mount in mounts[4:])
    assert f"source={request.source_snapshot},target=/src/zenodex,readonly" in mounts[0]


def test_host_runner_contract_never_emits_a_guest_identity(tmp_path: Path) -> None:
    request = replace(
        _guest_request_for_contract_test(tmp_path),
        kind=executor.BuildKind.HOST_VERIFIER,
        companion_artifact_file=None,
        companion_extraction_source=None,
    )

    script = docker_runner._container_script(request)

    assert "install -m 0555" in script
    assert "image_id='-'" in script
    assert "r0vm --elf" not in script
    assert docker_runner._parse_runner_result(
        b"12 " + b"a" * 64 + b" -\n",
        executor.BuildKind.HOST_VERIFIER,
    ).image_id is None


def test_direct_cli_entrypoint_loads_outside_repository(tmp_path: Path) -> None:
    result = subprocess.run(
        [
            sys.executable,
            str(
                planner.REPO_ROOT
                / "tools/execute_zrpf_source_opened_spot_v6_identity_rebuild.py"
            ),
            "--help",
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr
    assert "--cargo-registry-dir" in result.stdout


def _guest_request_for_contract_test(tmp_path: Path) -> executor.BuildRequest:
    return executor.BuildRequest(
        kind=executor.BuildKind.GUEST,
        pass_id="primary:source_spot",
        stage_id="source_spot",
        source_commit=SOURCE_COMMIT,
        source_snapshot=tmp_path / "snapshot",
        target_directory=tmp_path / "target",
        output_directory=tmp_path / "output",
        container_target_directory="/build/01-source-spot/target",
        container_output_directory="/build/01-source-spot/output",
        artifact_file="source_spot.bin",
        command=(planner.CANONICAL_CARGO, "build", "--locked", "--offline"),
        extraction_source="/build/01-source-spot/target/source_spot.bin",
        companion_artifact_file="source_spot_cli",
        companion_extraction_source="/build/01-source-spot/target/source_spot_cli",
    )
