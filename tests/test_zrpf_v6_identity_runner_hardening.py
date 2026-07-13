from __future__ import annotations

import base64
import hashlib
import os
import stat
import subprocess
from pathlib import Path

import pytest

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_identity_docker_runner as runner_module
from tools import zrpf_v6_identity_runner_integrity as integrity
from tools import zrpf_v6_identity_runner_resources as resources
from tools.zrpf_v6_identity_executor_types import (
    BuildKind,
    BuildRequest,
    ExecutionError,
)


def test_registry_identity_is_deterministic_bounded_and_mutation_sensitive(
    tmp_path: Path,
) -> None:
    registry = _registry(tmp_path)

    first = integrity.capture_cargo_registry(registry)
    second = integrity.capture_cargo_registry(registry)

    assert first == second
    assert first.evidence() == {
        "schema": integrity.CARGO_REGISTRY_IDENTITY_SCHEMA,
        "root_sha256": first.root_sha256,
        "file_count": 4,
        "total_bytes": 16,
        "components": ["cache", "index", "src"],
        "maximum_files": integrity.MAX_CARGO_REGISTRY_FILES,
        "maximum_total_bytes": integrity.MAX_CARGO_REGISTRY_BYTES,
        "maximum_file_bytes": integrity.MAX_CARGO_REGISTRY_FILE_BYTES,
    }

    (registry / "src/crate/lib.rs").write_bytes(b"pub fn changed() {}\n")

    assert integrity.capture_cargo_registry(registry) != first


def test_tool_identity_detects_same_byte_path_replacement(tmp_path: Path) -> None:
    tool = tmp_path / "cargo"
    raw = b"#!/bin/sh\nexit 0\n"
    tool.write_bytes(raw)
    tool.chmod(0o555)
    digest = hashlib.sha256(raw).hexdigest()
    before = integrity.capture_pinned_tool(tool, "cargo", digest)
    replacement = tmp_path / "replacement"
    replacement.write_bytes(raw)
    replacement.chmod(0o555)

    os.replace(replacement, tool)

    after = integrity.capture_pinned_tool(tool, "cargo", digest)
    assert after.sha256 == before.sha256
    assert after != before


def test_registry_identity_rejects_nested_file_inserted_during_capture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    registry = _registry(tmp_path)
    original = integrity._read_stable_regular
    inserted = False

    def insert_during_read(*args: object, **kwargs: object) -> object:
        nonlocal inserted
        result = original(*args, **kwargs)
        if not inserted:
            inserted = True
            (registry / "src/crate/injected.rs").write_bytes(b"injected")
        return result

    monkeypatch.setattr(integrity, "_read_stable_regular", insert_during_read)

    with pytest.raises(ExecutionError, match="inventory changed during identity capture"):
        integrity.capture_cargo_registry(registry)


def test_runner_posture_keeps_same_uid_and_complete_closure_false(
    tmp_path: Path,
) -> None:
    registry_identity = integrity.capture_cargo_registry(_registry(tmp_path))
    tool = tmp_path / "tool"
    tool.write_bytes(b"tool")
    tool.chmod(0o555)
    tool_identity = integrity.capture_pinned_tool(
        tool,
        "tool",
        hashlib.sha256(b"tool").hexdigest(),
    )
    runner = object.__new__(runner_module.DockerBuildRunner)
    runner._tool_identities = {
        name: tool_identity for name in ("cargo", "rustc", "r0vm", "cargo_risczero")
    }
    runner._registry_identity = registry_identity

    posture = runner.security_posture()

    assert posture["same_uid_resistance"] is False
    assert posture["complete_build_input_closure_verified"] is False
    policy = posture["resource_policy"]
    assert policy["aggregate_container_cpu_quota"] == 2
    assert policy["outer_cargo_jobs"] == 2
    assert policy["nested_cargo_jobs"] == 2
    assert policy["target_mount_execution"] == "exec_required"
    assert policy["output_and_auxiliary_mount_execution"] == "noexec_required"
    assert policy["container_cleanup_identity"] == "private_cidfile_exact_id_v1"
    assert (
        policy["nested_cargo_wrapper_sha256"]
        == hashlib.sha256(runner_module.NESTED_CARGO_WRAPPER_BYTES).hexdigest()
    )
    assert policy["output_transport"] == "bounded_base64_stdout_v1"
    assert runner_module.NESTED_CARGO_WRAPPER_BYTES == (planner.NESTED_CARGO_WRAPPER_BYTES)
    assert runner_module.NESTED_CARGO_WRAPPER_SHA256 == (planner.NESTED_CARGO_WRAPPER_SHA256)


def test_runner_reauthentication_rejects_tool_and_registry_mutation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    registry = _registry(tmp_path)
    baseline_registry = integrity.capture_cargo_registry(registry)
    runner = object.__new__(runner_module.DockerBuildRunner)
    before = integrity.StableFileIdentity(1, 1, 0o100555, 1, 1, 1, "a" * 64)
    after = integrity.StableFileIdentity(1, 2, 0o100555, 1, 1, 1, "a" * 64)
    runner._registry = registry
    runner._registry_identity = baseline_registry
    runner._tool_identities = {"cargo": before}
    monkeypatch.setattr(runner, "_capture_tool_identities", lambda: {"cargo": after})

    with pytest.raises(ExecutionError, match="pinned tool identity changed"):
        runner._require_external_inputs_unchanged("before test")

    monkeypatch.setattr(runner, "_capture_tool_identities", lambda: {"cargo": before})
    (registry / "cache/a.crate").write_bytes(b"mutated crate")
    with pytest.raises(ExecutionError, match="Cargo registry identity changed"):
        runner._require_external_inputs_unchanged("after test")


def test_command_uses_cgroup_bounded_tmpfs_and_read_only_wrapper(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = _request(tmp_path)
    toolchain = tmp_path / "toolchain"
    extension = tmp_path / "extension"
    registry = _registry(tmp_path)
    wrapper = tmp_path / "nested-cargo-wrapper"
    for directory in (request.source_snapshot, toolchain, extension):
        directory.mkdir(parents=True, exist_ok=True)
    wrapper.write_bytes(runner_module.NESTED_CARGO_WRAPPER_BYTES)
    wrapper.chmod(0o555)
    runner = object.__new__(runner_module.DockerBuildRunner)
    runner._docker = Path("/usr/bin/docker")
    runner._repo_root = planner.REPO_ROOT
    runner._toolchain = toolchain
    runner._extension = extension
    runner._registry = registry
    monkeypatch.setattr(runner_module, "_source_commit_epoch", lambda *_args: "1")

    container_id_file = request.target_directory / runner_module.CONTAINER_ID_FILE
    command = runner._docker_command(
        request,
        "zrpf-v6-test",
        wrapper,
        container_id_file,
    )
    joined = "\n".join(command)

    assert "--cpus\n2" in joined
    assert f"--memory\n{planner.BUILD_MEMORY_BYTES}" in joined
    assert f"size={runner_module.TARGET_TMPFS_QUOTA_BYTES}" in joined
    assert f"size={runner_module.OUTPUT_TMPFS_QUOTA_BYTES}" in joined
    assert f"source={wrapper},target=/pinned-bin/cargo,readonly" in joined
    assert f"--cidfile\n{container_id_file}" in joined
    assert f"source={request.target_directory}" not in joined
    assert f"source={request.output_directory}" not in joined
    assert "--rm" not in command
    for quota in (
        resources.TARGET_TMPFS_QUOTA_BYTES,
        resources.OUTPUT_TMPFS_QUOTA_BYTES,
        resources.TMP_TMPFS_QUOTA_BYTES,
        resources.CARGO_TMPFS_QUOTA_BYTES,
        resources.HOME_TMPFS_QUOTA_BYTES,
        resources.RISC0_TMPFS_QUOTA_BYTES,
    ):
        assert f"size={quota}" in joined
    writable_tmpfs = sum(
        (
            resources.TARGET_TMPFS_QUOTA_BYTES,
            resources.OUTPUT_TMPFS_QUOTA_BYTES,
            resources.TMP_TMPFS_QUOTA_BYTES,
            resources.CARGO_TMPFS_QUOTA_BYTES,
            resources.HOME_TMPFS_QUOTA_BYTES,
            resources.RISC0_TMPFS_QUOTA_BYTES,
        )
    )
    assert writable_tmpfs + resources.MINIMUM_PROCESS_MEMORY_HEADROOM_BYTES <= (
        planner.BUILD_MEMORY_BYTES
    )
    script = command[-1]
    assert "export CARGO_BUILD_JOBS=2 RAYON_NUM_THREADS=2" in script
    assert "export PATH=/pinned-bin:" in script
    assert runner_module.NESTED_CARGO_WRAPPER_SHA256 in script
    target_mount = next(
        value for value in command if value.startswith(f"{request.container_target_directory}:")
    )
    assert ",exec," in target_mount
    for value in command:
        if value.startswith(("/tmp:", "/cargo:", "/sandbox-home:", "/risc0:")):
            assert ",noexec," in value


def test_memory_and_tmpfs_budget_rejects_missing_process_headroom(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        resources,
        "TARGET_TMPFS_QUOTA_BYTES",
        planner.BUILD_MEMORY_BYTES,
    )

    with pytest.raises(ExecutionError, match="policy is inconsistent"):
        runner_module._validate_resource_policy()


def test_build_request_rejects_outer_job_or_target_override(tmp_path: Path) -> None:
    request = _request(tmp_path)
    wrong_jobs = _replace_command_value(request, "--jobs", "8")
    wrong_target = _replace_command_value(request, "--target-dir", "/tmp/escape")

    with pytest.raises(ExecutionError, match="exact outer Cargo job count"):
        runner_module._validate_build_request_resources(wrong_jobs)
    with pytest.raises(ExecutionError, match="target directory is not exact"):
        runner_module._validate_build_request_resources(wrong_target)


def test_base64_transport_rehashes_materializes_and_rejects_trailing_bytes(
    tmp_path: Path,
) -> None:
    request = _request(tmp_path)
    request.output_directory.mkdir()
    artifact = b"R0BF-program"
    companion = b"host-cli"
    raw = _runner_output(request, artifact, companion)

    payload = runner_module._parse_runner_payload(raw, request)
    runner_module._materialize_runner_payload(request, payload)

    assert (request.output_directory / request.artifact_file).read_bytes() == artifact
    assert (request.output_directory / request.companion_artifact_file).read_bytes() == companion
    assert stat.S_IMODE((request.output_directory / request.artifact_file).stat().st_mode) == 0o444
    with pytest.raises(ExecutionError, match="trailing framing"):
        runner_module._parse_runner_payload(raw + raw, request)
    with pytest.raises(ExecutionError, match="artifact binding"):
        runner_module._parse_runner_payload(
            raw.replace(base64.b64encode(artifact), base64.b64encode(b"R0BF-tamper")),
            request,
        )


def test_quota_exhaustion_rejects_and_runs_cleanup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = _request(tmp_path)
    request.source_snapshot.mkdir()
    runner = object.__new__(runner_module.DockerBuildRunner)
    monkeypatch.setattr(runner, "_require_external_inputs_unchanged", lambda _label: None)
    monkeypatch.setattr(runner, "_require_container_absent", lambda _name: None)
    monkeypatch.setattr(
        runner,
        "_docker_command",
        lambda _request, _name, _wrapper, _cidfile: ["docker", "run"],
    )
    cleaned: list[tuple[str, Path]] = []
    monkeypatch.setattr(
        runner,
        "_cleanup_owned_container",
        lambda name, cidfile: cleaned.append((name, cidfile)),
    )
    monkeypatch.setattr(
        runner_module.process_runner,
        "run_bounded",
        lambda _request: subprocess.CompletedProcess(
            ["docker", "run"],
            1,
            b"",
            b"No space left on device\n",
        ),
    )

    with pytest.raises(ExecutionError, match="container build rejected with exit 1"):
        runner.run(request)

    assert len(cleaned) == 1
    assert cleaned[0][0].startswith("zrpf-v6-")
    assert cleaned[0][1].name == runner_module.CONTAINER_ID_FILE


def test_cleanup_accepts_absent_and_removes_present_container(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runner = _cleanup_runner(tmp_path)
    name = "zrpf-v6-cleanup"
    absent = _absent(name)
    cidfile = tmp_path / "container.cid"
    calls: list[tuple[str, ...]] = []

    def already_absent(request: object) -> subprocess.CompletedProcess[bytes]:
        command = request.command  # type: ignore[attr-defined]
        calls.append(command)
        return absent

    monkeypatch.setattr(runner_module.process_runner, "run_bounded", already_absent)
    runner._cleanup_owned_container(name, cidfile)
    assert len(calls) == 1

    container_id = "a" * 64
    cidfile.write_text(container_id, encoding="ascii")
    cidfile.chmod(0o600)
    present = subprocess.CompletedProcess([], 0, container_id.encode() + b"\n", b"")
    removed = subprocess.CompletedProcess([], 0, container_id.encode() + b"\n", b"")
    sequence = iter((present, removed, _absent(container_id), absent))
    monkeypatch.setattr(
        runner_module.process_runner,
        "run_bounded",
        lambda _request: next(sequence),
    )
    runner._cleanup_owned_container(name, cidfile)


def test_cleanup_surfaces_rm_failure_or_orphan_with_container_name(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runner = _cleanup_runner(tmp_path)
    name = "zrpf-v6-orphan"
    container_id = "b" * 64
    cidfile = tmp_path / "container.cid"
    cidfile.write_text(container_id, encoding="ascii")
    cidfile.chmod(0o600)
    present = subprocess.CompletedProcess([], 0, container_id.encode() + b"\n", b"")
    failed_rm = subprocess.CompletedProcess([], 1, b"", b"daemon rejected removal\n")
    sequence = iter((present, failed_rm, present))
    monkeypatch.setattr(
        runner_module.process_runner,
        "run_bounded",
        lambda _request: next(sequence),
    )

    with pytest.raises(ExecutionError, match=f"container removal failed: {container_id}"):
        runner._cleanup_owned_container(name, cidfile)


def test_cleanup_surfaces_inspection_failure_with_container_name(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runner = _cleanup_runner(tmp_path)
    name = "zrpf-v6-inspect-failure"
    monkeypatch.setattr(
        runner_module.process_runner,
        "run_bounded",
        lambda _request: subprocess.CompletedProcess([], 2, b"", b"daemon unavailable\n"),
    )

    with pytest.raises(ExecutionError, match=f"cleanup inspection failed: {name}"):
        runner._cleanup_owned_container(name, tmp_path / "absent.cid")


def test_preexisting_container_name_rejects_without_removal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runner = _cleanup_runner(tmp_path)
    name = "zrpf-v6-preexisting"
    present = subprocess.CompletedProcess([], 0, b"c" * 64 + b"\n", b"")
    calls: list[tuple[str, ...]] = []

    def inspect_only(request: object) -> subprocess.CompletedProcess[bytes]:
        calls.append(request.command)  # type: ignore[attr-defined]
        return present

    monkeypatch.setattr(runner_module.process_runner, "run_bounded", inspect_only)

    with pytest.raises(ExecutionError, match=f"name must begin absent: {name}"):
        runner._require_container_absent(name)

    assert len(calls) == 1
    assert calls[0][1:3] == ("container", "inspect")


def test_missing_cidfile_never_deletes_container_found_by_name(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runner = _cleanup_runner(tmp_path)
    name = "zrpf-v6-unowned"
    present = subprocess.CompletedProcess([], 0, b"d" * 64 + b"\n", b"")
    commands: list[tuple[str, ...]] = []

    def inspect_only(request: object) -> subprocess.CompletedProcess[bytes]:
        commands.append(request.command)  # type: ignore[attr-defined]
        return present

    monkeypatch.setattr(runner_module.process_runner, "run_bounded", inspect_only)

    with pytest.raises(ExecutionError, match=f"ownership unavailable: {name}"):
        runner._cleanup_owned_container(name, tmp_path / "absent.cid")

    assert len(commands) == 1
    assert "rm" not in commands[0]


def test_container_id_file_rejects_malformed_or_linked_identity(tmp_path: Path) -> None:
    malformed = tmp_path / "malformed.cid"
    malformed.write_bytes(b"e" * 64 + b"\n")
    malformed.chmod(0o600)

    with pytest.raises(ExecutionError, match="container ID file identity rejected"):
        runner_module._read_container_id(malformed)

    target = tmp_path / "target.cid"
    target.write_bytes(b"f" * 64)
    target.chmod(0o600)
    linked = tmp_path / "linked.cid"
    linked.symlink_to(target)

    with pytest.raises(ExecutionError, match="container ID file is unavailable"):
        runner_module._read_container_id(linked)


@pytest.mark.skipif(
    os.environ.get("ZENODEX_RUN_NATIVE_ZRPF_IDENTITY_RUNNER") != "1",
    reason="live pinned-image target-exec probe is opt-in",
)
def test_live_pinned_image_target_exec_and_nested_job_wrapper(tmp_path: Path) -> None:
    project = tmp_path / "project"
    source = project / "src"
    source.mkdir(parents=True)
    (project / "Cargo.toml").write_text(
        '[package]\nname="nested-wrapper-probe"\nversion="0.0.0"\n'
        'edition="2021"\nbuild="build.rs"\n\n[dependencies]\n',
        encoding="ascii",
    )
    (project / "Cargo.lock").write_text(
        "# This file is automatically @generated by Cargo.\n"
        "# It is not intended for manual editing.\n"
        "version = 4\n\n"
        '[[package]]\nname = "nested-wrapper-probe"\nversion = "0.0.0"\n',
        encoding="ascii",
    )
    (project / "build.rs").write_text(
        'fn main(){assert_eq!(std::env::var("NUM_JOBS").unwrap(),"2");'
        'assert_eq!(std::env::var("CARGO_BUILD_JOBS").unwrap(),"2");}\n',
        encoding="ascii",
    )
    (source / "main.rs").write_text("fn main(){}\n", encoding="ascii")
    wrapper = tmp_path / "nested-cargo-wrapper"
    wrapper.write_bytes(runner_module.NESTED_CARGO_WRAPPER_BYTES)
    wrapper.chmod(0o555)

    uid = os.getuid()
    gid = os.getgid()
    toolchain = (Path.home() / ".risc0/toolchains" / resources.RISC0_TOOLCHAIN_DIRECTORY).resolve(
        strict=True
    )
    target_mount = resources.tmpfs(
        "/build/target",
        256 * 1024 * 1024,
        "0700",
        uid,
        gid,
        noexec=False,
    )
    command = (
        "/usr/bin/docker",
        "run",
        "--rm",
        "--network",
        "none",
        "--read-only",
        "--cap-drop",
        "ALL",
        "--security-opt",
        "no-new-privileges",
        "--pids-limit",
        "512",
        "--cpus",
        str(planner.BUILD_CPUS),
        "--memory",
        str(planner.BUILD_MEMORY_BYTES),
        "--memory-swap",
        str(planner.BUILD_MEMORY_BYTES),
        "--user",
        f"{uid}:{gid}",
        "--mount",
        f"type=bind,source={project},target=/probe,readonly",
        "--mount",
        f"type=bind,source={toolchain},target=/risc0/toolchains/{resources.RISC0_TOOLCHAIN_DIRECTORY},readonly",
        "--mount",
        f"type=bind,source={wrapper},target=/pinned-bin/cargo,readonly",
        "--tmpfs",
        resources.tmpfs("/tmp", 64 * 1024 * 1024, "1777", uid, gid, noexec=True),
        "--tmpfs",
        target_mount,
        "--tmpfs",
        resources.tmpfs("/cargo", 16 * 1024 * 1024, "0700", uid, gid, noexec=True),
        "--tmpfs",
        resources.tmpfs(
            "/sandbox-home",
            4 * 1024 * 1024,
            "0700",
            uid,
            gid,
            noexec=True,
        ),
        "--env",
        f"PATH=/pinned-bin:/risc0/toolchains/{resources.RISC0_TOOLCHAIN_DIRECTORY}/bin:/usr/bin:/bin",
        "--env",
        "HOME=/sandbox-home",
        "--workdir",
        "/probe",
        "--entrypoint",
        "/bin/bash",
        planner.BUILD_IMAGE,
        "-p",
        "-ceu",
        "install -d -m 0700 /cargo /sandbox-home; "
        "ln -s /cargo /sandbox-home/.cargo; "
        "printf '%s\\n' '[build]' 'jobs = 9' '' '[net]' 'offline = true' "
        "> /cargo/config.toml; "
        "unset CARGO_BUILD_JOBS CARGO_HOME CARGO_NET_OFFLINE; "
        "cargo build --locked --offline --target-dir /build/target; "
        "test -x /build/target/debug/nested-wrapper-probe",
    )

    completed = subprocess.run(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=180,
        check=False,
    )

    assert completed.returncode == 0, completed.stderr.decode(errors="replace")


@pytest.mark.skipif(
    os.environ.get("ZENODEX_RUN_NATIVE_ZRPF_IDENTITY_RUNNER") != "1",
    reason="live private-CID cleanup probe is opt-in",
)
def test_live_private_cidfile_binds_exact_container_cleanup(tmp_path: Path) -> None:
    runner = _cleanup_runner(tmp_path)
    suffix = hashlib.sha256(os.fsencode(tmp_path)).hexdigest()[:16]
    name = f"zrpf-v6-cid-probe-{suffix}"
    cidfile = tmp_path / "container.cid"
    created = False

    runner._require_container_absent(name)
    try:
        result = runner_module.process_runner.run_bounded(
            runner_module.process_runner.ProcessRequest(
                command=(
                    str(runner._docker),
                    "create",
                    "--name",
                    name,
                    "--cidfile",
                    str(cidfile),
                    "--network",
                    "none",
                    "--read-only",
                    "--cap-drop",
                    "ALL",
                    "--security-opt",
                    "no-new-privileges",
                    planner.BUILD_IMAGE,
                    "/bin/true",
                ),
                cwd=tmp_path,
                env=runner_module.replay_environment.clean_environment(),
                timeout_seconds=60,
                output_limit_bytes=4_096,
                profile=runner_module.process_runner.ProcessProfile.TOOL,
            )
        )
        assert result.returncode == 0, result.stderr.decode(errors="replace")
        assert result.stderr == b""
        created = True
        container_id = runner_module._read_container_id(cidfile)
        assert container_id is not None
        assert result.stdout == (container_id + "\n").encode("ascii")
        assert stat.S_IMODE(cidfile.stat().st_mode) == 0o600

        runner._cleanup_owned_container(name, cidfile)
        created = False
        assert runner_module._inspect_confirms_absent(runner._inspect_container(name), name)
    finally:
        if created:
            subprocess.run(
                (str(runner._docker), "rm", "--force", name),
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=30,
                check=False,
            )


def _registry(tmp_path: Path) -> Path:
    registry = tmp_path / "registry"
    (registry / "cache").mkdir(parents=True)
    (registry / "index").mkdir()
    (registry / "src/crate").mkdir(parents=True)
    (registry / "CACHEDIR.TAG").write_bytes(b"tag")
    (registry / "cache/a.crate").write_bytes(b"crate")
    (registry / "index/config.json").write_bytes(b"index")
    (registry / "src/crate/lib.rs").write_bytes(b"lib")
    return registry


def _request(tmp_path: Path) -> BuildRequest:
    target = "/build/01-source-spot/target"
    return BuildRequest(
        kind=BuildKind.GUEST,
        pass_id="primary:source_spot",
        stage_id="source_spot",
        source_commit="a" * 40,
        source_snapshot=tmp_path / "snapshot",
        target_directory=tmp_path / "target",
        output_directory=tmp_path / "output",
        container_target_directory=target,
        container_output_directory="/build/01-source-spot/output",
        artifact_file="source_spot.bin",
        command=(
            planner.CANONICAL_CARGO,
            "build",
            "--locked",
            "--offline",
            "--jobs",
            "2",
            "--target-dir",
            target,
        ),
        extraction_source=f"{target}/source_spot.bin",
        companion_artifact_file="source_spot_cli",
        companion_extraction_source=f"{target}/source_spot_cli",
    )


def _replace_command_value(
    request: BuildRequest,
    option: str,
    replacement: str,
) -> BuildRequest:
    from dataclasses import replace

    command = list(request.command)
    command[command.index(option) + 1] = replacement
    return replace(request, command=tuple(command))


def _runner_output(
    request: BuildRequest,
    artifact: bytes,
    companion: bytes | None,
) -> bytes:
    artifact_encoded = base64.b64encode(artifact)
    companion_encoded = b"" if companion is None else base64.b64encode(companion)
    companion_sha = "-" if companion is None else hashlib.sha256(companion).hexdigest()
    image_id = "a" * 64 if request.kind is BuildKind.GUEST else "-"
    header = (
        f"ZRPF_BUILD_RESULT_V2 {request.kind.value} {len(artifact)} "
        f"{hashlib.sha256(artifact).hexdigest()} {image_id} {len(artifact_encoded)} "
        f"{0 if companion is None else len(companion)} {companion_sha} "
        f"{len(companion_encoded)}\n"
    ).encode("ascii")
    return header + artifact_encoded + b"\n" + companion_encoded + b"\nZRPF_END\n"


def _cleanup_runner(tmp_path: Path) -> runner_module.DockerBuildRunner:
    runner = object.__new__(runner_module.DockerBuildRunner)
    runner._docker = Path("/usr/bin/docker")
    runner._risc0_home = tmp_path
    return runner


def _absent(name: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.CompletedProcess(
        [],
        1,
        b"\n",
        f"Error: No such container: {name}\n".encode("ascii"),
    )
