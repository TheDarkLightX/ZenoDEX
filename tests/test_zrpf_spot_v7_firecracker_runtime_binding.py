from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools import zrpf_spot_v7_firecracker_jail_staging as spot_v7_staging
from tools import zrpf_spot_v7_firecracker_jailer_lifecycle as lifecycle
from tools import zrpf_spot_v7_firecracker_runtime_binding as runtime_binding
from tools import zrpf_spot_v7_firecracker_runtime_manifest as runtime_manifest
from tools import zrpf_spot_v7_firecracker_runtime_protocol as protocol
from tools import zrpf_v3_firecracker_jail_staging as staging

ROOT = Path(__file__).resolve().parents[1]


def test_runtime_binding_retains_exact_proposal_bytes_with_authority_false() -> None:
    config = _canonical(_configuration())
    manifest = _runtime_manifest(config)

    binding = runtime_binding.ProposedSpotV7FirecrackerRuntimeBindingV1.validated(
        exact_machine_config_bytes=config,
        exact_runtime_manifest_bytes=manifest,
        runtime_profile_sha256=protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
    )

    assert binding.exact_machine_config_bytes == config
    assert binding.exact_runtime_manifest_bytes == manifest
    assert binding.machine_config_sha256 == hashlib.sha256(config).digest()
    assert binding.runtime_manifest_sha256 == hashlib.sha256(manifest).digest()
    assert binding.runtime_manifest_schema_verified is True
    assert binding.machine_config_manifest_binding_verified is True
    assert binding.artifact_role_contract_verified is True
    assert binding.runtime_manifest.artifact_set_id
    assert binding.artifact_bytes_verified is False
    assert binding.governance_admission_verified is False
    assert binding.governed_machine_config_verified is False
    assert binding.governed_runtime_manifest_verified is False
    assert binding.independent_expected_digests_verified is False
    assert binding.live_firecracker_execution_verified is False
    assert binding.release_authority is False
    assert binding.settlement_authority is False
    assert binding.production_authority is False


def test_stale_runtime_profile_rejects_before_staging() -> None:
    with pytest.raises(
        runtime_binding.SpotV7FirecrackerRuntimeBindingRejectV1,
        match="runtime_binding_profile",
    ):
        runtime_binding.ProposedSpotV7FirecrackerRuntimeBindingV1.validated(
            exact_machine_config_bytes=_canonical(_configuration()),
            exact_runtime_manifest_bytes=_canonical({"schema": "test"}),
            runtime_profile_sha256=b"s" * 32,
        )


@pytest.mark.parametrize(
    "manifest",
    [
        b'{"schema":"a","schema":"b"}\n',
        b'{"ratio":1.5}\n',
        b'{"schema":"missing-canonical-newline"}',
    ],
)
def test_runtime_manifest_requires_exact_bounded_canonical_json(
    manifest: bytes,
) -> None:
    with pytest.raises(
        runtime_binding.SpotV7FirecrackerRuntimeBindingRejectV1,
        match="runtime_binding_manifest",
    ):
        runtime_binding.ProposedSpotV7FirecrackerRuntimeBindingV1.validated(
            exact_machine_config_bytes=_canonical(_configuration()),
            exact_runtime_manifest_bytes=manifest,
            runtime_profile_sha256=(
                protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
            ),
        )


def test_machine_config_substitution_rejects_before_filesystem_effect(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    changed = _configuration()
    machine_config = changed["machine-config"]
    assert isinstance(machine_config, dict)
    machine_config["mem_size_mib"] = 512

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_spot_v7_machine_config_binding",
    ):
        inputs.prepare(config_bytes=_canonical(changed))

    assert not inputs.spec.jail_root_path.parent.exists()


def test_runtime_manifest_substitution_rejects_before_filesystem_effect(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    request = protocol.SpotV7FirecrackerRequestV1.validated(
        run_nonce_256=b"n" * 32,
        runtime_manifest_sha256=b"x" * 32,
        machine_config_sha256=inputs.binding.machine_config_sha256,
        input_drive_sha256=inputs.input_sha256,
        settlement_intent_sha256=b"i" * 32,
    ).encode()

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_spot_v7_runtime_manifest_binding",
    ):
        inputs.prepare(request_bytes=request)

    assert not inputs.spec.jail_root_path.parent.exists()


def test_post_prepare_config_path_identity_replacement_rejects(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    resources = prepared.jail_root_path / "resources"
    config_path = resources / "config.json"
    exact = config_path.read_bytes()
    resources.chmod(0o755)
    config_path.unlink()
    config_path.write_bytes(exact)
    config_path.chmod(0o444)

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_resource_identity_changed",
    ):
        prepared.verify_prelaunch()

    resources.chmod(0o555)
    prepared.abandon_before_launch()


def test_prepare_observation_retains_exact_config_and_runtime_identities(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()

    observation = prepared.prepare_observation()
    document = json.loads(observation.canonical_bytes())

    assert document["schema"] == (
        "zenodex/zrpf_spot_v7_firecracker_prepare_observation/v1"
    )
    assert document["runtime_binding"] == {
        "exact_machine_config_ascii": inputs.binding.exact_machine_config_bytes.decode(
            "ascii"
        ),
        "exact_runtime_manifest_ascii": (
            inputs.binding.exact_runtime_manifest_bytes.decode("ascii")
        ),
        "machine_config_sha256": inputs.binding.machine_config_sha256.hex(),
        "request_sha256": hashlib.sha256(inputs.request_bytes).hexdigest(),
        "runtime_manifest_sha256": inputs.binding.runtime_manifest_sha256.hex(),
        "runtime_manifest_artifact_set_id": (
            inputs.binding.runtime_manifest.artifact_set_id.hex()
        ),
        "runtime_manifest_schema": runtime_manifest.SPOT_V7_RUNTIME_MANIFEST_SCHEMA_V1,
        "runtime_profile_sha256": (
            protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1.hex()
        ),
    }
    assert all(value is False for value in document["authority"].values())
    prepared.abandon_before_launch()


def test_v7_lifecycle_finish_binds_prepare_and_rejects_identity_substitution(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    jail_root = prepared.jail_root_path
    launch_observation = lifecycle._JailerLaunchObservationV1(
        jailer_pid=41,
        process_set=frozenset({41, 42}),
        cgroup_relative_path="zrpf/run00001",
    )
    request = protocol.decode_exact_request_v1(inputs.request_bytes)
    committed_output = protocol.build_data_only_committed_output_v1(
        request,
        observed_input_drive_sha256=inputs.input_sha256,
        payload=_golden_payload(),
    )

    def launch() -> tuple[_FakeProcess, lifecycle._JailerLaunchObservationV1]:
        output = prepared.jail_root_path / "resources/output"
        with output.open("r+b") as stream:
            stream.write(committed_output)
        return _FakeProcess(41), launch_observation

    def finish(
        _process: lifecycle.ProcessHandle,
        observation: lifecycle._JailerLaunchObservationV1,
        prepare: runtime_binding.SpotV7FirecrackerPrepareObservationV1,
    ) -> dict[str, object]:
        return lifecycle._spot_v7_finish_observation_document_v1(
            observation=observation,
            prepare_observation=prepare,
            exit_code=0,
        )

    completed = lifecycle._complete_prepared_spot_v7_jailer_lifecycle_for_test(
        prepared_jail=prepared,
        launch=launch,
        finish=finish,
    )
    finish_document = completed.finish_observation
    finish_bytes = _canonical(finish_document)
    validated = lifecycle._validate_exact_spot_v7_finish_observation_v1(
        finish_bytes,
        observation=launch_observation,
        prepare_observation=_prepare_from_document(inputs),
    )

    assert validated == finish_document
    assert validated["prepare_observation"] == completed.prepare_observation
    authority = validated["authority"]
    assert isinstance(authority, dict)
    assert all(value is False for value in authority.values())
    assert not jail_root.exists()

    for field in (
        "exact_machine_config_ascii",
        "exact_runtime_manifest_ascii",
    ):
        changed = json.loads(finish_bytes)
        changed["prepare_observation"]["runtime_binding"][field] += " "
        with pytest.raises(
            lifecycle.JailerLauncherReject,
            match="jailer_spot_v7_finish_binding_mismatch",
        ):
            lifecycle._validate_exact_spot_v7_finish_observation_v1(
                _canonical(changed),
                observation=launch_observation,
                prepare_observation=_prepare_from_document(inputs),
            )

    changed = json.loads(finish_bytes)
    changed["authority"]["production_authority"] = 0
    with pytest.raises(
        lifecycle.JailerLauncherReject,
        match="jailer_spot_v7_finish_binding_mismatch",
    ):
        lifecycle._validate_exact_spot_v7_finish_observation_v1(
            _canonical(changed),
            observation=launch_observation,
            prepare_observation=_prepare_from_document(inputs),
        )


def test_v7_lifecycle_prelaunch_failure_abandons_prepared_jail(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    jail_root = prepared.jail_root_path
    output = jail_root / "resources/output"
    with output.open("r+b") as stream:
        stream.seek(len(inputs.request_bytes))
        stream.write(b"\x01")

    launch_called = False

    def launch() -> tuple[_FakeProcess, lifecycle._JailerLaunchObservationV1]:
        nonlocal launch_called
        launch_called = True
        raise AssertionError("launch must not run after prelaunch rejection")

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_output_not_fresh",
    ):
        lifecycle._complete_prepared_spot_v7_jailer_lifecycle_for_test(
            prepared_jail=prepared,
            launch=launch,
            finish=lambda _process, _observation, _prepare: {},
        )

    assert launch_called is False
    assert not jail_root.exists()


def test_v7_lifecycle_launch_failure_quarantines_prepared_jail(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    jail_root = prepared.jail_root_path

    def fail_launch() -> tuple[_FakeProcess, lifecycle._JailerLaunchObservationV1]:
        raise staging.JailerLauncherReject("test_launch_state_uncertain")

    with pytest.raises(
        staging.JailerLauncherReject,
        match="test_launch_state_uncertain",
    ):
        lifecycle._complete_prepared_spot_v7_jailer_lifecycle_for_test(
            prepared_jail=prepared,
            launch=fail_launch,
            finish=lambda _process, _observation, _prepare: {},
        )

    assert jail_root.exists()
    prepared.cleanup_after_teardown()
    assert not jail_root.exists()


def test_v7_lifecycle_finish_failure_quarantines_prepared_jail(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    jail_root = prepared.jail_root_path
    observation = lifecycle._JailerLaunchObservationV1(
        jailer_pid=41,
        process_set=frozenset({41, 42}),
        cgroup_relative_path="zrpf/run00001",
    )

    def fail_finish(
        _process: lifecycle.ProcessHandle,
        _observation: lifecycle._JailerLaunchObservationV1,
        _prepare: runtime_binding.SpotV7FirecrackerPrepareObservationV1,
    ) -> dict[str, object]:
        raise staging.JailerLauncherReject("test_finish_state_uncertain")

    with pytest.raises(
        staging.JailerLauncherReject,
        match="test_finish_state_uncertain",
    ):
        lifecycle._complete_prepared_spot_v7_jailer_lifecycle_for_test(
            prepared_jail=prepared,
            launch=lambda: (_FakeProcess(41), observation),
            finish=fail_finish,
        )

    assert jail_root.exists()
    prepared.cleanup_after_teardown()
    assert not jail_root.exists()


def test_v7_lifecycle_output_reject_after_verified_finish_removes_prepared_jail(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    jail_root = prepared.jail_root_path
    observation = lifecycle._JailerLaunchObservationV1(
        jailer_pid=41,
        process_set=frozenset({41, 42}),
        cgroup_relative_path="zrpf/run00001",
    )

    def finish(
        _process: lifecycle.ProcessHandle,
        exact_observation: lifecycle._JailerLaunchObservationV1,
        prepare: runtime_binding.SpotV7FirecrackerPrepareObservationV1,
    ) -> dict[str, object]:
        return lifecycle._spot_v7_finish_observation_document_v1(
            observation=exact_observation,
            prepare_observation=prepare,
            exit_code=0,
        )

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_output_protocol_rejected",
    ):
        lifecycle._complete_prepared_spot_v7_jailer_lifecycle_for_test(
            prepared_jail=prepared,
            launch=lambda: (_FakeProcess(41), observation),
            finish=finish,
        )

    assert not jail_root.exists()


@dataclass(slots=True)
class _Inputs:
    spec: staging.PreparedJailRootSpecV2
    artifacts: tuple[staging.RootOwnedStagedArtifactV2, ...]
    binding: runtime_binding.ProposedSpotV7FirecrackerRuntimeBindingV1
    request_bytes: bytes
    input_sha256: bytes
    trusted_root: Path

    def prepare(
        self,
        *,
        config_bytes: bytes | None = None,
        request_bytes: bytes | None = None,
    ) -> spot_v7_staging.PreparedSpotV7JailRootV1:
        return spot_v7_staging.prepare_root_owned_spot_v7_jail_v1(
            spec=self.spec,
            artifacts=self.artifacts,
            config_bytes=(
                self.binding.exact_machine_config_bytes
                if config_bytes is None
                else config_bytes
            ),
            request_bytes=self.request_bytes if request_bytes is None else request_bytes,
            runtime_binding=self.binding,
            trusted_chroot_root=self.trusted_root,
            trusted_source_root=self.trusted_root,
        )


@dataclass(slots=True)
class _FakeProcess:
    pid: int

    def poll(self) -> int | None:
        return 0

    def wait(self, timeout: float | None = None) -> int:
        del timeout
        return 0

    def kill(self) -> None:
        return None


def _inputs(tmp_path: Path) -> _Inputs:
    uid = os.getuid()
    runtime_uid = uid if uid != 0 else 65534
    runtime_gid = os.getgid() if uid != 0 else 65534
    chroot_base = tmp_path / "jailer"
    exec_dir = chroot_base / "firecracker"
    exec_dir.mkdir(parents=True, mode=0o700)
    chroot_base.chmod(0o700)
    exec_dir.chmod(0o700)
    sources = tmp_path / "sources"
    sources.mkdir(mode=0o700)
    artifacts: list[staging.RootOwnedStagedArtifactV2] = []
    input_sha256 = b""
    for role in ("input", "kernel", "rootfs"):
        raw = f"governed-{role}".encode("ascii")
        path = sources / role
        path.write_bytes(raw)
        path.chmod(0o400)
        digest = hashlib.sha256(raw).digest()
        if role == "input":
            input_sha256 = digest
        artifacts.append(
            staging.RootOwnedStagedArtifactV2(
                role=role,
                source_path=path,
                sha256=digest.hex(),
                size_bytes=len(raw),
            )
        )
    config = _canonical(_configuration())
    manifest = _runtime_manifest(config)
    binding = runtime_binding.ProposedSpotV7FirecrackerRuntimeBindingV1.validated(
        exact_machine_config_bytes=config,
        exact_runtime_manifest_bytes=manifest,
        runtime_profile_sha256=protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
    )
    request = protocol.SpotV7FirecrackerRequestV1.validated(
        run_nonce_256=b"n" * 32,
        runtime_manifest_sha256=binding.runtime_manifest_sha256,
        machine_config_sha256=binding.machine_config_sha256,
        input_drive_sha256=input_sha256,
        settlement_intent_sha256=b"i" * 32,
    ).encode()
    spec = staging.PreparedJailRootSpecV2(
        jail_id="run00001",
        firecracker_file_name="firecracker",
        chroot_base_dir=chroot_base,
        runtime_uid=runtime_uid,
        runtime_gid=runtime_gid,
        trusted_uid=uid,
    )
    return _Inputs(spec, tuple(artifacts), binding, request, input_sha256, tmp_path)


def _configuration() -> dict[str, object]:
    return {
        "boot-source": {
            "boot_args": (
                f"init={runtime_manifest.SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1}"
            ),
            "kernel_image_path": "/resources/kernel",
        },
        "drives": [
            {
                "drive_id": "rootfs",
                "is_read_only": True,
                "is_root_device": True,
                "path_on_host": "/resources/rootfs",
            },
            {
                "drive_id": "input",
                "is_read_only": True,
                "is_root_device": False,
                "path_on_host": "/resources/input",
            },
            {
                "drive_id": "output",
                "is_read_only": False,
                "is_root_device": False,
                "path_on_host": "/resources/output",
            },
        ],
        "machine-config": {
            "mem_size_mib": 256,
            "smt": False,
            "track_dirty_pages": False,
            "vcpu_count": 1,
        },
    }


def _canonical(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("ascii")


def _runtime_manifest(config: bytes) -> bytes:
    artifacts = tuple(
        runtime_manifest.SpotV7RuntimeArtifactIdentityV1.validated(
            role=role,
            artifact_name=runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1[role],
            sha256=bytes([index]) * 32,
            size_bytes=4_096 + index,
        )
        for index, role in enumerate(
            runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1,
            start=1,
        )
    )
    return runtime_manifest.build_candidate_spot_v7_runtime_manifest_v1(
        exact_machine_config_bytes=config,
        artifacts=artifacts,
        v7_image_id=tuple(0x10 + index for index in range(8)),
        v6_image_id=tuple(0x80 + index for index in range(8)),
    )


def _golden_payload() -> bytes:
    path = (
        ROOT
        / "zk/spot_settlement_v7_risc0/verifier/tests/vectors/"
        "spot_settlement_v7_firecracker_output_v1.hex"
    )
    compact = "".join(
        line.split("//", maxsplit=1)[0].strip()
        for line in path.read_text(encoding="ascii").splitlines()
    )
    return bytes.fromhex(compact)


def _prepare_from_document(
    inputs: _Inputs,
) -> runtime_binding.SpotV7FirecrackerPrepareObservationV1:
    return runtime_binding._new_prepare_observation(
        inputs.binding,
        request_sha256=hashlib.sha256(inputs.request_bytes).digest(),
    )
