"""CBC tests for the descriptor-to-launch Spot V7 Firecracker bridge."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import pickle
from dataclasses import dataclass
from pathlib import Path
from typing import cast

import pytest

from tools import zrpf_spot_v7_firecracker_artifact_binding as artifact_binding
from tools import zrpf_spot_v7_firecracker_descriptor_staging as descriptor_staging
from tools import zrpf_spot_v7_firecracker_runtime_manifest as runtime_manifest
from tools import zrpf_spot_v7_firecracker_runtime_protocol as runtime_protocol
from tools import zrpf_v3_firecracker_jail_staging as jail_staging


@dataclass(frozen=True, slots=True)
class _Fixture:
    config: bytes
    manifest: bytes
    request: bytes
    sources: tuple[artifact_binding.SpotV7RuntimeArtifactSourceV1, ...]
    paths: dict[str, Path]
    artifact_root: Path
    launch_root: Path
    trusted_root: Path
    trusted_uid: int
    jail_spec: jail_staging.PreparedJailRootSpecV2

    def open_bound(
        self,
    ) -> artifact_binding._DescriptorBoundSpotV7FirecrackerRuntimeBindingV1:
        return artifact_binding.open_descriptor_bound_spot_v7_runtime_binding_v1(
            exact_machine_config_bytes=self.config,
            exact_runtime_manifest_bytes=self.manifest,
            artifact_sources=self.sources,
            runtime_profile_sha256=(
                runtime_protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
            ),
            trusted_source_root=self.trusted_root,
            trusted_uid=self.trusted_uid,
        )

    def prepare(
        self,
        bound: artifact_binding._DescriptorBoundSpotV7FirecrackerRuntimeBindingV1,
    ) -> descriptor_staging._PreparedDescriptorBoundSpotV7LaunchV1:
        return descriptor_staging.prepare_descriptor_bound_spot_v7_launch_v1(
            descriptor_bound_runtime=bound,
            jail_spec=self.jail_spec,
            request_bytes=self.request,
            launch_snapshot_root=self.launch_root,
            trusted_chroot_root=self.trusted_root,
            trusted_snapshot_root=self.trusted_root,
        )


def test_descriptor_bridge_stages_exact_manifest_without_reopening_caller_paths(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    bound = fixture.open_bound()
    original_sources = frozenset(fixture.paths.values())
    reopened: list[Path] = []
    original_open = descriptor_staging.staging_io.open_trusted_source

    def record_snapshot_open(
        path: Path,
        *,
        trusted_root: Path,
        trusted_uid: int,
    ) -> int:
        reopened.append(path)
        return original_open(
            path,
            trusted_root=trusted_root,
            trusted_uid=trusted_uid,
        )

    monkeypatch.setattr(
        descriptor_staging.staging_io,
        "open_trusted_source",
        record_snapshot_open,
    )

    prepared = fixture.prepare(bound)
    try:
        prepared.verify_prelaunch()
        assert prepared.artifact_roles == runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1
        assert prepared.artifact_set_id == prepared.runtime_manifest.artifact_set_id
        assert prepared.runtime_manifest_sha256 == hashlib.sha256(fixture.manifest).digest()
        assert prepared.launch_spec.jail_id == fixture.jail_spec.jail_id
        assert prepared.launch_spec.chroot_base_dir == fixture.jail_spec.chroot_base_dir
        assert prepared.snapshot_root_path == fixture.launch_root / fixture.jail_spec.jail_id
        assert all(path not in original_sources for path in reopened)
        assert {path.name for path in reopened} == {"input", "kernel", "rootfs"}
        for role in ("firecracker", "guest_init", "jailer"):
            assert prepared.snapshot_artifact_path(role).stat().st_mode & 0o111
        assert prepared.governance_admission_verified is False
        assert prepared.live_firecracker_execution_verified is False
        assert prepared.release_authority is False
        assert prepared.settlement_authority is False
        assert prepared.production_authority is False
    finally:
        prepared.close_before_launch()

    assert not prepared.snapshot_root_path.exists()


def test_post_open_path_substitution_rejects_before_snapshot_staging(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    bound = fixture.open_bound()
    target = fixture.paths["kernel"]
    exact = target.read_bytes()
    target.rename(target.with_name("kernel-old"))
    target.write_bytes(exact)
    target.chmod(0o400)

    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as captured:
        fixture.prepare(bound)

    assert captured.value.code == "runtime_artifact_path_replaced"
    assert not (fixture.launch_root / fixture.jail_spec.jail_id).exists()


def test_descriptor_truncation_rejects_and_spends_source_capability(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    bound = fixture.open_bound()
    target = fixture.paths["input"]
    target.chmod(0o600)
    with target.open("r+b") as stream:
        stream.truncate(target.stat().st_size - 1)
    target.chmod(0o400)

    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as captured:
        fixture.prepare(bound)
    assert captured.value.code == "runtime_artifact_source_changed"

    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as reused:
        fixture.prepare(bound)
    assert reused.value.code == "runtime_artifact_binding_spent"


def test_closed_source_descriptor_rejects_and_closes_complete_set(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    bound = fixture.open_bound()
    descriptors = tuple(record.descriptor for record in bound._artifacts._records)
    os.close(descriptors[2])

    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as captured:
        fixture.prepare(bound)
    assert captured.value.code == "runtime_artifact_descriptor_invalid"
    for descriptor in descriptors:
        with pytest.raises(OSError):
            os.fstat(descriptor)


def test_role_swap_inside_retained_set_rejects_before_any_copy(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    bound = fixture.open_bound()
    records = list(bound._artifacts._records)
    records[0], records[1] = records[1], records[0]
    object.__setattr__(bound._artifacts, "_records", tuple(records))

    with pytest.raises(
        descriptor_staging.SpotV7DescriptorStagingRejectV1
    ) as captured:
        fixture.prepare(bound)
    assert captured.value.code == "descriptor_stage_artifact_inventory"
    assert not (fixture.launch_root / fixture.jail_spec.jail_id).exists()


def test_partial_snapshot_failure_removes_stage_and_closes_source_descriptors(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    bound = fixture.open_bound()
    descriptors = tuple(record.descriptor for record in bound._artifacts._records)
    original_copy = descriptor_staging.staging_io.copy_exact_artifact
    calls = 0

    def fail_third_copy(**kwargs: object) -> int:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise jail_staging.JailerLauncherReject("injected_partial_stage_failure")
        return original_copy(**kwargs)

    monkeypatch.setattr(
        descriptor_staging.staging_io,
        "copy_exact_artifact",
        fail_third_copy,
    )

    with pytest.raises(
        descriptor_staging.SpotV7DescriptorStagingRejectV1
    ) as captured:
        fixture.prepare(bound)
    assert captured.value.code == "descriptor_stage_snapshot_copy"
    assert not (fixture.launch_root / fixture.jail_spec.jail_id).exists()
    for descriptor in descriptors:
        with pytest.raises(OSError):
            os.fstat(descriptor)


def test_successful_preparation_spends_descriptor_binding_and_rejects_reuse(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    bound = fixture.open_bound()
    prepared = fixture.prepare(bound)
    try:
        with pytest.raises(
            artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
        ) as captured:
            fixture.prepare(bound)
        assert captured.value.code == "runtime_artifact_binding_spent"
    finally:
        prepared.close_before_launch()


def test_launch_handoff_is_one_shot_and_retains_exact_executables(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    prepared = fixture.prepare(fixture.open_bound())

    handoff = prepared._take_for_lifecycle_v1(
        descriptor_staging._LIFECYCLE_HANDOFF_REQUEST_SEAL_V1
    )
    try:
        handoff.verify_prelaunch()
        assert handoff.launch_spec == prepared.launch_spec
        assert handoff.jailer.path == prepared.snapshot_artifact_path("jailer")
        assert handoff.firecracker.path == prepared.snapshot_artifact_path("firecracker")
        with pytest.raises(
            descriptor_staging.SpotV7DescriptorStagingRejectV1
        ) as captured:
            prepared._take_for_lifecycle_v1(
                descriptor_staging._LIFECYCLE_HANDOFF_REQUEST_SEAL_V1
            )
        assert captured.value.code == "descriptor_stage_launch_spent"
    finally:
        handoff.abandon_before_launch()


def test_close_before_launch_is_idempotent_and_blocks_future_use(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    prepared = fixture.prepare(fixture.open_bound())

    prepared.close_before_launch()
    prepared.close_before_launch()

    with pytest.raises(
        descriptor_staging.SpotV7DescriptorStagingRejectV1
    ) as captured:
        prepared.verify_prelaunch()
    assert captured.value.code == "descriptor_stage_launch_closed"


def test_close_before_launch_closes_snapshot_and_executable_descriptors(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    prepared = fixture.prepare(fixture.open_bound())
    resources = prepared._resources
    descriptors = tuple(
        row.descriptor for row in resources.snapshot._state.artifacts
    ) + (
        resources.jailer._identity.parent_fd,
        resources.jailer._identity.file_fd,
        resources.firecracker._identity.parent_fd,
        resources.firecracker._identity.file_fd,
    )

    prepared.close_before_launch()

    for descriptor in descriptors:
        with pytest.raises(OSError):
            os.fstat(descriptor)
    assert not prepared.snapshot_root_path.exists()


def test_prepared_and_handoff_types_are_sealed_noncopyable_nonserializable(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    prepared = fixture.prepare(fixture.open_bound())
    try:
        for operation in (
            lambda: copy.copy(prepared),
            lambda: copy.deepcopy(prepared),
            lambda: pickle.dumps(prepared),
        ):
            with pytest.raises(TypeError):
                operation()
        with pytest.raises(TypeError, match="module-private seal"):
            descriptor_staging._PreparedDescriptorBoundSpotV7LaunchV1(
                resources=cast(descriptor_staging._LaunchResourcesV1, object()),
                seal=cast(descriptor_staging._PreparedLaunchSealV1, object()),
            )
    finally:
        prepared.close_before_launch()


def _fixture(tmp_path: Path) -> _Fixture:
    trusted_uid = os.getuid()
    runtime_uid = trusted_uid if trusted_uid != 0 else 65_534
    runtime_gid = os.getgid() if trusted_uid != 0 else 65_534
    artifact_root = tmp_path / "artifacts"
    launch_root = tmp_path / "launch-snapshots"
    chroot_base = tmp_path / "jailer"
    for directory in (artifact_root, launch_root, chroot_base):
        directory.mkdir(mode=0o700)
    (chroot_base / "firecracker").mkdir(mode=0o700)
    paths: dict[str, Path] = {}
    identities: list[runtime_manifest.SpotV7RuntimeArtifactIdentityV1] = []
    sources: list[artifact_binding.SpotV7RuntimeArtifactSourceV1] = []
    input_sha256 = b""
    for index, role in enumerate(
        runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1,
        start=1,
    ):
        name = runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1[role]
        raw = (f"governed-{role}-" * (index + 1)).encode("ascii")
        path = artifact_root / name
        path.write_bytes(raw)
        path.chmod(0o400)
        digest = hashlib.sha256(raw).digest()
        if role == "input":
            input_sha256 = digest
        identities.append(
            runtime_manifest.SpotV7RuntimeArtifactIdentityV1.validated(
                role=role,
                artifact_name=name,
                sha256=digest,
                size_bytes=len(raw),
            )
        )
        sources.append(
            artifact_binding.SpotV7RuntimeArtifactSourceV1.validated(
                role=role,
                source_path=path,
            )
        )
        paths[role] = path
    config = _canonical(_machine_config())
    manifest = runtime_manifest.build_candidate_spot_v7_runtime_manifest_v1(
        exact_machine_config_bytes=config,
        artifacts=tuple(identities),
        v7_image_id=tuple(0x10 + index for index in range(8)),
        v6_image_id=tuple(0x80 + index for index in range(8)),
    )
    request = runtime_protocol.SpotV7FirecrackerRequestV1.validated(
        run_nonce_256=b"n" * 32,
        runtime_manifest_sha256=hashlib.sha256(manifest).digest(),
        machine_config_sha256=hashlib.sha256(config).digest(),
        input_drive_sha256=input_sha256,
        settlement_intent_sha256=b"i" * 32,
    ).encode()
    return _Fixture(
        config=config,
        manifest=manifest,
        request=request,
        sources=tuple(sources),
        paths=paths,
        artifact_root=artifact_root,
        launch_root=launch_root,
        trusted_root=tmp_path,
        trusted_uid=trusted_uid,
        jail_spec=jail_staging.PreparedJailRootSpecV2(
            jail_id="run00001",
            firecracker_file_name="firecracker",
            chroot_base_dir=chroot_base,
            runtime_uid=runtime_uid,
            runtime_gid=runtime_gid,
            trusted_uid=trusted_uid,
        ),
    )


def _machine_config() -> dict[str, object]:
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
