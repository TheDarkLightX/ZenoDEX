from __future__ import annotations

import copy
import hashlib
import json
import os
import pickle
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools import zrpf_v3_firecracker_jail_staging as staging
from tools.zrpf_v3_firecracker_output_protocol import (
    OUTPUT_BYTES_V1,
    FirecrackerRequestV1,
    build_committed_output,
)


def test_prepared_jail_retains_exact_private_resources_and_fresh_output(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)

    prepared = inputs.prepare()

    prepared.verify_prelaunch()
    resources = prepared.jail_root_path / "resources"
    assert sorted(path.name for path in resources.iterdir()) == [
        "config.json",
        "input",
        "kernel",
        "output",
        "rootfs",
    ]
    assert (resources / "output").stat().st_size == OUTPUT_BYTES_V1
    assert (resources / "output").read_bytes()[:192] == inputs.request_bytes
    prepared.abandon_before_launch()
    assert not (inputs.spec.chroot_base_dir / "firecracker" / "run00001").exists()


def test_source_mutation_after_capture_cannot_change_staged_artifact(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    source = inputs.artifacts[0].source_path
    staged = prepared.jail_root_path / "resources" / inputs.artifacts[0].role
    expected = staged.read_bytes()

    source.chmod(0o600)
    source.write_bytes(b"attacker replacement")
    source.chmod(0o400)

    prepared.verify_prelaunch()
    assert staged.read_bytes() == expected
    prepared.abandon_before_launch()


def test_staged_artifact_mutation_rejects_before_launch(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    kernel = prepared.jail_root_path / "resources" / "kernel"
    kernel.chmod(0o600)
    kernel.write_bytes(b"mutated kernel")

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_immutable_resource_changed",
    ):
        prepared.verify_prelaunch()
    prepared.abandon_before_launch()


def test_staged_path_replacement_rejects_even_when_bytes_match(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    resources = prepared.jail_root_path / "resources"
    rootfs = prepared.jail_root_path / "resources" / "rootfs"
    original = rootfs.read_bytes()
    resources.chmod(0o755)
    rootfs.unlink()
    rootfs.write_bytes(original)
    rootfs.chmod(0o444)

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_resource_identity_changed",
    ):
        prepared.verify_prelaunch()
    resources.chmod(0o555)
    prepared.abandon_before_launch()


def test_preexisting_jail_id_rejects_without_removing_stale_tree(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    stale = inputs.spec.chroot_base_dir / "firecracker" / "run00001"
    stale.mkdir(mode=0o700)
    marker = stale / "do-not-delete"
    marker.write_bytes(b"stale")

    with pytest.raises(FileExistsError):
        inputs.prepare()

    assert marker.read_bytes() == b"stale"


def test_failed_final_prelaunch_removes_read_only_partial_stage(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    inputs = _inputs(tmp_path)

    def reject_final_prelaunch(_prepared: staging.PreparedJailRootV2) -> None:
        raise staging.JailerLauncherReject("injected_final_prelaunch_reject")

    monkeypatch.setattr(
        staging.PreparedJailRootV2,
        "verify_prelaunch",
        reject_final_prelaunch,
    )

    with pytest.raises(
        staging.JailerLauncherReject,
        match="injected_final_prelaunch_reject",
    ):
        inputs.prepare()

    target = inputs.spec.chroot_base_dir / "firecracker" / "run00001"
    assert not target.exists()


def test_nonzero_output_bytes_after_request_reject_prelaunch(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    output = prepared.jail_root_path / "resources" / "output"
    with output.open("r+b", buffering=0) as handle:
        handle.seek(192)
        handle.write(b"\x01")

    with pytest.raises(staging.JailerLauncherReject, match="jail_stage_output_not_fresh"):
        prepared.verify_prelaunch()
    prepared.abandon_before_launch()


def test_post_exit_output_is_read_through_retained_descriptor(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    request = staging.decode_request(inputs.request_bytes)
    committed = build_committed_output(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=b"verified-v7-payload",
    )
    output = prepared.jail_root_path / "resources" / "output"
    with output.open("r+b", buffering=0) as handle:
        handle.seek(0)
        handle.write(committed)
        handle.flush()
        os.fsync(handle.fileno())

    assert prepared.read_validated_output_after_exit() == committed
    prepared.cleanup_after_teardown()


def test_uncommitted_output_rejects_after_exit(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_output_protocol_rejected",
    ):
        prepared.read_validated_output_after_exit()
    prepared.cleanup_after_teardown()


def test_resource_directory_write_enable_rejects_before_output_path_reuse(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()
    resources = prepared.jail_root_path / "resources"
    output = prepared.jail_root_path / "resources" / "output"
    resources.chmod(0o755)
    output.unlink()
    output.write_bytes(b"\x00" * OUTPUT_BYTES_V1)
    output.chmod(0o600)

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_resource_identity_changed",
    ):
        prepared.read_output_after_exit()
    resources.chmod(0o555)
    prepared.cleanup_after_teardown()


def test_config_must_be_canonical_and_bind_all_resource_paths(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    document = json.loads(inputs.config_bytes)
    document["drives"][1]["path_on_host"] = "/attacker/input"
    inputs.config_bytes = _canonical(document)

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_config_resource_binding_invalid",
    ):
        inputs.prepare()

    target = inputs.spec.chroot_base_dir / "firecracker" / "run00001"
    assert not target.exists()


def test_duplicate_artifact_role_rejects_before_filesystem_effect(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    artifacts = inputs.artifacts
    inputs.artifacts = (artifacts[0], artifacts[0], artifacts[2])

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_artifact_inventory_invalid",
    ):
        inputs.prepare()


def test_staging_and_jailer_share_the_same_minimum_jail_id_width(
    tmp_path: Path,
) -> None:
    inputs = _inputs(tmp_path)

    with pytest.raises(
        staging.JailerLauncherReject,
        match="jail_stage_id_invalid",
    ):
        staging.PreparedJailRootSpecV2(
            jail_id="short",
            firecracker_file_name=inputs.spec.firecracker_file_name,
            chroot_base_dir=inputs.spec.chroot_base_dir,
            runtime_uid=inputs.spec.runtime_uid,
            runtime_gid=inputs.spec.runtime_gid,
            trusted_uid=inputs.spec.trusted_uid,
        )


def test_prepared_jail_is_process_local_nontransferable(tmp_path: Path) -> None:
    inputs = _inputs(tmp_path)
    prepared = inputs.prepare()

    for operation in (
        lambda: copy.copy(prepared),
        lambda: copy.deepcopy(prepared),
        lambda: pickle.dumps(prepared),
    ):
        with pytest.raises(TypeError):
            operation()
    with pytest.raises(TypeError, match="cannot be mutated"):
        prepared._closed = True
    prepared.abandon_before_launch()


@pytest.mark.skipif(
    os.environ.get("ZENODEX_RUN_PRIVILEGED_ZRPF_FIRECRACKER_STAGING") != "1",
    reason="set the explicit privileged staging opt-in",
)
def test_privileged_root_owned_staging_uses_distinct_runtime_owner(
    tmp_path: Path,
) -> None:
    if os.geteuid() != 0:
        pytest.fail("privileged Firecracker staging opt-in requires euid 0")
    runtime_uid = int(os.environ.get("ZENODEX_FIRECRACKER_TEST_UID", "65534"))
    runtime_gid = int(os.environ.get("ZENODEX_FIRECRACKER_TEST_GID", "65534"))
    inputs = _inputs_for_identities(
        tmp_path,
        trusted_uid=0,
        runtime_uid=runtime_uid,
        runtime_gid=runtime_gid,
    )

    prepared = inputs.prepare()

    resources = prepared.jail_root_path / "resources"
    assert resources.stat().st_uid == 0
    assert (resources / "kernel").stat().st_uid == 0
    assert (resources / "output").stat().st_uid == runtime_uid
    assert (resources / "output").stat().st_gid == runtime_gid
    prepared.abandon_before_launch()


@dataclass(slots=True)
class _Inputs:
    spec: staging.PreparedJailRootSpecV2
    artifacts: tuple[staging.RootOwnedStagedArtifactV2, ...]
    config_bytes: bytes
    request_bytes: bytes
    trusted_chroot_root: Path
    trusted_source_root: Path

    def prepare(self) -> staging.PreparedJailRootV2:
        return staging.prepare_root_owned_jail_v2(
            spec=self.spec,
            artifacts=self.artifacts,
            config_bytes=self.config_bytes,
            request_bytes=self.request_bytes,
            trusted_chroot_root=self.trusted_chroot_root,
            trusted_source_root=self.trusted_source_root,
        )


def _inputs(tmp_path: Path) -> _Inputs:
    runtime_uid = os.getuid() if os.getuid() != 0 else 65534
    runtime_gid = os.getgid() if os.getuid() != 0 else 65534
    return _inputs_for_identities(
        tmp_path,
        trusted_uid=os.getuid(),
        runtime_uid=runtime_uid,
        runtime_gid=runtime_gid,
    )


def _inputs_for_identities(
    tmp_path: Path,
    *,
    trusted_uid: int,
    runtime_uid: int,
    runtime_gid: int,
) -> _Inputs:
    chroot_base = tmp_path / "jailer"
    exec_dir = chroot_base / "firecracker"
    exec_dir.mkdir(parents=True, mode=0o700)
    chroot_base.chmod(0o700)
    exec_dir.chmod(0o700)
    source_root = tmp_path / "sources"
    source_root.mkdir(mode=0o700)
    artifacts: list[staging.RootOwnedStagedArtifactV2] = []
    for role in ("input", "kernel", "rootfs"):
        raw = f"governed-{role}".encode("ascii")
        path = source_root / role
        path.write_bytes(raw)
        path.chmod(0o400)
        artifacts.append(
            staging.RootOwnedStagedArtifactV2(
                role=role,
                source_path=path,
                sha256=hashlib.sha256(raw).hexdigest(),
                size_bytes=len(raw),
            )
        )
    request = FirecrackerRequestV1.validated(
        run_nonce_256=b"n" * 32,
        runtime_manifest_sha256=b"m" * 32,
        input_drive_sha256=b"i" * 32,
        replay_intent_sha256=b"r" * 32,
    ).encode()
    return _Inputs(
        spec=staging.PreparedJailRootSpecV2(
            jail_id="run00001",
            firecracker_file_name="firecracker",
            chroot_base_dir=chroot_base,
            runtime_uid=runtime_uid,
            runtime_gid=runtime_gid,
            trusted_uid=trusted_uid,
        ),
        artifacts=tuple(artifacts),
        config_bytes=_canonical(_configuration()),
        request_bytes=request,
        trusted_chroot_root=tmp_path,
        trusted_source_root=tmp_path,
    )


def _configuration() -> dict[str, object]:
    return {
        "boot-source": {
            "boot_args": "init=/sbin/zrpf-replay-init",
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
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")
