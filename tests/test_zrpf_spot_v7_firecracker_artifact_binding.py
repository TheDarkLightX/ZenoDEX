"""Adversarial tests for descriptor-bound Spot V7 runtime artifacts."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import pickle
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools import zrpf_spot_v7_firecracker_artifact_binding as artifact_binding
from tools import zrpf_spot_v7_firecracker_runtime_manifest as runtime_manifest
from tools import zrpf_spot_v7_firecracker_runtime_protocol as runtime_protocol


@dataclass(frozen=True, slots=True)
class _Fixture:
    config: bytes
    manifest: bytes
    sources: tuple[artifact_binding.SpotV7RuntimeArtifactSourceV1, ...]
    paths: dict[str, Path]
    trusted_root: Path
    trusted_uid: int


def test_all_manifest_artifacts_are_opened_hashed_and_retained(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)

    with artifact_binding.open_descriptor_bound_spot_v7_runtime_binding_v1(
        exact_machine_config_bytes=fixture.config,
        exact_runtime_manifest_bytes=fixture.manifest,
        artifact_sources=fixture.sources,
        runtime_profile_sha256=(
            runtime_protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
        ),
        trusted_source_root=fixture.trusted_root,
        trusted_uid=fixture.trusted_uid,
    ) as bound:
        assert bound.artifact_roles == runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1
        assert bound.artifact_bytes_verified is True
        assert bound.descriptor_identity_verified is True
        assert bound.governance_admission_verified is False
        assert bound.governed_runtime_manifest_verified is False
        assert bound.live_firecracker_execution_verified is False
        assert bound.release_authority is False
        assert bound.settlement_authority is False
        assert bound.production_authority is False
        assert bound.witness_privacy is False
        assert bound.zero_knowledge_privacy is False
        bound.reverify_artifacts()


def test_artifact_content_substitution_rejects_exact_digest(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["kernel"]
    target.chmod(0o600)
    target.write_bytes(b"substituted-kernel")
    target.chmod(0o400)

    _expect_reject(fixture, "runtime_artifact_size_mismatch")


def test_artifact_same_size_substitution_rejects_exact_digest(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["kernel"]
    original = target.read_bytes()
    target.chmod(0o600)
    target.write_bytes(bytes([original[0] ^ 1]) + original[1:])
    target.chmod(0o400)

    _expect_reject(fixture, "runtime_artifact_digest_mismatch")


def test_artifact_symlink_rejects_without_following(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["rootfs"]
    replacement = target.with_name("replacement-rootfs")
    replacement.write_bytes(target.read_bytes())
    replacement.chmod(0o400)
    target.unlink()
    target.symlink_to(replacement)

    _expect_reject(fixture, "runtime_artifact_source_open")


def test_artifact_under_symlinked_parent_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    real_parent = fixture.trusted_root / "real-parent"
    real_parent.mkdir(mode=0o700)
    target = real_parent / "kernel"
    target.write_bytes(fixture.paths["kernel"].read_bytes())
    target.chmod(0o400)
    alias = fixture.trusted_root / "parent-alias"
    alias.symlink_to(real_parent, target_is_directory=True)
    sources = list(fixture.sources)
    kernel_index = runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1.index("kernel")
    sources[kernel_index] = (
        artifact_binding.SpotV7RuntimeArtifactSourceV1.validated(
            role="kernel",
            source_path=alias / "kernel",
        )
    )

    _expect_reject(
        fixture,
        "runtime_artifact_source_open",
        sources=tuple(sources),
    )


def test_special_file_artifact_rejects_without_reading(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["input"]
    target.unlink()
    os.mkfifo(target, mode=0o400)

    _expect_reject(fixture, "runtime_artifact_source_open")


def test_owner_writable_artifact_rejects_before_binding(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    fixture.paths["guest_init"].chmod(0o600)

    _expect_reject(fixture, "runtime_artifact_source_writable")


def test_artifact_truncation_rejects_before_binding(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["input"]
    target.chmod(0o600)
    with target.open("r+b") as stream:
        stream.truncate(max(1, target.stat().st_size - 1))
    target.chmod(0o400)

    _expect_reject(fixture, "runtime_artifact_size_mismatch")


def test_artifact_mutation_during_bounded_read_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["firecracker"]
    original_hash = artifact_binding._hash_opened_artifact
    mutated = False

    def mutate_after_hash(descriptor: int, expected_size: int) -> str:
        nonlocal mutated
        digest = original_hash(descriptor, expected_size)
        if not mutated:
            raw = target.read_bytes()
            target.chmod(0o600)
            target.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
            target.chmod(0o400)
            mutated = True
        return digest

    monkeypatch.setattr(
        artifact_binding,
        "_hash_opened_artifact",
        mutate_after_hash,
    )

    _expect_reject(fixture, "runtime_artifact_changed_while_reading")


def test_partial_inventory_failure_closes_every_opened_descriptor(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["kernel"]
    raw = target.read_bytes()
    target.chmod(0o600)
    target.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
    target.chmod(0o400)
    original_open = artifact_binding.staging_io.open_trusted_source
    opened: list[int] = []

    def capture_opened_descriptor(
        path: Path,
        *,
        trusted_root: Path,
        trusted_uid: int,
    ) -> int:
        descriptor = original_open(
            path,
            trusted_root=trusted_root,
            trusted_uid=trusted_uid,
        )
        opened.append(descriptor)
        return descriptor

    monkeypatch.setattr(
        artifact_binding.staging_io,
        "open_trusted_source",
        capture_opened_descriptor,
    )

    _expect_reject(fixture, "runtime_artifact_digest_mismatch")
    assert opened
    for descriptor in opened:
        with pytest.raises(OSError):
            os.fstat(descriptor)


def test_descriptor_hash_io_failure_is_typed_and_closes_descriptor(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    opened: list[int] = []
    original_open = artifact_binding.staging_io.open_trusted_source

    def capture_opened_descriptor(
        path: Path,
        *,
        trusted_root: Path,
        trusted_uid: int,
    ) -> int:
        descriptor = original_open(
            path,
            trusted_root=trusted_root,
            trusted_uid=trusted_uid,
        )
        opened.append(descriptor)
        return descriptor

    def fail_hash(_descriptor: int, _expected_size: int) -> str:
        raise OSError("injected descriptor read failure")

    monkeypatch.setattr(
        artifact_binding.staging_io,
        "open_trusted_source",
        capture_opened_descriptor,
    )
    monkeypatch.setattr(artifact_binding.staging_io, "sha256_fd", fail_hash)

    _expect_reject(fixture, "runtime_artifact_changed_while_reading")
    assert len(opened) == 1
    with pytest.raises(OSError):
        os.fstat(opened[0])


def test_trusted_source_post_open_fstat_failure_closes_descriptor(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    source = fixture.paths["firecracker"]
    captured: list[int] = []
    original_open = artifact_binding.staging_io.os.open
    original_fstat = artifact_binding.staging_io.os.fstat

    def capture_target_open(
        path: str | bytes,
        flags: int,
        mode: int = 0o777,
        *,
        dir_fd: int | None = None,
    ) -> int:
        descriptor = original_open(path, flags, mode, dir_fd=dir_fd)
        if path == source.name:
            captured.append(descriptor)
        return descriptor

    def fail_target_fstat(descriptor: int) -> os.stat_result:
        if descriptor in captured:
            raise OSError("injected post-open fstat failure")
        return original_fstat(descriptor)

    monkeypatch.setattr(artifact_binding.staging_io.os, "open", capture_target_open)
    monkeypatch.setattr(artifact_binding.staging_io.os, "fstat", fail_target_fstat)

    with pytest.raises(artifact_binding.JailerLauncherReject) as rejection:
        artifact_binding.staging_io.open_trusted_source(
            source,
            trusted_root=fixture.trusted_root,
            trusted_uid=fixture.trusted_uid,
        )
    assert str(rejection.value) == "jail_stage_source_open_failed"
    assert len(captured) == 1
    with pytest.raises(OSError):
        original_fstat(captured[0])


def test_extra_artifact_rejects_closed_inventory(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)

    _expect_reject(
        fixture,
        "runtime_artifact_inventory",
        sources=fixture.sources + (fixture.sources[0],),
    )


def test_duplicate_role_rejects_before_open(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    duplicate = list(fixture.sources)
    duplicate[1] = artifact_binding.SpotV7RuntimeArtifactSourceV1.validated(
        role=duplicate[0].role,
        source_path=duplicate[1].source_path,
    )

    _expect_reject(
        fixture,
        "runtime_artifact_duplicate_role",
        sources=tuple(duplicate),
    )


def test_duplicate_path_rejects_before_open(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    duplicate = list(fixture.sources)
    duplicate[1] = artifact_binding.SpotV7RuntimeArtifactSourceV1.validated(
        role=duplicate[1].role,
        source_path=duplicate[0].source_path,
    )

    _expect_reject(
        fixture,
        "runtime_artifact_duplicate_path",
        sources=tuple(duplicate),
    )


def test_role_path_name_mismatch_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    wrong = list(fixture.sources)
    wrong_path = fixture.trusted_root / "wrong-kernel-name"
    wrong_path.write_bytes(fixture.paths["kernel"].read_bytes())
    wrong_path.chmod(0o400)
    kernel_index = runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1.index("kernel")
    wrong[kernel_index] = artifact_binding.SpotV7RuntimeArtifactSourceV1.validated(
        role="kernel",
        source_path=wrong_path,
    )

    _expect_reject(
        fixture,
        "runtime_artifact_path",
        sources=tuple(wrong),
    )


def test_post_open_path_replacement_cannot_substitute_retained_descriptor(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    bound = artifact_binding.open_descriptor_bound_spot_v7_runtime_binding_v1(
        exact_machine_config_bytes=fixture.config,
        exact_runtime_manifest_bytes=fixture.manifest,
        artifact_sources=fixture.sources,
        runtime_profile_sha256=(
            runtime_protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
        ),
        trusted_source_root=fixture.trusted_root,
        trusted_uid=fixture.trusted_uid,
    )
    try:
        target = fixture.paths["jailer"]
        exact = target.read_bytes()
        target.unlink()
        target.write_bytes(exact)
        target.chmod(0o400)

        with pytest.raises(
            artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
        ) as captured:
            bound.reverify_artifacts()
        assert captured.value.code == "runtime_artifact_path_replaced"
    finally:
        bound.close()


def test_path_replacement_immediately_after_open_rejects_binding(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    target = fixture.paths["firecracker"]
    original_open = artifact_binding.staging_io.open_trusted_source
    replaced = False

    def open_then_replace(
        path: Path,
        *,
        trusted_root: Path,
        trusted_uid: int,
    ) -> int:
        nonlocal replaced
        descriptor = original_open(
            path,
            trusted_root=trusted_root,
            trusted_uid=trusted_uid,
        )
        if path == target and not replaced:
            exact = path.read_bytes()
            path.unlink()
            path.write_bytes(exact)
            path.chmod(0o400)
            replaced = True
        return descriptor

    monkeypatch.setattr(
        artifact_binding.staging_io,
        "open_trusted_source",
        open_then_replace,
    )

    _expect_reject(fixture, "runtime_artifact_path_replaced")


def test_bool_uid_alias_rejects_before_open(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)

    _expect_reject(
        fixture,
        "runtime_artifact_trusted_uid",
        trusted_uid=True,
    )


def test_overlong_artifact_path_rejects_before_filesystem_access() -> None:
    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as rejection:
        artifact_binding.SpotV7RuntimeArtifactSourceV1.validated(
            role="kernel",
            source_path=Path("/") / ("x" * 4_097),
        )
    assert rejection.value.code == "runtime_artifact_path"


def test_descriptor_bound_result_is_sealed_noncopyable_and_nonserializable(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    bound = artifact_binding.open_descriptor_bound_spot_v7_runtime_binding_v1(
        exact_machine_config_bytes=fixture.config,
        exact_runtime_manifest_bytes=fixture.manifest,
        artifact_sources=fixture.sources,
        runtime_profile_sha256=(
            runtime_protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
        ),
        trusted_source_root=fixture.trusted_root,
        trusted_uid=fixture.trusted_uid,
    )
    try:
        with pytest.raises(TypeError, match="cannot be copied"):
            copy.copy(bound)
        with pytest.raises(TypeError, match="cannot be deep-copied"):
            copy.deepcopy(bound)
        with pytest.raises(TypeError, match="cannot be serialized"):
            pickle.dumps(bound)
    finally:
        bound.close()

    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as captured:
        bound.reverify_artifacts()
    assert captured.value.code == "runtime_artifact_binding_closed"
    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as captured:
        _ = bound.artifact_bytes_verified
    assert captured.value.code == "runtime_artifact_binding_closed"
    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as captured:
        _ = bound.exact_runtime_manifest_bytes
    assert captured.value.code == "runtime_artifact_binding_closed"


def test_descriptor_capabilities_require_module_private_seals() -> None:
    with pytest.raises(TypeError, match="module-private seal"):
        artifact_binding._OpenedSpotV7RuntimeArtifactSetV1(
            records=(),
            seal=object(),  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="module-private seal"):
        artifact_binding._DescriptorBoundSpotV7FirecrackerRuntimeBindingV1(
            proposal=object(),  # type: ignore[arg-type]
            artifacts=object(),  # type: ignore[arg-type]
            seal=object(),  # type: ignore[arg-type]
        )


def test_forged_source_shape_rejects_at_consuming_boundary(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    forged = object.__new__(artifact_binding.SpotV7RuntimeArtifactSourceV1)
    object.__setattr__(forged, "role", True)
    object.__setattr__(forged, "source_path", fixture.sources[0].source_path)
    sources = list(fixture.sources)
    sources[0] = forged

    _expect_reject(
        fixture,
        "runtime_artifact_role",
        sources=tuple(sources),
    )


def _expect_reject(
    fixture: _Fixture,
    code: str,
    *,
    sources: tuple[artifact_binding.SpotV7RuntimeArtifactSourceV1, ...] | None = None,
    trusted_uid: int | bool | None = None,
) -> None:
    with pytest.raises(
        artifact_binding.SpotV7RuntimeArtifactBindingRejectV1
    ) as captured:
        artifact_binding.open_descriptor_bound_spot_v7_runtime_binding_v1(
            exact_machine_config_bytes=fixture.config,
            exact_runtime_manifest_bytes=fixture.manifest,
            artifact_sources=fixture.sources if sources is None else sources,
            runtime_profile_sha256=(
                runtime_protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
            ),
            trusted_source_root=fixture.trusted_root,
            trusted_uid=(
                fixture.trusted_uid if trusted_uid is None else trusted_uid
            ),
        )
    assert captured.value.code == code


def _fixture(tmp_path: Path) -> _Fixture:
    trusted_root = tmp_path / "artifacts"
    trusted_root.mkdir(mode=0o700)
    identities: list[runtime_manifest.SpotV7RuntimeArtifactIdentityV1] = []
    sources: list[artifact_binding.SpotV7RuntimeArtifactSourceV1] = []
    paths: dict[str, Path] = {}
    for index, role in enumerate(
        runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1,
        start=1,
    ):
        artifact_name = runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1[role]
        raw = (f"governed-{role}-" * (index + 1)).encode("ascii")
        path = trusted_root / artifact_name
        path.write_bytes(raw)
        path.chmod(0o400)
        identities.append(
            runtime_manifest.SpotV7RuntimeArtifactIdentityV1.validated(
                role=role,
                artifact_name=artifact_name,
                sha256=hashlib.sha256(raw).digest(),
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
    return _Fixture(
        config=config,
        manifest=manifest,
        sources=tuple(sources),
        paths=paths,
        trusted_root=trusted_root,
        trusted_uid=os.getuid(),
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
