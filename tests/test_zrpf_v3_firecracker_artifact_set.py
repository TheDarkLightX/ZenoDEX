from __future__ import annotations

import os
from pathlib import Path

import pytest

from tests.test_zrpf_v3_firecracker_runtime_manifest import (
    build_manifest_document,
    parse_manifest,
)
from tools import zrpf_v3_firecracker_artifact_set as artifact_set


def test_exact_artifact_inventory_binds_bytes_without_paths(tmp_path: Path) -> None:
    kernel = b"kernel-bytes"
    rootfs = b"rootfs-bytes"
    manifest = parse_manifest(build_manifest_document(kernel, rootfs))
    _write_artifacts(tmp_path, manifest, kernel, rootfs)

    bound = artifact_set.verify_artifact_set(tmp_path, manifest)
    report = bound.to_document()

    assert bound.artifact_set_id == manifest.artifact_set_id
    assert report["status"] == "exact_local_bytes_matched_non_authoritative"
    assert all(value is False for value in report["authority"].values())
    assert tmp_path.as_posix() not in str(report)


def test_extra_and_missing_inventory_reject(tmp_path: Path) -> None:
    manifest = parse_manifest(build_manifest_document())
    _write_artifacts(tmp_path, manifest, b"test-kernel", b"test-rootfs")
    (tmp_path / "extra").write_bytes(b"x")

    with pytest.raises(artifact_set.ArtifactSetError) as extra:
        artifact_set.verify_artifact_set(tmp_path, manifest)
    assert extra.value.code == "artifact_inventory_rejected"

    (tmp_path / "extra").unlink()
    (tmp_path / manifest.rootfs.artifact.artifact_name).unlink()
    with pytest.raises(artifact_set.ArtifactSetError) as missing:
        artifact_set.verify_artifact_set(tmp_path, manifest)
    assert missing.value.code == "artifact_inventory_rejected"


def test_symlink_fifo_and_hardlink_reject_without_following(tmp_path: Path) -> None:
    manifest = parse_manifest(build_manifest_document())
    kernel_path, rootfs_path = _write_artifacts(
        tmp_path,
        manifest,
        b"test-kernel",
        b"test-rootfs",
    )

    kernel_path.unlink()
    kernel_path.symlink_to(rootfs_path)
    with pytest.raises(artifact_set.ArtifactSetError) as symlink:
        artifact_set.verify_artifact_set(tmp_path, manifest)
    assert symlink.value.code == "artifact_input_rejected"

    kernel_path.unlink()
    os.mkfifo(kernel_path)
    with pytest.raises(artifact_set.ArtifactSetError) as fifo:
        artifact_set.verify_artifact_set(tmp_path, manifest)
    assert fifo.value.code == "artifact_input_rejected"

    kernel_path.unlink()
    kernel_path.write_bytes(b"test-kernel")
    hardlink = tmp_path.parent / "kernel-hardlink"
    os.link(kernel_path, hardlink)
    try:
        with pytest.raises(artifact_set.ArtifactSetError) as linked:
            artifact_set.verify_artifact_set(tmp_path, manifest)
        assert linked.value.code == "artifact_input_rejected"
    finally:
        hardlink.unlink()


def test_wrong_size_and_hash_reject_at_distinct_boundaries(tmp_path: Path) -> None:
    manifest = parse_manifest(build_manifest_document())
    kernel_path, rootfs_path = _write_artifacts(
        tmp_path,
        manifest,
        b"test-kernel",
        b"test-rootfs",
    )
    rootfs_path.write_bytes(b"short")
    with pytest.raises(artifact_set.ArtifactSetError) as size:
        artifact_set.verify_artifact_set(tmp_path, manifest)
    assert size.value.code == "artifact_size_mismatch"

    rootfs_path.write_bytes(b"wrong-bytes")
    assert len(b"wrong-bytes") == len(b"test-rootfs")
    with pytest.raises(artifact_set.ArtifactSetError) as digest:
        artifact_set.verify_artifact_set(tmp_path, manifest)
    assert digest.value.code == "artifact_sha256_mismatch"
    assert kernel_path.exists()


def test_growth_during_streaming_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    kernel = b"k" * 64
    rootfs = b"r" * (2 * 1024 * 1024)
    manifest = parse_manifest(build_manifest_document(kernel, rootfs))
    _, rootfs_path = _write_artifacts(tmp_path, manifest, kernel, rootfs)
    original_read = artifact_set.os.read
    mutated = False

    def read_then_mutate(descriptor: int, count: int) -> bytes:
        nonlocal mutated
        chunk = original_read(descriptor, count)
        if not mutated and os.fstat(descriptor).st_size == len(rootfs):
            mutated = True
            with rootfs_path.open("ab") as output:
                output.write(b"x")
        return chunk

    monkeypatch.setattr(artifact_set.os, "read", read_then_mutate)
    with pytest.raises(artifact_set.ArtifactSetError) as changed:
        artifact_set.verify_artifact_set(tmp_path, manifest)
    assert changed.value.code == "artifact_changed_while_reading"


def _write_artifacts(
    root: Path,
    manifest,
    kernel: bytes,
    rootfs: bytes,
) -> tuple[Path, Path]:
    kernel_path = root / manifest.guest_kernel.artifact.artifact_name
    rootfs_path = root / manifest.rootfs.artifact.artifact_name
    input_path = root / manifest.input_image.artifact.artifact_name
    kernel_path.write_bytes(kernel)
    input_path.write_bytes(b"input-image")
    rootfs_path.write_bytes(rootfs)
    return kernel_path, rootfs_path
