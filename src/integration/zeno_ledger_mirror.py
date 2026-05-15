"""Public mirror indexes for ZenoLedger artifact bundles."""

from __future__ import annotations

import hashlib
import shutil
from pathlib import Path
from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_v0 import hash_v0, merkle_root_v0


MIRROR_INDEX_SCHEMA_V0 = "zenodex/zeno_ledger/mirror_index/v0"
MIRROR_PUBLISH_RECEIPT_SCHEMA_V0 = "zenodex/zeno_ledger/mirror_publish_receipt/v0"


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _is_relative_safe(path_text: str) -> bool:
    path = Path(path_text)
    return not path.is_absolute() and path_text != "" and ".." not in path.parts


def _relative_to_root(path: Path, root: Path) -> str:
    resolved = path.resolve()
    root_resolved = root.resolve()
    rel = resolved.relative_to(root_resolved).as_posix()
    if not _is_relative_safe(rel):
        raise ValueError(f"unsafe relative path: {rel}")
    return rel


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return "0x" + h.hexdigest()


def _json_artifact_paths(root: Path, *, exclude_paths: Sequence[Path] = ()) -> list[Path]:
    root_resolved = root.resolve()
    excludes = {path.resolve() for path in exclude_paths}
    out: list[Path] = []
    for path in root_resolved.rglob("*.json"):
        if path.resolve() in excludes:
            continue
        if path.name == "mirror_index.json":
            continue
        if path.is_file():
            out.append(path)
    return sorted(out, key=lambda p: _relative_to_root(p, root_resolved))


def _artifact_entry(path: Path, *, root: Path) -> dict[str, Any]:
    rel = _relative_to_root(path, root)
    size = path.stat().st_size
    entry = {
        "relative_path": rel,
        "byte_length": size,
        "sha256": _sha256_file(path),
    }
    return {**entry, "entry_hash": hash_v0("mirror_artifact_entry_v0", entry)}


def build_mirror_index_v0(
    *,
    mirror_root: Path,
    manifest_path: Path,
    exclude_paths: Sequence[Path] = (),
) -> dict[str, Any]:
    """Build a deterministic index over JSON artifacts under a mirror root."""

    root = mirror_root.resolve()
    manifest = manifest_path.resolve()
    if not root.is_dir():
        raise ValueError("mirror_root must be a directory")
    if not manifest.is_file():
        raise ValueError("manifest_path must be a file")
    manifest_rel = _relative_to_root(manifest, root)
    entries = [_artifact_entry(path, root=root) for path in _json_artifact_paths(root, exclude_paths=exclude_paths)]
    if manifest_rel not in {entry["relative_path"] for entry in entries}:
        raise ValueError("manifest_path must be included under mirror_root")
    entry_hashes = [str(entry["entry_hash"]) for entry in entries]
    body = {
        "schema": MIRROR_INDEX_SCHEMA_V0,
        "manifest_path": manifest_rel,
        "artifact_count": len(entries),
        "artifact_root": merkle_root_v0("mirror_artifact_entries_v0", entry_hashes),
        "artifacts": entries,
    }
    return {**body, "mirror_index_hash": hash_v0("mirror_index_v0", body)}


def validate_mirror_index_v0(*, index: Mapping[str, Any], mirror_root: Path) -> None:
    obj = _require_mapping(index, name="index")
    if obj.get("schema") != MIRROR_INDEX_SCHEMA_V0:
        raise ValueError("mirror index schema mismatch")
    manifest_rel = _require_str(obj.get("manifest_path"), name="manifest_path")
    if not _is_relative_safe(manifest_rel):
        raise ValueError("manifest_path must be relative and safe")
    artifact_count = _require_nonnegative_int(obj.get("artifact_count"), name="artifact_count")
    artifacts = obj.get("artifacts")
    if not isinstance(artifacts, list):
        raise TypeError("artifacts must be a list")
    if len(artifacts) != artifact_count:
        raise ValueError("artifact_count mismatch")

    root = mirror_root.resolve()
    rebuilt_entries = []
    seen_paths: set[str] = set()
    for index_i, raw_entry in enumerate(artifacts):
        entry = _require_mapping(raw_entry, name=f"artifacts[{index_i}]")
        rel = _require_str(entry.get("relative_path"), name=f"artifacts[{index_i}].relative_path")
        if not _is_relative_safe(rel):
            raise ValueError("artifact relative_path must be relative and safe")
        if rel in seen_paths:
            raise ValueError("duplicate artifact relative_path")
        seen_paths.add(rel)
        path = (root / rel).resolve()
        path.relative_to(root)
        if not path.is_file():
            raise ValueError(f"artifact missing: {rel}")
        rebuilt_entries.append(_artifact_entry(path, root=root))

    if manifest_rel not in seen_paths:
        raise ValueError("manifest_path is not in artifacts")
    if list(artifacts) != rebuilt_entries:
        raise ValueError("mirror artifact binding mismatch")
    entry_hashes = [str(entry["entry_hash"]) for entry in rebuilt_entries]
    body = {
        "schema": MIRROR_INDEX_SCHEMA_V0,
        "manifest_path": manifest_rel,
        "artifact_count": len(rebuilt_entries),
        "artifact_root": merkle_root_v0("mirror_artifact_entries_v0", entry_hashes),
        "artifacts": rebuilt_entries,
    }
    expected = {**body, "mirror_index_hash": hash_v0("mirror_index_v0", body)}
    if dict(obj) != expected:
        raise ValueError("mirror index binding mismatch")


def publish_mirror_from_index_v0(
    *,
    index: Mapping[str, Any],
    source_root: Path,
    index_path: Path,
    publish_root: Path,
    extra_paths: Sequence[Path] = (),
) -> dict[str, Any]:
    """Copy exactly indexed artifacts into a publish directory and verify them."""

    source = source_root.resolve()
    publish = publish_root.resolve()
    if not source.is_dir():
        raise ValueError("source_root must be a directory")
    if publish == source:
        raise ValueError("publish_root must be distinct from source_root")
    try:
        publish.relative_to(source)
    except ValueError:
        pass
    else:
        raise ValueError("publish_root must not be inside source_root")

    index_file = index_path.resolve()
    index_rel = _relative_to_root(index_file, source)
    if not index_file.is_file():
        raise ValueError("index_path must be a file under source_root")
    validate_mirror_index_v0(index=index, mirror_root=source)

    obj = _require_mapping(index, name="index")
    artifacts = obj.get("artifacts")
    if not isinstance(artifacts, list):
        raise TypeError("artifacts must be a list")

    copied_paths: list[str] = []
    publish.mkdir(parents=True, exist_ok=True)
    for raw_entry in artifacts:
        entry = _require_mapping(raw_entry, name="artifact")
        rel = _require_str(entry.get("relative_path"), name="artifact.relative_path")
        if not _is_relative_safe(rel):
            raise ValueError("artifact relative_path must be relative and safe")
        src = (source / rel).resolve()
        src.relative_to(source)
        dst = publish / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
        copied_paths.append(rel)

    index_dst = publish / index_rel
    index_dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(index_file, index_dst)

    extra_rel_paths: list[str] = []
    for extra in extra_paths:
        extra_file = extra.resolve()
        extra_rel = _relative_to_root(extra_file, source)
        if extra_rel in copied_paths or extra_rel == index_rel:
            continue
        if not extra_file.is_file():
            raise ValueError(f"extra path must be a file: {extra}")
        dst = publish / extra_rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(extra_file, dst)
        extra_rel_paths.append(extra_rel)

    validate_mirror_index_v0(index=obj, mirror_root=publish)
    body = {
        "schema": MIRROR_PUBLISH_RECEIPT_SCHEMA_V0,
        "mirror_index_hash": obj["mirror_index_hash"],
        "artifact_count": obj["artifact_count"],
        "artifact_root": obj["artifact_root"],
        "index_relative_path": index_rel,
        "copied_artifact_paths": copied_paths,
        "copied_extra_paths": sorted(extra_rel_paths),
    }
    return {**body, "publish_receipt_hash": hash_v0("mirror_publish_receipt_v0", body)}
