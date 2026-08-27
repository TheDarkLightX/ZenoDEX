#!/usr/bin/env python3
"""Build the source-pinned, research-only M6 command-to-lane registry."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Final, NoReturn, cast

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.core.m6_command_lane_registry_v1 import (  # noqa: E402
    ACTIVE_PLAN_COMMIT_V1,
    ACTIVE_PLAN_REGISTRY_PATH_V1,
    ACTIVE_PLAN_REGISTRY_SHA256_V1,
    ADMISSION_RECEIPT_ARTIFACT_SHA256_V1,
    ADMISSION_RECEIPT_PATH_V1,
    CAPABILITY_MANIFEST_SHA256_V1,
    REQUIREMENTS_ARTIFACT_SHA256_V1,
    REQUIREMENTS_REGISTRY_ROOT_V1,
    SAFE_MOUNT_SOURCE_COMMIT_V1,
    SAFE_MOUNT_SOURCE_PATH_V1,
    CommandLaneRegistryRejectV1,
    CommandLaneSourceSnapshotV1,
    build_registry_artifact_v1,
)
from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _atomic_replace_regular_file_v1,
    _git_head_v1,
    _git_is_ancestor_v1,
    _git_tree_entry_v1,
    _git_tree_v1,
    _read_bounded_regular_file_v1,
)
from tools.m6_normative_requirements_v1 import (  # noqa: E402
    canonical_json_bytes_v1,
    decode_json_object_v1,
)

JSON_OUTPUT: Final = Path("docs/research/ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json")
ACTIVE_PLAN_REGISTRY: Final = Path(ACTIVE_PLAN_REGISTRY_PATH_V1)
ADMISSION_RECEIPT: Final = Path(ADMISSION_RECEIPT_PATH_V1)
CAPABILITY_MANIFEST: Final = Path("docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json")
REQUIREMENTS_ARTIFACT: Final = Path("docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json")
MAX_INPUT_BYTES_V1: Final = 524_288


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CommandLaneRegistryRejectV1(code, path, detail)


def _sha256_v1(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git_blob_id_v1(raw: bytes) -> str:
    if type(raw) is not bytes:
        _reject("SAFE_MOUNT_SOURCE_BYTES_TYPE", SAFE_MOUNT_SOURCE_PATH_V1, "must be exact bytes")
    header = f"blob {len(raw)}\0".encode("ascii")
    # Git object identity is SHA-1 by protocol definition; this is an equality
    # check against the Git tree entry, never a security digest choice.
    return hashlib.sha1(header + raw, usedforsecurity=False).hexdigest()


def _lane_dispositions_v1(manifest: object) -> tuple[tuple[str, str], ...]:
    if type(manifest) is not dict:
        _reject("CAPABILITY_MANIFEST_ROOT_TYPE", "capability_manifest", "must be an object")
    manifest_object = cast(dict[str, object], manifest)
    lanes = manifest_object.get("lanes")
    if type(lanes) is not list:
        _reject("CAPABILITY_MANIFEST_LANES_TYPE", "capability_manifest.lanes", "must be a list")
    lane_rows = cast(list[object], lanes)
    rows: list[tuple[str, str]] = []
    for index, lane in enumerate(lane_rows):
        if type(lane) is not dict:
            _reject("CAPABILITY_MANIFEST_LANE_TYPE", f"lanes[{index}]", "must be an object")
        lane_object = cast(dict[str, object], lane)
        lane_id = lane_object.get("lane_id")
        disposition = lane_object.get("disposition")
        if type(lane_id) is not str or type(disposition) is not str:
            _reject(
                "CAPABILITY_MANIFEST_LANE_FIELD_TYPE",
                f"lanes[{index}]",
                "lane fields must be strings",
            )
        rows.append((lane_id, disposition))
    return tuple(rows)


def _route_ids_v1(manifest: object) -> tuple[str, ...]:
    if type(manifest) is not dict:
        _reject("CAPABILITY_MANIFEST_ROOT_TYPE", "capability_manifest", "must be an object")
    routes = cast(dict[str, object], manifest).get("required_cross_lane_routes")
    if type(routes) is not list or any(type(route) is not str for route in routes):
        _reject(
            "CAPABILITY_MANIFEST_ROUTES_TYPE", "required_cross_lane_routes", "must be a string list"
        )
    return tuple(cast(list[str], routes))


def _requirements_root_v1(requirements: object) -> str:
    if type(requirements) is not dict:
        _reject("REQUIREMENTS_ARTIFACT_ROOT_TYPE", "requirements", "must be an object")
    requirements_object = cast(dict[str, object], requirements)
    root = requirements_object.get("registry_root")
    if type(root) is not str:
        _reject("REQUIREMENTS_ROOT_TYPE", "requirements.registry_root", "must be a string")
    return root


def _load_safe_mount_binding_v1(root: Path, captured_head: str) -> tuple[str, str]:
    if not _git_is_ancestor_v1(root, SAFE_MOUNT_SOURCE_COMMIT_V1, captured_head):
        _reject("SAFE_MOUNT_ANCESTRY", "HEAD", "safe-mount source commit is not on current lineage")
    source_tree = _git_tree_v1(root, SAFE_MOUNT_SOURCE_COMMIT_V1)
    source_path, source_mode, source_type, source_blob = _git_tree_entry_v1(
        root, SAFE_MOUNT_SOURCE_COMMIT_V1, SAFE_MOUNT_SOURCE_PATH_V1
    )
    current_path, current_mode, current_type, current_blob = _git_tree_entry_v1(
        root, captured_head, SAFE_MOUNT_SOURCE_PATH_V1
    )
    if (
        source_path != SAFE_MOUNT_SOURCE_PATH_V1
        or source_mode != "100644"
        or source_type != "blob"
        or current_path != source_path
        or current_mode != source_mode
        or current_type != source_type
        or current_blob != source_blob
    ):
        _reject(
            "SAFE_MOUNT_SOURCE_BLOB_DRIFT", SAFE_MOUNT_SOURCE_PATH_V1, "committed source blob drift"
        )
    current_safe_mount_raw = _read_bounded_regular_file_v1(
        root / SAFE_MOUNT_SOURCE_PATH_V1,
        MAX_INPUT_BYTES_V1,
        "safe-mount source",
    )
    if _git_blob_id_v1(current_safe_mount_raw) != source_blob:
        _reject(
            "SAFE_MOUNT_WORKTREE_BLOB_DRIFT",
            SAFE_MOUNT_SOURCE_PATH_V1,
            "working-tree source differs from the pinned committed blob",
        )
    return source_tree, source_blob


def _load_registry_sources_v1(
    root: Path,
) -> tuple[str, str, str, str, str, tuple[tuple[str, str], ...], tuple[str, ...]]:
    active_plan_raw = _read_bounded_regular_file_v1(
        root / ACTIVE_PLAN_REGISTRY, MAX_INPUT_BYTES_V1, "active plan registry"
    )
    admission_raw = _read_bounded_regular_file_v1(
        root / ADMISSION_RECEIPT, MAX_INPUT_BYTES_V1, "plan admission receipt"
    )
    capability_raw = _read_bounded_regular_file_v1(
        root / CAPABILITY_MANIFEST, MAX_INPUT_BYTES_V1, "capability manifest"
    )
    requirements_raw = _read_bounded_regular_file_v1(
        root / REQUIREMENTS_ARTIFACT, MAX_INPUT_BYTES_V1, "requirements artifact"
    )
    if _sha256_v1(active_plan_raw) != ACTIVE_PLAN_REGISTRY_SHA256_V1:
        _reject("ACTIVE_PLAN_REGISTRY_SHA_DRIFT", str(ACTIVE_PLAN_REGISTRY), "source hash mismatch")
    if _sha256_v1(admission_raw) != ADMISSION_RECEIPT_ARTIFACT_SHA256_V1:
        _reject("ADMISSION_RECEIPT_SHA_DRIFT", str(ADMISSION_RECEIPT), "source hash mismatch")
    if _sha256_v1(capability_raw) != CAPABILITY_MANIFEST_SHA256_V1:
        _reject("CAPABILITY_MANIFEST_SHA_DRIFT", str(CAPABILITY_MANIFEST), "source hash mismatch")
    if _sha256_v1(requirements_raw) != REQUIREMENTS_ARTIFACT_SHA256_V1:
        _reject(
            "REQUIREMENTS_ARTIFACT_SHA_DRIFT", str(REQUIREMENTS_ARTIFACT), "source hash mismatch"
        )
    capability_manifest = decode_json_object_v1(capability_raw, "capability manifest")
    requirements = decode_json_object_v1(requirements_raw, "requirements artifact")
    requirements_root = _requirements_root_v1(requirements)
    if requirements_root != REQUIREMENTS_REGISTRY_ROOT_V1:
        _reject("REQUIREMENTS_ROOT_DRIFT", "requirements.registry_root", "source root mismatch")
    return (
        _sha256_v1(active_plan_raw),
        _sha256_v1(admission_raw),
        _sha256_v1(capability_raw),
        _sha256_v1(requirements_raw),
        requirements_root,
        _lane_dispositions_v1(capability_manifest),
        _route_ids_v1(capability_manifest),
    )


def load_source_snapshot_v1(root: Path) -> CommandLaneSourceSnapshotV1:
    """Acquire bounded files and Git bindings before invoking the pure core."""

    captured_head = _git_head_v1(root)
    if not _git_is_ancestor_v1(root, ACTIVE_PLAN_COMMIT_V1, captured_head):
        _reject("ACTIVE_PLAN_ANCESTRY", "HEAD", "admitted Plan V2.1 is not on current lineage")
    source_tree, source_blob = _load_safe_mount_binding_v1(root, captured_head)
    (
        active_plan_sha,
        admission_sha,
        capability_sha,
        requirements_sha,
        requirements_root,
        dispositions,
        route_ids,
    ) = _load_registry_sources_v1(root)
    rechecked_head = _git_head_v1(root)
    return CommandLaneSourceSnapshotV1(
        captured_head=captured_head,
        rechecked_head=rechecked_head,
        safe_mount_source_tree=source_tree,
        safe_mount_source_blob=source_blob,
        active_plan_registry_sha256=active_plan_sha,
        admission_receipt_artifact_sha256=admission_sha,
        capability_manifest_sha256=capability_sha,
        requirements_artifact_sha256=requirements_sha,
        requirements_registry_root=requirements_root,
        lane_dispositions=dispositions,
        route_ids=route_ids,
    )


def build_registry_bytes_v1(root: Path) -> bytes:
    snapshot = load_source_snapshot_v1(root)
    if snapshot.captured_head != snapshot.rechecked_head:
        _reject("HEAD_CHANGED_DURING_CAPTURE", "HEAD", "Git HEAD changed during source capture")
    return canonical_json_bytes_v1(build_registry_artifact_v1(snapshot))


def write_registry_v1(root: Path) -> dict[str, str]:
    data = build_registry_bytes_v1(root)
    _atomic_replace_regular_file_v1(root / JSON_OUTPUT, data)
    return {"json_path": str(JSON_OUTPUT), "json_sha256": _sha256_v1(data)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        data = build_registry_bytes_v1(args.root)
        target = args.root / JSON_OUTPUT
        if args.check:
            actual = _read_bounded_regular_file_v1(target, MAX_INPUT_BYTES_V1, "registry artifact")
            if actual != data:
                print(
                    json.dumps({"ok": False, "finding": "REGISTRY_ARTIFACT_DRIFT"}, sort_keys=True)
                )
                return 1
            print(json.dumps({"ok": True, "json_sha256": _sha256_v1(data)}, sort_keys=True))
            return 0
        _atomic_replace_regular_file_v1(target, data)
        print(json.dumps({"ok": True, "json_sha256": _sha256_v1(data)}, sort_keys=True))
        return 0
    except (CommandLaneRegistryRejectV1, ShellRejectV1, ValueError, TypeError) as exc:
        code = (
            exc.code
            if isinstance(exc, (CommandLaneRegistryRejectV1, ShellRejectV1))
            else type(exc).__name__
        )
        print(json.dumps({"ok": False, "finding": code}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
