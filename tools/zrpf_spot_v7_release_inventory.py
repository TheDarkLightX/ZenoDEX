"""Committed source inventory for the recursively reached Spot V7 workspaces."""

from __future__ import annotations

import hashlib
import heapq
import posixpath
import re
from collections import deque
from pathlib import Path, PurePosixPath
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as v6_planner
from tools.zrpf_spot_v7_release_ancestry import commit_file, require_repo_relative
from tools.zrpf_spot_v7_release_cargo import discover_cargo_closure
from tools.zrpf_spot_v7_release_schema import (
    V7_WORKSPACE_MANIFEST,
    ReleaseClosureError,
    canonical_bytes,
)

_LITERAL_INCLUDE = re.compile(
    rb"\b(include|include_str|include_bytes)!\s*\(\s*\"([^\"\r\n]+)\"\s*\)",
    re.MULTILINE,
)
_PATH_ATTRIBUTE = re.compile(rb"#\s*\[\s*path\s*=\s*\"([^\"\r\n]+)\"\s*\]")
_PATH_ATTRIBUTE_START = re.compile(rb"#\s*\[\s*path\s*=")
_INCLUDE_START = re.compile(rb"\binclude(?:_str|_bytes)?!\s*\(")
_GENERATED_OUT_DIR_INCLUDE = re.compile(
    rb"\binclude(?:_bytes)?!\s*\(\s*concat!\s*\(\s*env!\s*\(\s*"
    rb"(?:\\?\"OUT_DIR\\?\")\s*\)",
    re.MULTILINE,
)

MAX_LITERAL_COMPILER_INPUTS = 4_096
MAX_LITERAL_COMPILER_SOURCES = 4_096
MAX_LITERAL_COMPILER_INPUT_EDGES = 16_384


def build_source_closure(root: Path, commit: str) -> dict[str, Any]:
    """Bind reached workspaces and literal compiler-visible external files."""

    packages, edges, workspace_roots = discover_cargo_closure(root, commit)
    base_files = v6_planner._tracked_files_for_roots(
        root,
        commit,
        tuple(sorted(workspace_roots)),
    )
    base_paths = {row[0] for row in base_files}
    supplemental, generated, compiler_input_edges = _literal_compiler_inputs(
        root,
        commit,
        base_files,
        base_paths,
    )
    cargo_configs = _ancestor_cargo_config_paths(root, commit, workspace_roots)
    supplemental = sorted(set(supplemental).union(set(cargo_configs) - base_paths))
    if len(supplemental) > MAX_LITERAL_COMPILER_INPUTS:
        raise ReleaseClosureError("supplemental compiler-input set exceeds its bound")
    supplemental_rows = _inventory_explicit_paths(root, commit, supplemental)
    all_files = sorted(base_files + supplemental_rows)
    if len(all_files) != len({row[0] for row in all_files}):
        raise ReleaseClosureError("source closure contains duplicate file paths")
    entries = [
        {"path": path, "git_mode": mode, "bytes": size, "sha256": sha256}
        for path, mode, size, sha256 in all_files
    ]
    lockfiles = _lockfile_rows(workspace_roots, entries)
    config_rows = _selected_file_rows(cargo_configs, entries, "Cargo config")
    return {
        "root_workspace_manifest": V7_WORKSPACE_MANIFEST,
        "workspace_roots": sorted(workspace_roots),
        "package_manifests": packages,
        "local_path_dependency_edges": edges,
        "lockfiles": lockfiles,
        "lockfile_set_root_sha256": _rows_root(
            b"zenodex.zrpf.spot_v7.lockfile_set.v1\0",
            lockfiles,
        ),
        "ancestor_cargo_configs": config_rows,
        "supplemental_compiler_inputs": supplemental,
        "literal_compiler_input_edges": compiler_input_edges,
        "generated_out_dir_include_sources": generated,
        "files": entries,
        "tracked_file_count": len(entries),
        "tracked_bytes": sum(row["bytes"] for row in entries),
        "inventory_root_sha256": _file_inventory_root(entries),
        "all_recursive_local_path_dependencies_inventoried": True,
        "all_reached_workspace_lockfiles_bound": True,
        "all_tracked_files_under_reached_workspaces_included": True,
        "literal_external_compiler_inputs_included": True,
        "literal_compiler_inputs_reached_fixed_point": True,
        "literal_compiler_source_graph_acyclic": True,
        "tracked_ancestor_cargo_configs_included": True,
        "complete_build_input_closure_verified": False,
    }


def _literal_compiler_inputs(
    root: Path,
    commit: str,
    base_files: list[tuple[str, str, int, str]],
    base_paths: set[str],
) -> tuple[list[str], list[str], list[dict[str, Any]]]:
    supplemental: set[str] = set()
    generated: set[str] = set()
    pending = deque(
        sorted(path for path, _mode, _size, _sha256 in base_files if path.endswith(".rs"))
    )
    queued = set(pending)
    scanned: set[str] = set()
    source_graph: dict[str, set[str]] = {}
    edge_keys: set[tuple[str, str, str, bool]] = set()
    observed_edge_count = 0
    while pending:
        path = pending.popleft()
        if path in scanned:
            continue
        if len(scanned) >= MAX_LITERAL_COMPILER_SOURCES:
            raise ReleaseClosureError("literal Rust compiler-source graph exceeds its bound")
        raw = commit_file(root, commit, path)
        source_graph.setdefault(path, set())
        for kind, target, is_compiler_source in _literal_input_edges(path, raw):
            observed_edge_count += 1
            if observed_edge_count > MAX_LITERAL_COMPILER_INPUT_EDGES:
                raise ReleaseClosureError("literal compiler-input edge graph exceeds its bound")
            external = target not in base_paths
            edge_keys.add((path, kind, target, external))
            if external:
                supplemental.add(target)
                if len(supplemental) > MAX_LITERAL_COMPILER_INPUTS:
                    raise ReleaseClosureError("supplemental compiler-input set exceeds its bound")
            if is_compiler_source:
                source_graph[path].add(target)
                source_graph.setdefault(target, set())
                if target not in queued:
                    pending.append(target)
                    queued.add(target)
        if _GENERATED_OUT_DIR_INCLUDE.search(raw):
            generated.add(path)
        scanned.add(path)
    for path in sorted(supplemental):
        commit_file(root, commit, path)
    _require_acyclic_compiler_source_graph(source_graph)
    edges = [
        {
            "source_path": source,
            "input_kind": kind,
            "target_path": target,
            "outside_reached_workspaces": external,
        }
        for source, kind, target, external in sorted(edge_keys)
    ]
    return sorted(supplemental), sorted(generated), edges


def _uncovered_literal_inputs(
    source_path: str,
    raw: bytes,
    base_paths: set[str],
) -> set[str]:
    return {
        target
        for _kind, target, _is_compiler_source in _literal_input_edges(source_path, raw)
        if target not in base_paths
    }


def _literal_input_edges(source_path: str, raw: bytes) -> list[tuple[str, str, bool]]:
    result: list[tuple[str, str, bool]] = []
    recognized_starts = {match.start() for match in _LITERAL_INCLUDE.finditer(raw)}
    recognized_starts.update(match.start() for match in _GENERATED_OUT_DIR_INCLUDE.finditer(raw))
    recognized_path_starts = {match.start() for match in _PATH_ATTRIBUTE.finditer(raw)}
    if any(match.start() not in recognized_starts for match in _INCLUDE_START.finditer(raw)):
        raise ReleaseClosureError("Rust include form is outside the governed scanner")
    if any(
        match.start() not in recognized_path_starts for match in _PATH_ATTRIBUTE_START.finditer(raw)
    ):
        raise ReleaseClosureError("Rust path attribute is outside the governed scanner")
    for match in _LITERAL_INCLUDE.finditer(raw):
        kind = match.group(1).decode("ascii")
        relative = _decode_compiler_input_path(match.group(2))
        result.append((kind, _resolve_source_relative(source_path, relative), kind == "include"))
    for match in _PATH_ATTRIBUTE.finditer(raw):
        relative = _decode_compiler_input_path(match.group(1))
        result.append(("path_attribute", _resolve_source_relative(source_path, relative), True))
    return result


def _decode_compiler_input_path(raw: bytes) -> str:
    try:
        return raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise ReleaseClosureError("Rust compiler input path is not UTF-8") from exc


def _require_acyclic_compiler_source_graph(graph: dict[str, set[str]]) -> None:
    indegree = {node: 0 for node in graph}
    for targets in graph.values():
        for target in targets:
            indegree[target] = indegree.get(target, 0) + 1
    pending = [node for node, degree in indegree.items() if degree == 0]
    heapq.heapify(pending)
    visited = 0
    while pending:
        source = heapq.heappop(pending)
        visited += 1
        for target in sorted(graph.get(source, set())):
            indegree[target] -= 1
            if indegree[target] == 0:
                heapq.heappush(pending, target)
    if visited != len(indegree):
        raise ReleaseClosureError("literal Rust compiler-source graph contains a cycle")


def _resolve_source_relative(source: str, relative: str) -> str:
    if not relative or "\x00" in relative or relative.startswith("/"):
        raise ReleaseClosureError("Rust compiler input path is noncanonical")
    normalized = posixpath.normpath(
        posixpath.join(PurePosixPath(source).parent.as_posix(), relative)
    )
    require_repo_relative(normalized, "Rust compiler input path")
    return normalized


def _inventory_explicit_paths(
    root: Path,
    commit: str,
    paths: list[str],
) -> list[tuple[str, str, int, str]]:
    if not paths:
        return []
    entries = v6_planner._tracked_files_for_roots(root, commit, tuple(paths))
    if [row[0] for row in entries] != paths:
        raise ReleaseClosureError("supplemental compiler input inventory differs")
    return entries


def _ancestor_cargo_config_paths(
    root: Path,
    commit: str,
    workspace_roots: set[str],
) -> list[str]:
    candidates: set[str] = set()
    directories: set[str] = set()
    for workspace in workspace_roots:
        current = PurePosixPath(workspace)
        for ancestor in (current, *current.parents):
            directory = ancestor.as_posix()
            if directory == ".":
                directory = ""
            directories.add(directory)
            prefix = f"{directory}/" if directory else ""
            candidates.add(f"{prefix}.cargo/config")
            candidates.add(f"{prefix}.cargo/config.toml")
    raw = v6_planner._run_git(
        root,
        ["ls-tree", "-r", "-z", commit, "--", *sorted(candidates)],
        maximum_stdout=1024 * 1024,
    ).stdout
    entries = v6_planner._parse_ls_tree(raw)
    existing = sorted(path for path, _mode, _object_id in entries)
    if any(path not in candidates for path in existing):
        raise ReleaseClosureError("Cargo config inventory contains an unexpected path")
    existing_set = set(existing)
    for directory in directories:
        prefix = f"{directory}/" if directory else ""
        pair = {f"{prefix}.cargo/config", f"{prefix}.cargo/config.toml"}
        if pair.issubset(existing_set):
            raise ReleaseClosureError("Cargo config and config.toml are both present")
    return existing


def _selected_file_rows(
    paths: list[str],
    entries: list[dict[str, Any]],
    label: str,
) -> list[dict[str, Any]]:
    by_path = {row["path"]: row for row in entries}
    result: list[dict[str, Any]] = []
    for path in paths:
        row = by_path.get(path)
        if row is None:
            raise ReleaseClosureError(f"{label} is absent from the source inventory")
        result.append(
            {
                "path": row["path"],
                "git_mode": row["git_mode"],
                "bytes": row["bytes"],
                "sha256": row["sha256"],
            }
        )
    return result


def _lockfile_rows(
    workspace_roots: set[str],
    entries: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    by_path = {row["path"]: row for row in entries}
    result: list[dict[str, Any]] = []
    for root in sorted(workspace_roots):
        path = f"{root}/Cargo.lock"
        row = by_path.get(path)
        if row is None:
            raise ReleaseClosureError("reachable Cargo workspace lockfile is missing")
        result.append(
            {
                "workspace_root": root,
                "path": path,
                "git_mode": row["git_mode"],
                "bytes": row["bytes"],
                "sha256": row["sha256"],
            }
        )
    return result


def _file_inventory_root(entries: list[dict[str, Any]]) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.zrpf.spot_v7.release_source_closure.v1\0")
    for row in entries:
        path = row["path"].encode("utf-8")
        mode = row["git_mode"].encode("ascii")
        hasher.update(len(path).to_bytes(4, "big"))
        hasher.update(path)
        hasher.update(len(mode).to_bytes(1, "big"))
        hasher.update(mode)
        hasher.update(row["bytes"].to_bytes(8, "big"))
        hasher.update(bytes.fromhex(row["sha256"]))
    return hasher.hexdigest()


def _rows_root(domain: bytes, rows: list[dict[str, Any]]) -> str:
    hasher = hashlib.sha256()
    hasher.update(domain)
    for row in rows:
        encoded = canonical_bytes(row)
        hasher.update(len(encoded).to_bytes(4, "big"))
        hasher.update(encoded)
    return hasher.hexdigest()
