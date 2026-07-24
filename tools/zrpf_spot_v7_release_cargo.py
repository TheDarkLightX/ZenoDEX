"""Recursive local Cargo dependency discovery for the Spot V7 release lane."""

from __future__ import annotations

import posixpath
import tomllib
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as v6_planner
from tools.zrpf_spot_v7_release_ancestry import commit_file, require_repo_relative
from tools.zrpf_spot_v7_release_schema import (
    V7_WORKSPACE_MANIFEST,
    ReleaseClosureError,
)

MAX_MANIFEST_BYTES = 1024 * 1024
MAX_GIT_PATH_OUTPUT_BYTES = 8 * 1024 * 1024
MAX_PACKAGE_COUNT = 512
MAX_WORKSPACE_COUNT = 64
MAX_DEPENDENCY_EDGES = 4_096


@dataclass
class _CargoContext:
    root: Path
    commit: str
    manifest_paths: set[str]
    cache: dict[str, dict[str, Any]]


def discover_cargo_closure(
    root: Path,
    commit: str,
) -> tuple[list[dict[str, Any]], list[dict[str, str]], set[str]]:
    """Return reached packages, path edges, and workspace lock roots."""

    manifest_paths = _all_manifest_paths(root, commit)
    if V7_WORKSPACE_MANIFEST not in manifest_paths:
        raise ReleaseClosureError("V7 workspace manifest is absent at G")
    root_doc = _manifest(root, commit, V7_WORKSPACE_MANIFEST)
    pending = _workspace_member_manifests(V7_WORKSPACE_MANIFEST, root_doc)
    if "package" in root_doc:
        pending.append(V7_WORKSPACE_MANIFEST)
    seen: set[str] = set()
    rows: list[dict[str, Any]] = []
    edges: list[dict[str, str]] = []
    workspace_roots: set[str] = set()
    override_roots: set[str] = set()
    context = _CargoContext(
        root=root,
        commit=commit,
        manifest_paths=manifest_paths,
        cache={V7_WORKSPACE_MANIFEST: root_doc},
    )

    while pending:
        manifest_path = pending.pop(0)
        if manifest_path in seen:
            continue
        row, discovered_edges, workspace_root = _package_closure_rows(
            context,
            manifest_path,
            override_roots,
        )
        workspace_roots.add(workspace_root)
        rows.append(row)
        edges.extend(discovered_edges)
        pending.extend(
            edge["to_manifest"] for edge in discovered_edges if edge["to_manifest"] not in seen
        )
        seen.add(manifest_path)
        if len(seen) > MAX_PACKAGE_COUNT or len(edges) > MAX_DEPENDENCY_EDGES:
            raise ReleaseClosureError("Cargo local dependency graph exceeds its bound")

    if not workspace_roots or len(workspace_roots) > MAX_WORKSPACE_COUNT:
        raise ReleaseClosureError("reachable Cargo workspace count is outside policy")
    return (
        sorted(rows, key=lambda row: row["manifest_path"]),
        sorted(edges, key=_edge_key),
        workspace_roots,
    )


def _package_closure_rows(
    context: _CargoContext,
    manifest_path: str,
    override_roots: set[str],
) -> tuple[dict[str, Any], list[dict[str, str]], str]:
    document = _require_package_manifest(context, manifest_path)
    workspace_root = _nearest_workspace_root(context, manifest_path)
    edges = _dependency_rows(
        context,
        manifest_path,
        document,
        workspace_root,
    )
    if workspace_root not in override_roots:
        edges.extend(_local_override_rows(context, workspace_root))
        override_roots.add(workspace_root)
    row = {
        "manifest_path": manifest_path,
        "package_name": document["package"]["name"],
        "workspace_root": workspace_root,
    }
    return row, edges, workspace_root


def _require_package_manifest(
    context: _CargoContext,
    path: str,
) -> dict[str, Any]:
    if path not in context.manifest_paths:
        raise ReleaseClosureError("reachable Cargo package manifest is untracked")
    document = context.cache.setdefault(
        path,
        _manifest(context.root, context.commit, path),
    )
    package = document.get("package")
    if type(package) is not dict or type(package.get("name")) is not str:
        raise ReleaseClosureError("reachable Cargo manifest lacks one package name")
    return document


def _dependency_rows(
    context: _CargoContext,
    manifest_path: str,
    document: dict[str, Any],
    workspace_root: str,
) -> list[dict[str, str]]:
    workspace_manifest = f"{workspace_root}/Cargo.toml"
    workspace_doc = context.cache.setdefault(
        workspace_manifest,
        _manifest(context.root, context.commit, workspace_manifest),
    )
    rows: list[dict[str, str]] = []
    for kind, table in _dependency_tables(document):
        for name in sorted(table):
            spec = table[name]
            if type(spec) is not dict:
                continue
            resolved_spec, base_manifest = _resolve_inherited_dependency(
                spec,
                name,
                manifest_path,
                (workspace_manifest, workspace_doc),
            )
            path_value = resolved_spec.get("path")
            if path_value is None:
                continue
            if type(path_value) is not str:
                raise ReleaseClosureError("Cargo local dependency path must be text")
            target = _resolve_manifest_relative(base_manifest, path_value)
            if target not in context.manifest_paths:
                raise ReleaseClosureError("Cargo local dependency target is absent or untracked")
            rows.append(
                {
                    "from_manifest": manifest_path,
                    "dependency_kind": kind,
                    "dependency_name": name,
                    "to_manifest": target,
                }
            )
    return rows


def _resolve_inherited_dependency(
    spec: dict[str, Any],
    name: str,
    manifest_path: str,
    workspace: tuple[str, dict[str, Any]],
) -> tuple[dict[str, Any], str]:
    if spec.get("workspace") is not True:
        return spec, manifest_path
    workspace_manifest, workspace_doc = workspace
    workspace_table = workspace_doc.get("workspace", {})
    dependencies = workspace_table.get("dependencies", {}) if type(workspace_table) is dict else {}
    resolved = dependencies.get(name) if type(dependencies) is dict else None
    if type(resolved) is not dict:
        raise ReleaseClosureError("inherited workspace dependency is unresolved")
    return resolved, workspace_manifest


def _local_override_rows(
    context: _CargoContext,
    workspace_root: str,
) -> list[dict[str, str]]:
    workspace_manifest = f"{workspace_root}/Cargo.toml"
    document = context.cache.setdefault(
        workspace_manifest,
        _manifest(context.root, context.commit, workspace_manifest),
    )
    rows = _patch_rows(context, workspace_manifest, document.get("patch", {}))
    rows.extend(_replace_rows(context, workspace_manifest, document.get("replace", {})))
    return rows


def _patch_rows(
    context: _CargoContext,
    workspace_manifest: str,
    patch: Any,
) -> list[dict[str, str]]:
    if type(patch) is not dict:
        raise ReleaseClosureError("Cargo patch table is malformed")
    rows: list[dict[str, str]] = []
    for source in sorted(patch):
        table = patch[source]
        if type(source) is not str or type(table) is not dict:
            raise ReleaseClosureError("Cargo patch source table is malformed")
        rows.extend(
            _override_table_rows(
                context,
                workspace_manifest,
                f"patch:{source}",
                table,
            )
        )
    return rows


def _replace_rows(
    context: _CargoContext,
    workspace_manifest: str,
    table: Any,
) -> list[dict[str, str]]:
    if type(table) is not dict:
        raise ReleaseClosureError("Cargo replace table is malformed")
    return _override_table_rows(context, workspace_manifest, "replace", table)


def _override_table_rows(
    context: _CargoContext,
    workspace_manifest: str,
    kind: str,
    table: dict[str, Any],
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for name in sorted(table):
        spec = table[name]
        if type(name) is not str or type(spec) is not dict:
            raise ReleaseClosureError("Cargo override entry must be an explicit table")
        path_value = spec.get("path")
        if path_value is None:
            continue
        if type(path_value) is not str:
            raise ReleaseClosureError("Cargo local override path must be text")
        target = _resolve_manifest_relative(workspace_manifest, path_value)
        if target not in context.manifest_paths:
            raise ReleaseClosureError("Cargo local override target is absent or untracked")
        rows.append(
            {
                "from_manifest": workspace_manifest,
                "dependency_kind": kind,
                "dependency_name": name,
                "to_manifest": target,
            }
        )
    return rows


def _dependency_tables(document: dict[str, Any]) -> Iterable[tuple[str, dict[str, Any]]]:
    names = ("dependencies", "dev-dependencies", "build-dependencies")
    for name in names:
        value = document.get(name, {})
        if type(value) is not dict:
            raise ReleaseClosureError(f"Cargo {name} table is malformed")
        yield name, value
    targets = document.get("target", {})
    if type(targets) is not dict:
        raise ReleaseClosureError("Cargo target table is malformed")
    for target_name in sorted(targets):
        target = targets[target_name]
        if type(target) is not dict:
            raise ReleaseClosureError("Cargo target configuration is malformed")
        for name in names:
            value = target.get(name, {})
            if type(value) is not dict:
                raise ReleaseClosureError("Cargo target dependency table is malformed")
            yield f"target:{target_name}:{name}", value


def _workspace_member_manifests(
    workspace_manifest: str,
    document: dict[str, Any],
) -> list[str]:
    workspace = document.get("workspace")
    if type(workspace) is not dict:
        raise ReleaseClosureError("V7 root manifest is not a Cargo workspace")
    members = workspace.get("members")
    if type(members) is not list or not members:
        raise ReleaseClosureError("V7 workspace must declare nonempty explicit members")
    result: list[str] = []
    for member in members:
        if type(member) is not str or any(character in member for character in "*?[]"):
            raise ReleaseClosureError("Cargo workspace members must be explicit paths")
        result.append(_resolve_manifest_relative(workspace_manifest, member))
    if len(result) != len(set(result)):
        raise ReleaseClosureError("Cargo workspace member list contains duplicates")
    return result


def _nearest_workspace_root(
    context: _CargoContext,
    package_manifest: str,
) -> str:
    package_root = PurePosixPath(package_manifest).parent
    for candidate in (package_root, *package_root.parents):
        if candidate == PurePosixPath("."):
            continue
        manifest = f"{candidate.as_posix()}/Cargo.toml"
        if manifest not in context.manifest_paths:
            continue
        document = context.cache.setdefault(
            manifest,
            _manifest(context.root, context.commit, manifest),
        )
        if type(document.get("workspace")) is dict:
            return candidate.as_posix()
    raise ReleaseClosureError("reachable Cargo package has no tracked workspace lock root")


def _all_manifest_paths(root: Path, commit: str) -> set[str]:
    raw = v6_planner._run_git(
        root,
        ["ls-tree", "-r", "-z", "--name-only", commit, "--"],
        maximum_stdout=MAX_GIT_PATH_OUTPUT_BYTES,
    ).stdout
    if raw and not raw.endswith(b"\0"):
        raise ReleaseClosureError("Git path inventory framing is invalid")
    result: set[str] = set()
    for item in raw.split(b"\0"):
        if not item:
            continue
        try:
            path = item.decode("utf-8", errors="strict")
        except UnicodeDecodeError as exc:
            raise ReleaseClosureError("Git path inventory contains non-UTF-8") from exc
        if path.endswith("/Cargo.toml") or path == "Cargo.toml":
            require_repo_relative(path, "Cargo manifest path")
            result.add(path)
    if not result:
        raise ReleaseClosureError("Git commit contains no Cargo manifests")
    return result


def _manifest(root: Path, commit: str, path: str) -> dict[str, Any]:
    raw = commit_file(root, commit, path, maximum=MAX_MANIFEST_BYTES)
    try:
        value = tomllib.loads(raw.decode("utf-8", errors="strict"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise ReleaseClosureError("Cargo manifest is not strict UTF-8 TOML") from exc
    if type(value) is not dict:
        raise ReleaseClosureError("Cargo manifest root is malformed")
    return value


def _resolve_manifest_relative(base_manifest: str, relative: str) -> str:
    if not relative or "\x00" in relative or relative.startswith("/"):
        raise ReleaseClosureError("Cargo path dependency is noncanonical")
    base = PurePosixPath(base_manifest).parent.as_posix()
    normalized = posixpath.normpath(posixpath.join(base, relative, "Cargo.toml"))
    require_repo_relative(normalized, "Cargo path dependency")
    return normalized


def _edge_key(row: dict[str, str]) -> tuple[str, str, str, str]:
    return (
        row["from_manifest"],
        row["dependency_kind"],
        row["dependency_name"],
        row["to_manifest"],
    )
