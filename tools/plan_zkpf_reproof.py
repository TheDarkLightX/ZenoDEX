#!/usr/bin/env python3
"""Plan deterministic ZKPF rebuild, reproof, replay, and release work."""
from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable, Mapping, Sequence

SCHEMA = "zenodex/zkpf_reproof_graph/v1"
PLAN_SCHEMA = "zenodex/zkpf_reproof_plan/v1"
TASK_SCHEMA = "zenodex/zkpf_reproof_task/v1"
MAX_MANIFEST_BYTES = 256 * 1024
MAX_CHANGED_PATHS = 4096
MAX_STAGES = 128
MAX_JSON_DEPTH = 128
_STAGE_ID_RE = re.compile(r"^[a-z][a-z0-9_]{0,63}$")
_ALLOWED_STAGE_TYPES = frozenset(
    {"source", "guest", "proof", "verifier", "adapter", "runtime", "release", "store"}
)
_ALLOWED_RESOURCES = frozenset({"light", "heavy", "privileged"})
_ALLOWED_AGENTS = frozenset({"routine", "strong", "frontier", "privileged_operator"})
_ALLOWED_REVIEWS = frozenset({"ordinary", "security", "math", "release", "operations"})
_ALLOWED_IMPLEMENTATION_STATUS = frozenset({"implemented", "planned"})
_STAGE_FIELDS = frozenset(
    {
        "id",
        "stage_type",
        "depends_on",
        "source_globs",
        "commands",
        "success_predicates",
        "outputs",
        "resource_class",
        "minimum_agent_class",
        "review_class",
        "implementation_status",
    }
)
_ROOT_FIELDS = frozenset({"schema", "stages"})


class ReproofPlanError(ValueError):
    pass


def canonical_json_bytes(value: object) -> bytes:
    rendered = json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )
    return (rendered + "\n").encode("ascii")


def _reject_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in out:
            raise ReproofPlanError(f"duplicate JSON key: {key}")
        out[key] = value
    return out


def _reject_float(value: str) -> object:
    raise ReproofPlanError(f"floating-point JSON number forbidden: {value}")


def _reject_constant(value: str) -> object:
    raise ReproofPlanError(f"non-finite JSON number forbidden: {value}")


def _require_depth(raw: bytes, maximum: int = MAX_JSON_DEPTH) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in (0x5B, 0x7B):
            depth += 1
            if depth > maximum:
                raise ReproofPlanError("JSON nesting exceeds limit")
        elif byte in (0x5D, 0x7D):
            depth -= 1
            if depth < 0:
                raise ReproofPlanError("JSON nesting is malformed")
    if in_string or depth != 0:
        raise ReproofPlanError("JSON structure is incomplete")


def strict_json_loads(raw: bytes, *, maximum: int = MAX_MANIFEST_BYTES) -> object:
    if type(raw) is not bytes or not raw or len(raw) > maximum:
        raise ReproofPlanError("manifest must be nonempty bounded bytes")
    _require_depth(raw)
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise ReproofPlanError("manifest must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_pairs,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
        )
    except ReproofPlanError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise ReproofPlanError("manifest JSON is invalid") from exc
    if canonical_json_bytes(value) != raw:
        raise ReproofPlanError("manifest JSON is not canonical")
    return value


def _safe_path(value: object, *, label: str, allow_glob: bool) -> str:
    if type(value) is not str or not value or len(value.encode("utf-8")) > 512:
        raise ReproofPlanError(f"{label} must be a bounded nonempty path")
    if "\\" in value or "\0" in value or value.startswith("/"):
        raise ReproofPlanError(f"{label} is not a safe repository-relative path")
    normalized = value
    if allow_glob:
        normalized = re.sub(r"[*?\[\]]", "x", value)
    parts = PurePosixPath(normalized).parts
    if not parts or any(part in {"", ".", ".."} for part in parts):
        raise ReproofPlanError(f"{label} is not a safe repository-relative path")
    return value


def _string_list(
    value: object,
    *,
    label: str,
    allow_empty: bool = False,
    paths: bool = False,
    require_sorted: bool = True,
) -> tuple[str, ...]:
    if not isinstance(value, list) or (not allow_empty and not value):
        requirement = "possibly empty" if allow_empty else "nonempty"
        raise ReproofPlanError(f"{label} must be a {requirement} list")
    out: list[str] = []
    for item in value:
        if type(item) is not str or not item:
            raise ReproofPlanError(f"{label} entries must be nonempty strings")
        out.append(_safe_path(item, label=label, allow_glob=True) if paths else item)
    if len(out) != len(set(out)):
        raise ReproofPlanError(f"{label} must be unique")
    if require_sorted and out != sorted(out):
        raise ReproofPlanError(f"{label} must be sorted")
    return tuple(out)


@dataclass(frozen=True, slots=True)
class Stage:
    id: str
    stage_type: str
    depends_on: tuple[str, ...]
    source_globs: tuple[str, ...]
    commands: tuple[str, ...]
    success_predicates: tuple[str, ...]
    outputs: tuple[str, ...]
    resource_class: str
    minimum_agent_class: str
    review_class: str
    implementation_status: str


@dataclass(frozen=True, slots=True)
class Graph:
    stages: tuple[Stage, ...]
    canonical_bytes: bytes

    @property
    def by_id(self) -> dict[str, Stage]:
        return {stage.id: stage for stage in self.stages}

    @property
    def digest(self) -> str:
        return hashlib.sha256(self.canonical_bytes).hexdigest()


def parse_graph(raw: bytes) -> Graph:
    value = strict_json_loads(raw)
    if type(value) is not dict or frozenset(value) != _ROOT_FIELDS:
        raise ReproofPlanError("graph root field set mismatch")
    if value.get("schema") != SCHEMA:
        raise ReproofPlanError("graph schema mismatch")
    rows = value.get("stages")
    if not isinstance(rows, list) or not rows or len(rows) > MAX_STAGES:
        raise ReproofPlanError("stages must be a nonempty bounded list")
    stages: list[Stage] = []
    for index, row in enumerate(rows):
        if type(row) is not dict or frozenset(row) != _STAGE_FIELDS:
            raise ReproofPlanError(f"stage[{index}] field set mismatch")
        stage_id = row.get("id")
        if type(stage_id) is not str or _STAGE_ID_RE.fullmatch(stage_id) is None:
            raise ReproofPlanError(f"stage[{index}] id is invalid")
        stage_type = row.get("stage_type")
        resource_class = row.get("resource_class")
        agent = row.get("minimum_agent_class")
        review = row.get("review_class")
        implementation_status = row.get("implementation_status")
        if stage_type not in _ALLOWED_STAGE_TYPES:
            raise ReproofPlanError(f"stage {stage_id} has unsupported type")
        if resource_class not in _ALLOWED_RESOURCES:
            raise ReproofPlanError(f"stage {stage_id} has unsupported resource class")
        if agent not in _ALLOWED_AGENTS:
            raise ReproofPlanError(f"stage {stage_id} has unsupported agent class")
        if review not in _ALLOWED_REVIEWS:
            raise ReproofPlanError(f"stage {stage_id} has unsupported review class")
        if implementation_status not in _ALLOWED_IMPLEMENTATION_STATUS:
            raise ReproofPlanError(
                f"stage {stage_id} has unsupported implementation status"
            )
        stages.append(
            Stage(
                id=stage_id,
                stage_type=stage_type,
                depends_on=_string_list(
                    row.get("depends_on"),
                    label=f"{stage_id}.depends_on",
                    allow_empty=True,
                ),
                source_globs=_string_list(
                    row.get("source_globs"),
                    label=f"{stage_id}.source_globs",
                    allow_empty=True,
                    paths=True,
                ),
                commands=_string_list(
                    row.get("commands"),
                    label=f"{stage_id}.commands",
                    require_sorted=False,
                ),
                success_predicates=_string_list(
                    row.get("success_predicates"),
                    label=f"{stage_id}.success_predicates",
                    require_sorted=False,
                ),
                outputs=_string_list(row.get("outputs"), label=f"{stage_id}.outputs"),
                resource_class=resource_class,
                minimum_agent_class=agent,
                review_class=review,
                implementation_status=implementation_status,
            )
        )
    if [stage.id for stage in stages] != sorted(stage.id for stage in stages):
        raise ReproofPlanError("stages must be sorted by id")
    if len(stages) != len({stage.id for stage in stages}):
        raise ReproofPlanError("stage ids must be unique")
    ids = {stage.id for stage in stages}
    for stage in stages:
        unknown = set(stage.depends_on) - ids
        if unknown or stage.id in stage.depends_on:
            raise ReproofPlanError(f"stage {stage.id} dependency set is invalid")
    _topological_waves(tuple(stages), set(ids))
    return Graph(tuple(stages), raw)


def normalize_changed_paths(paths: Iterable[str]) -> tuple[str, ...]:
    values = sorted(
        {
            _safe_path(path.strip(), label="changed path", allow_glob=False)
            for path in paths
            if path.strip()
        }
    )
    if len(values) > MAX_CHANGED_PATHS:
        raise ReproofPlanError("changed path count exceeds limit")
    return tuple(values)


def _matches(path: str, pattern: str) -> bool:
    if pattern.endswith("/**"):
        prefix = pattern[:-3].rstrip("/")
        return path == prefix or path.startswith(prefix + "/")
    return fnmatch.fnmatchcase(path, pattern)


def _topological_waves(stages: tuple[Stage, ...], selected: set[str]) -> list[list[str]]:
    by_id = {stage.id: stage for stage in stages}
    pending = set(selected)
    done: set[str] = set()
    waves: list[list[str]] = []
    while pending:
        ready = sorted(
            stage_id
            for stage_id in pending
            if all(
                dependency not in selected or dependency in done
                for dependency in by_id[stage_id].depends_on
            )
        )
        if not ready:
            raise ReproofPlanError("stage graph contains a dependency cycle")
        waves.append(ready)
        done.update(ready)
        pending.difference_update(ready)
    return waves


def plan_reproof(graph: Graph, changed_paths: Sequence[str]) -> dict[str, object]:
    changed = normalize_changed_paths(changed_paths)
    by_id = graph.by_id
    direct: dict[str, list[str]] = {}
    for stage in graph.stages:
        matches = [
            path
            for path in changed
            if any(_matches(path, pattern) for pattern in stage.source_globs)
        ]
        if matches:
            direct[stage.id] = matches

    selected = set(direct)
    changed_flag = True
    while changed_flag:
        changed_flag = False
        for stage in graph.stages:
            if stage.id not in selected and any(
                dependency in selected for dependency in stage.depends_on
            ):
                selected.add(stage.id)
                changed_flag = True

    waves = _topological_waves(graph.stages, selected) if selected else []
    changed_preimage = "".join(f"{path}\n" for path in changed).encode("utf-8")
    changed_root = hashlib.sha256(changed_preimage).hexdigest()
    tasks: list[dict[str, object]] = []
    task_ids: dict[str, str] = {}
    for wave_index, wave in enumerate(waves):
        for stage_id in wave:
            stage = by_id[stage_id]
            dependency_tasks = [
                task_ids[dependency]
                for dependency in stage.depends_on
                if dependency in task_ids
            ]
            seed = canonical_json_bytes(
                {
                    "changed_paths_sha256": changed_root,
                    "graph_sha256": graph.digest,
                    "stage_id": stage_id,
                    "dependency_task_ids": dependency_tasks,
                }
            )
            task_id = hashlib.sha256(seed).hexdigest()
            task_ids[stage_id] = task_id
            tasks.append(
                {
                    "task_id": task_id,
                    "stage_id": stage.id,
                    "stage_type": stage.stage_type,
                    "wave": wave_index,
                    "direct": stage.id in direct,
                    "matched_paths": direct.get(stage.id, []),
                    "dependency_task_ids": dependency_tasks,
                    "commands": list(stage.commands),
                    "success_predicates": list(stage.success_predicates),
                    "outputs": list(stage.outputs),
                    "resource_class": stage.resource_class,
                    "minimum_agent_class": stage.minimum_agent_class,
                    "review_class": stage.review_class,
                    "implementation_status": stage.implementation_status,
                    "blocked_by_missing_implementation": (
                        stage.implementation_status == "planned"
                    ),
                    "authority": {
                        "proof_authority": False,
                        "release_authority": False,
                        "settlement_authority": False,
                        "production_authority": False,
                    },
                }
            )
    return {
        "schema": PLAN_SCHEMA,
        "graph_sha256": graph.digest,
        "changed_paths_sha256": changed_root,
        "changed_paths": list(changed),
        "direct_invalidations": [
            {"stage_id": stage_id, "matched_paths": direct[stage_id]}
            for stage_id in sorted(direct)
        ],
        "execution_waves": waves,
        "tasks": tasks,
        "unaffected_stages": [
            stage.id for stage in graph.stages if stage.id not in selected
        ],
        "authority": {
            "proof_authority": False,
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        },
    }


def _git_changed_paths(repository: Path, base: str, head: str) -> tuple[str, ...]:
    completed = subprocess.run(
        [
            "git",
            "-c",
            "core.quotepath=false",
            "diff",
            "--name-only",
            "--diff-filter=ACMR",
            f"{base}...{head}",
            "--",
        ],
        cwd=repository,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
        env={"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "LC_ALL": "C"},
    )
    if completed.returncode != 0 or completed.stderr:
        raise ReproofPlanError("git diff failed")
    return normalize_changed_paths(
        completed.stdout.decode("utf-8", errors="strict").splitlines()
    )


def _write_tasks(directory: Path, plan: Mapping[str, object]) -> None:
    if directory.exists():
        raise ReproofPlanError("task output directory must begin absent")
    directory.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(
        tempfile.mkdtemp(prefix=f".{directory.name}.staging-", dir=directory.parent)
    )
    try:
        tasks = plan.get("tasks")
        if not isinstance(tasks, list):
            raise ReproofPlanError("plan tasks are malformed")
        index: list[dict[str, object]] = []
        for row in tasks:
            if not isinstance(row, dict):
                raise ReproofPlanError("plan task is malformed")
            stage_id = row.get("stage_id")
            task_id = row.get("task_id")
            if type(stage_id) is not str or type(task_id) is not str:
                raise ReproofPlanError("plan task identity is malformed")
            task = {"schema": TASK_SCHEMA, **row}
            filename = f"{stage_id}-{task_id[:12]}.json"
            (staging / filename).write_bytes(canonical_json_bytes(task))
            index.append(
                {"stage_id": stage_id, "task_id": task_id, "file": filename}
            )
        (staging / "index.json").write_bytes(
            canonical_json_bytes(
                {
                    "schema": "zenodex/zkpf_reproof_task_index/v1",
                    "graph_sha256": plan["graph_sha256"],
                    "changed_paths_sha256": plan["changed_paths_sha256"],
                    "tasks": index,
                }
            )
        )
        os.rename(staging, directory)
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise


def _read_manifest(path: Path) -> bytes:
    raw = path.read_bytes()
    if len(raw) > MAX_MANIFEST_BYTES:
        raise ReproofPlanError("manifest exceeds byte limit")
    return raw


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--graph",
        type=Path,
        default=Path("config/proof_profiles/zkpf_reproof_graph_v1.json"),
    )
    parser.add_argument("--changed-path", action="append", default=[])
    parser.add_argument("--changed-paths-file", type=Path)
    parser.add_argument("--repository", type=Path, default=Path("."))
    parser.add_argument("--base")
    parser.add_argument("--head")
    parser.add_argument("--tasks-directory", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)
    try:
        graph = parse_graph(_read_manifest(args.graph))
        changed: list[str] = list(args.changed_path)
        if args.changed_paths_file is not None:
            changed.extend(
                args.changed_paths_file.read_text(encoding="utf-8").splitlines()
            )
        if args.base or args.head:
            if not args.base or not args.head or changed:
                raise ReproofPlanError(
                    "use either changed paths or an exact base/head pair"
                )
            changed.extend(_git_changed_paths(args.repository, args.base, args.head))
        plan = plan_reproof(graph, changed)
        if args.tasks_directory is not None:
            _write_tasks(args.tasks_directory, plan)
        if args.pretty:
            print(json.dumps(plan, indent=2, sort_keys=True))
        else:
            sys.stdout.buffer.write(canonical_json_bytes(plan))
        return 0
    except (OSError, ReproofPlanError, subprocess.SubprocessError) as exc:
        print(f"error: ZKPF reproof planning failed closed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
