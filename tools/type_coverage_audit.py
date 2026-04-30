#!/usr/bin/env python3
from __future__ import annotations

import argparse
import ast
import json
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ROOTS = ("src", "tools", "tests")
EXCLUDED_PARTS = frozenset({"deprecated", "experiments", "external", "generated", ".venv"})
EXCLUDED_PREFIXES = ("tools/dex-ui/",)


@dataclass(frozen=True)
class ModuleTypingStats:
    functions_total: int
    fully_typed_functions: int
    partially_typed_functions: int
    untyped_functions: int
    classes_total: int
    annotated_assignments: int

    @property
    def fully_typed_percent(self) -> float:
        if self.functions_total == 0:
            return 100.0
        return (self.fully_typed_functions / self.functions_total) * 100.0


@dataclass(frozen=True)
class TypingScopeStats:
    file_count: int
    mypy_configured_file_count: int
    module_stats: ModuleTypingStats

    @property
    def fully_typed_percent(self) -> float:
        return self.module_stats.fully_typed_percent


def _is_excluded(path: Path) -> bool:
    normalized = path.as_posix()
    return bool(set(path.parts) & EXCLUDED_PARTS) or any(
        normalized.startswith(prefix) for prefix in EXCLUDED_PREFIXES
    )


def _tracked_python_files(roots: Iterable[str]) -> list[Path]:
    root_args = list(roots)
    try:
        completed = subprocess.run(
            ["git", "ls-files", "--", *root_args],
            cwd=REPO_ROOT,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        files = [
            Path(line)
            for line in completed.stdout.splitlines()
            if line.endswith(".py") and not _is_excluded(Path(line))
        ]
        return sorted(files)
    except Exception:
        fallback_files: list[Path] = []
        for root in root_args:
            for path in (REPO_ROOT / root).rglob("*.py"):
                rel = path.relative_to(REPO_ROOT)
                if not _is_excluded(rel):
                    fallback_files.append(rel)
        return sorted(fallback_files)


def _configured_mypy_files(pyproject_path: Path = REPO_ROOT / "pyproject.toml") -> set[str]:
    if not pyproject_path.exists():
        return set()
    payload = tomllib.loads(pyproject_path.read_text(encoding="utf-8"))
    raw_files = payload.get("tool", {}).get("mypy", {}).get("files", [])
    if not isinstance(raw_files, list):
        return set()
    return {str(item) for item in raw_files if isinstance(item, str)}


def _function_annotation_state(node: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
    args = [
        *node.args.posonlyargs,
        *node.args.args,
        *node.args.kwonlyargs,
    ]
    if node.args.vararg is not None:
        args.append(node.args.vararg)
    if node.args.kwarg is not None:
        args.append(node.args.kwarg)
    arg_annotations = [
        arg.annotation is not None or arg.arg in {"self", "cls"}
        for arg in args
    ]
    has_return = node.returns is not None
    if has_return and all(arg_annotations):
        return "full"
    if has_return or any(arg_annotations):
        return "partial"
    return "none"


def module_typing_stats(path: Path) -> ModuleTypingStats:
    source = (REPO_ROOT / path).read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(path))
    functions_total = 0
    fully_typed_functions = 0
    partially_typed_functions = 0
    untyped_functions = 0
    classes_total = 0
    annotated_assignments = 0
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions_total += 1
            state = _function_annotation_state(node)
            if state == "full":
                fully_typed_functions += 1
            elif state == "partial":
                partially_typed_functions += 1
            else:
                untyped_functions += 1
        elif isinstance(node, ast.ClassDef):
            classes_total += 1
        elif isinstance(node, ast.AnnAssign):
            annotated_assignments += 1
    return ModuleTypingStats(
        functions_total=functions_total,
        fully_typed_functions=fully_typed_functions,
        partially_typed_functions=partially_typed_functions,
        untyped_functions=untyped_functions,
        classes_total=classes_total,
        annotated_assignments=annotated_assignments,
    )


def _sum_module_stats(stats: Iterable[ModuleTypingStats]) -> ModuleTypingStats:
    total = ModuleTypingStats(0, 0, 0, 0, 0, 0)
    for item in stats:
        total = ModuleTypingStats(
            functions_total=total.functions_total + item.functions_total,
            fully_typed_functions=total.fully_typed_functions + item.fully_typed_functions,
            partially_typed_functions=total.partially_typed_functions + item.partially_typed_functions,
            untyped_functions=total.untyped_functions + item.untyped_functions,
            classes_total=total.classes_total + item.classes_total,
            annotated_assignments=total.annotated_assignments + item.annotated_assignments,
        )
    return total


def audit_typing(roots: Iterable[str] = DEFAULT_ROOTS) -> dict[str, Any]:
    files = _tracked_python_files(roots)
    configured_files = _configured_mypy_files()
    per_file = {path: module_typing_stats(path) for path in files}

    def scope(prefixes: tuple[str, ...]) -> TypingScopeStats:
        scope_files = [path for path in files if path.as_posix().startswith(prefixes)]
        scope_stats = _sum_module_stats(per_file[path] for path in scope_files)
        return TypingScopeStats(
            file_count=len(scope_files),
            mypy_configured_file_count=sum(1 for path in scope_files if path.as_posix() in configured_files),
            module_stats=scope_stats,
        )

    scopes = {
        "overall": TypingScopeStats(
            file_count=len(files),
            mypy_configured_file_count=sum(1 for path in files if path.as_posix() in configured_files),
            module_stats=_sum_module_stats(per_file.values()),
        ),
        "src": scope(("src/",)),
        "core_state": scope(("src/core/", "src/state/")),
        "tools": scope(("tools/",)),
        "tests": scope(("tests/",)),
    }
    return {
        "schema": "zenodex/python-typing-audit/v1",
        "tracked_python_file_count": len(files),
        "mypy_configured_file_count": len(configured_files),
        "mypy_configured_present_count": scopes["overall"].mypy_configured_file_count,
        "scopes": {
            name: {
                "file_count": stats.file_count,
                "mypy_configured_file_count": stats.mypy_configured_file_count,
                "functions_total": stats.module_stats.functions_total,
                "fully_typed_functions": stats.module_stats.fully_typed_functions,
                "partially_typed_functions": stats.module_stats.partially_typed_functions,
                "untyped_functions": stats.module_stats.untyped_functions,
                "fully_typed_percent": round(stats.fully_typed_percent, 3),
                "classes_total": stats.module_stats.classes_total,
                "annotated_assignments": stats.module_stats.annotated_assignments,
            }
            for name, stats in scopes.items()
        },
    }


def _check_thresholds(
    result: dict[str, Any],
    *,
    min_src_full_typed_pct: float,
    min_core_state_full_typed_pct: float,
    min_mypy_configured_present: int,
) -> list[str]:
    errors: list[str] = []
    scopes = result["scopes"]
    src_pct = float(scopes["src"]["fully_typed_percent"])
    core_state_pct = float(scopes["core_state"]["fully_typed_percent"])
    configured_present = int(result["mypy_configured_present_count"])
    if src_pct < min_src_full_typed_pct:
        errors.append(f"src fully typed function rate {src_pct:.3f}% < {min_src_full_typed_pct:.3f}%")
    if core_state_pct < min_core_state_full_typed_pct:
        errors.append(
            "src/core+src/state fully typed function rate "
            f"{core_state_pct:.3f}% < {min_core_state_full_typed_pct:.3f}%"
        )
    if configured_present < min_mypy_configured_present:
        errors.append(
            f"mypy configured present files {configured_present} < {min_mypy_configured_present}"
        )
    return errors


def _print_text(result: dict[str, Any], errors: list[str]) -> None:
    print(f"tracked_python_file_count: {result['tracked_python_file_count']}")
    print(f"mypy_configured_file_count: {result['mypy_configured_file_count']}")
    print(f"mypy_configured_present_count: {result['mypy_configured_present_count']}")
    for name, stats in result["scopes"].items():
        print(
            f"{name}: files={stats['file_count']} configured={stats['mypy_configured_file_count']} "
            f"functions={stats['functions_total']} fully_typed={stats['fully_typed_functions']} "
            f"partial={stats['partially_typed_functions']} untyped={stats['untyped_functions']} "
            f"rate={stats['fully_typed_percent']:.3f}%"
        )
    for error in errors:
        print(f"error: {error}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.add_argument("--check", action="store_true", help="Fail if ratchet thresholds are not met.")
    parser.add_argument("--min-src-full-typed-pct", type=float, default=98.9)
    parser.add_argument("--min-core-state-full-typed-pct", type=float, default=97.5)
    parser.add_argument("--min-mypy-configured-present", type=int, default=25)
    args = parser.parse_args(argv)

    result = audit_typing()
    errors = (
        _check_thresholds(
            result,
            min_src_full_typed_pct=float(args.min_src_full_typed_pct),
            min_core_state_full_typed_pct=float(args.min_core_state_full_typed_pct),
            min_mypy_configured_present=int(args.min_mypy_configured_present),
        )
        if args.check
        else []
    )
    if args.format == "json":
        payload = dict(result)
        payload["ok"] = not errors
        payload["errors"] = errors
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        _print_text(result, errors)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
