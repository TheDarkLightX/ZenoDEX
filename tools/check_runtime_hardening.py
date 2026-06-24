#!/usr/bin/env python3
"""Runtime hardening checks for consensus-adjacent Python source.

The checker intentionally gates only three high-signal regression classes:

* runtime ``assert`` statements in source paths, because ``python -O`` strips
  them;
* broad exception handlers whose entire body is ``pass``, ``continue``, or
  ``return None``, because they silently erase unexpected faults.
* module-scope broad exception handlers, because optional dependency guards must
  not hide arbitrary package initialization bugs.

Boundary handlers that catch ``Exception as exc`` and return a stable,
fail-closed error are outside this checker. Those need surface-specific review.
"""

from __future__ import annotations

import argparse
import ast
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence


DEFAULT_SCAN_PATHS = (
    Path("src/core"),
    Path("src/integration"),
    Path("src/state"),
)

BROAD_EXCEPTION_NAMES = frozenset({"Exception", "BaseException"})


@dataclass(frozen=True)
class Finding:
    code: str
    path: str
    line: int
    function: str
    detail: str


def _python_files(paths: Iterable[Path]) -> list[Path]:
    files: list[Path] = []
    for path in paths:
        if path.is_file() and path.suffix == ".py":
            files.append(path)
        elif path.is_dir():
            files.extend(sorted(path.rglob("*.py")))
    return sorted(dict.fromkeys(files))


def _parent_map(tree: ast.AST) -> dict[ast.AST, ast.AST]:
    parents: dict[ast.AST, ast.AST] = {}
    for node in ast.walk(tree):
        for child in ast.iter_child_nodes(node):
            parents[child] = node
    return parents


def _enclosing_function(node: ast.AST, parents: dict[ast.AST, ast.AST]) -> str:
    parent = parents.get(node)
    while parent is not None:
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return parent.name
        parent = parents.get(parent)
    return "<module>"


def _broad_exception_type(node: ast.ExceptHandler) -> bool:
    if node.type is None:
        return True
    if isinstance(node.type, ast.Name):
        return node.type.id in BROAD_EXCEPTION_NAMES
    if isinstance(node.type, ast.Tuple):
        return any(isinstance(elt, ast.Name) and elt.id in BROAD_EXCEPTION_NAMES for elt in node.type.elts)
    return False


def _single_suppression_statement(node: ast.ExceptHandler) -> str | None:
    if len(node.body) != 1:
        return None
    stmt = node.body[0]
    if isinstance(stmt, ast.Pass):
        return "pass"
    if isinstance(stmt, ast.Continue):
        return "continue"
    if isinstance(stmt, ast.Return):
        if stmt.value is None:
            return "return_none"
        if isinstance(stmt.value, ast.Constant) and stmt.value.value is None:
            return "return_none"
    return None


def _is_module_scope_exception_handler(node: ast.ExceptHandler, parents: dict[ast.AST, ast.AST]) -> bool:
    parent = parents.get(node)
    return isinstance(parent, ast.Try) and isinstance(parents.get(parent), ast.Module)


def _scan_file(path: Path, *, root: Path) -> list[Finding]:
    rel_path = path.relative_to(root).as_posix() if path.is_relative_to(root) else path.as_posix()
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except SyntaxError as exc:
        return [
            Finding(
                code="python_syntax_error",
                path=rel_path,
                line=int(exc.lineno or 0),
                function="<parse>",
                detail=str(exc),
            )
        ]

    parents = _parent_map(tree)
    findings: list[Finding] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Assert):
            findings.append(
                Finding(
                    code="runtime_assert",
                    path=rel_path,
                    line=int(node.lineno),
                    function=_enclosing_function(node, parents),
                    detail="runtime assert is stripped by python -O",
                )
            )
            continue

        if isinstance(node, ast.ExceptHandler) and _broad_exception_type(node):
            if _is_module_scope_exception_handler(node, parents):
                findings.append(
                    Finding(
                        code="module_scope_broad_except",
                        path=rel_path,
                        line=int(node.lineno),
                        function="<module>",
                        detail="module-scope optional dependency guard catches arbitrary exceptions",
                    )
                )
                continue
            suppression = _single_suppression_statement(node)
            if suppression is None:
                continue
            findings.append(
                Finding(
                    code=f"broad_except_{suppression}",
                    path=rel_path,
                    line=int(node.lineno),
                    function=_enclosing_function(node, parents),
                    detail=f"broad exception handler only {suppression!r}s",
                )
            )
    return findings


def audit_runtime_hardening(root: Path, paths: Sequence[Path] = DEFAULT_SCAN_PATHS) -> dict[str, object]:
    root = root.resolve()
    scan_paths = [path if path.is_absolute() else root / path for path in paths]
    files = _python_files(scan_paths)
    findings: list[Finding] = []
    for path in files:
        findings.extend(_scan_file(path.resolve(), root=root))
    return {
        "ok": not findings,
        "files_scanned": len(files),
        "findings": [asdict(finding) for finding in findings],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path, default=list(DEFAULT_SCAN_PATHS))
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    report = audit_runtime_hardening(args.root, tuple(args.paths))
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        findings = report["findings"]
        if not isinstance(findings, list):
            raise TypeError("runtime hardening report findings must be a list")
        print(f"ok={report['ok']} files_scanned={report['files_scanned']} findings={len(findings)}")
        for finding in findings:
            if not isinstance(finding, dict):
                raise TypeError("runtime hardening finding must be an object")
            print(
                f"{finding['path']}:{finding['line']}:{finding['function']}: "
                f"{finding['code']}: {finding['detail']}"
            )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
