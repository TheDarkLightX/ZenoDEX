#!/usr/bin/env python3
"""Static guard for direct DEX value-moving entrypoints.

Production ingress should route through `src.integration.dex_engine.apply_ops`
or an explicitly scoped verifier/certificate helper. This check is deliberately
small and syntactic: it catches accidental new direct calls to settlement
application helpers or pure `Dex` construction in runtime code.
"""

from __future__ import annotations

import ast
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

WATCH_ROOTS = (ROOT / "src", ROOT / "tools")
CALL_NAMES = {"apply_settlement", "apply_settlement_pure", "Dex"}
DEX_IMPORT_MODULES = {
    "..core.dex",
    ".core.dex",
    "src.core.dex",
}

ALLOWED_CALLS = {
    ("src/core/batch_clearing.py", "apply_settlement"),
    ("src/core/batch_clearing.py", "apply_settlement_pure"),
    ("src/core/dex.py", "apply_settlement_pure"),
    ("src/integration/dex_engine.py", "apply_settlement_pure"),
    ("src/integration/settlement_strong_certificate.py", "apply_settlement_pure"),
    ("src/integration/validation.py", "apply_settlement"),
}

ALLOWED_DEX_IMPORT_FILES = {
    "src/core/dex.py",
}


def _iter_python_files() -> list[Path]:
    files: list[Path] = []
    for root in WATCH_ROOTS:
        if not root.exists():
            continue
        files.extend(path for path in root.rglob("*.py") if "__pycache__" not in path.parts)
    return sorted(files)


def _rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def _call_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _import_module(node: ast.ImportFrom) -> str:
    dots = "." * int(node.level or 0)
    return dots + (node.module or "")


def _scan_file(path: Path) -> list[dict[str, object]]:
    rel = _rel(path)
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=rel)
    except SyntaxError as exc:
        return [{"path": rel, "line": exc.lineno or 0, "kind": "syntax_error", "detail": str(exc)}]

    issues: list[dict[str, object]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            name = _call_name(node.func)
            if name in CALL_NAMES and (rel, name) not in ALLOWED_CALLS:
                issues.append(
                    {
                        "path": rel,
                        "line": int(getattr(node, "lineno", 0)),
                        "kind": "direct_value_moving_call",
                        "detail": name,
                    }
                )
        elif isinstance(node, ast.ImportFrom):
            module = _import_module(node)
            if module in DEX_IMPORT_MODULES and rel not in ALLOWED_DEX_IMPORT_FILES:
                imported = {alias.name for alias in node.names}
                if "Dex" in imported:
                    issues.append(
                        {
                            "path": rel,
                            "line": int(getattr(node, "lineno", 0)),
                            "kind": "direct_dex_import",
                            "detail": module,
                        }
                    )
    return issues


def main() -> int:
    issues: list[dict[str, object]] = []
    for path in _iter_python_files():
        issues.extend(_scan_file(path))

    payload = {
        "schema": "zenodex.dex_value_moving_entrypoints_check.v1",
        "ok": not issues,
        "checked_file_count": len(_iter_python_files()),
        "allowed_calls": sorted(
            [{"path": path, "call": call} for path, call in ALLOWED_CALLS],
            key=lambda x: (x["path"], x["call"]),
        ),
        "issues": issues,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if not issues else 1


if __name__ == "__main__":
    raise SystemExit(main())
