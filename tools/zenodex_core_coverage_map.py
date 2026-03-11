#!/usr/bin/env python3
"""
Generate a "coverage map" for the functional core: src/core + src/state.

This is an internal quality tool to support correct-by-construction posture:
- Identify which modules are kernel-backed (src/kernels/python) or use ESSO directly.
- Identify which modules are exercised by tests (import graph from tests/**/*.py).
- Surface likely FSM boundaries (modules that define a top-level `step`).
- Cross-reference available verification reports under internal/**/verification_report.md.

This tool is evidence-discovery only. It does not claim semantic equivalence between
implementation and specs; it just helps you locate existing evidence artifacts.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class ModuleInfo:
    path: Path
    module: str
    is_state: bool
    has_step: bool
    kernel_py_imports: tuple[str, ...]
    esso_imports: tuple[str, ...]
    imported_by_tests: tuple[str, ...]


def _iter_py_files(root: Path) -> list[Path]:
    out: list[Path] = []
    for p in root.rglob("*.py"):
        if "__pycache__" in p.parts:
            continue
        out.append(p)
    out.sort()
    return out


def _module_name_for_path(py_path: Path) -> str:
    rel = py_path.relative_to(REPO_ROOT)
    if rel.parts[0] != "src":
        raise ValueError(f"expected src-relative file, got: {py_path}")
    parts = list(rel.with_suffix("").parts)
    # Python module naming: package __init__.py is imported as the package name.
    if parts and parts[-1] == "__init__":
        parts = parts[:-1]
    mod = ".".join(parts)
    return mod


def _parse_ast(path: Path) -> ast.AST:
    try:
        src = path.read_text(encoding="utf-8")
    except Exception as exc:  # pragma: no cover (tooling)
        raise RuntimeError(f"failed to read {path}: {exc}") from exc
    try:
        return ast.parse(src, filename=str(path))
    except SyntaxError as exc:  # pragma: no cover (tooling)
        raise RuntimeError(f"failed to parse {path}: {exc}") from exc


def _imports_from_tree(tree: ast.AST) -> list[tuple[str, int]]:
    """Return list of (imported_module, level) for all import forms."""
    out: list[tuple[str, int]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                out.append((str(alias.name), 0))
        elif isinstance(node, ast.ImportFrom):
            if node.module is None:
                continue
            out.append((str(node.module), int(node.level or 0)))
    return out


def _defines_step(tree: ast.AST) -> bool:
    for node in tree.body if isinstance(tree, ast.Module) else []:
        if isinstance(node, ast.FunctionDef) and node.name == "step":
            return True
    return False


def _kernel_imports(imports: Iterable[tuple[str, int]]) -> tuple[str, ...]:
    mods: set[str] = set()
    for mod, _lvl in imports:
        # Relative imports in src/core use module like "kernels.python.xxx" with level>0.
        if mod.startswith("kernels.python.") or mod == "kernels.python":
            mods.add(mod)
        if mod.startswith("src.kernels.python.") or mod == "src.kernels.python":
            mods.add(mod)
    return tuple(sorted(mods))


def _esso_imports(imports: Iterable[tuple[str, int]]) -> tuple[str, ...]:
    mods: set[str] = set()
    for mod, _lvl in imports:
        if mod == "ESSO" or mod.startswith("ESSO."):
            mods.add(mod)
    return tuple(sorted(mods))


def _test_import_index() -> dict[str, set[str]]:
    """Map module -> set(test paths) by parsing tests/**/*.py AST imports."""
    tests_root = REPO_ROOT / "tests"
    if not tests_root.is_dir():
        return {}

    idx: dict[str, set[str]] = {}
    for path in _iter_py_files(tests_root):
        tree = _parse_ast(path)
        imports = _imports_from_tree(tree)
        for mod, _lvl in imports:
            if not (mod.startswith("src.core") or mod.startswith("src.state")):
                continue
            idx.setdefault(mod, set()).add(str(path.relative_to(REPO_ROOT)))
    return idx


def _verification_report_index() -> dict[str, set[str]]:
    """Map model_id -> set(report paths) for internal/**/verification_report.md."""
    internal_root = REPO_ROOT / "internal"
    if not internal_root.is_dir():
        return {}
    idx: dict[str, set[str]] = {}
    for path in internal_root.rglob("verification_report.md"):
        if "__pycache__" in path.parts:
            continue
        try:
            txt = path.read_text(encoding="utf-8")
        except Exception:
            continue
        model: str | None = None
        for line in txt.splitlines():
            if not line.startswith("**Model**:"):
                continue
            i = line.find("`")
            j = line.find("`", i + 1) if i >= 0 else -1
            if i >= 0 and j > i:
                model = line[i + 1 : j].strip()
            break
        if not model:
            continue
        idx.setdefault(model, set()).add(str(path.relative_to(REPO_ROOT)))
    return idx


def _generated_ref_index() -> dict[str, set[str]]:
    """Map ref stem -> set(paths) for generated/**/*_ref.py."""
    gen_root = REPO_ROOT / "generated"
    if not gen_root.is_dir():
        return {}
    idx: dict[str, set[str]] = {}
    for path in gen_root.rglob("*_ref.py"):
        if "__pycache__" in path.parts:
            continue
        stem = path.stem  # e.g., cpmm_swap_v8_ref
        idx.setdefault(stem, set()).add(str(path.relative_to(REPO_ROOT)))
    return idx


def _render_markdown(mods: list[ModuleInfo]) -> str:
    lines: list[str] = []
    lines.append("# Functional Core Coverage Map (auto)")
    lines.append("")
    lines.append("This is a discovery report (not a proof). It summarizes:")
    lines.append("- which modules are exercised by tests (import graph)")
    lines.append("- which modules are kernel-backed (src/kernels/python)")
    lines.append("- which modules import ESSO (spec interpreter / IR tooling)")
    lines.append("- likely FSM boundaries (top-level `step`)")
    lines.append("")

    total = len(mods)
    kernel_backed = sum(1 for m in mods if m.kernel_py_imports)
    esso_used = sum(1 for m in mods if m.esso_imports)
    fsm_like = sum(1 for m in mods if m.has_step)
    no_tests = sum(1 for m in mods if not m.imported_by_tests)
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Modules scanned: {total}")
    lines.append(f"- Kernel-backed modules: {kernel_backed}")
    lines.append(f"- ESSO-importing modules: {esso_used}")
    lines.append(f"- Modules defining `step`: {fsm_like}")
    lines.append(f"- Modules not imported by any tests: {no_tests}")
    lines.append("")

    lines.append("## Modules")
    lines.append("")
    lines.append("| Module | Path | FSM (`step`) | Kernel Python Imports | ESSO Imports | Imported By Tests |")
    lines.append("|---|---|---:|---|---|---|")
    for m in mods:
        k = ", ".join(m.kernel_py_imports) if m.kernel_py_imports else ""
        e = ", ".join(m.esso_imports) if m.esso_imports else ""
        t = ", ".join(m.imported_by_tests) if m.imported_by_tests else ""
        lines.append(
            "| "
            + m.module
            + " | "
            + str(m.path.relative_to(REPO_ROOT))
            + " | "
            + ("yes" if m.has_step else "")
            + " | "
            + k
            + " | "
            + e
            + " | "
            + t
            + " |"
        )

    lines.append("")
    lines.append("## Verification Reports (internal)")
    lines.append("")
    vr = _verification_report_index()
    if not vr:
        lines.append("- (none found under internal/**/verification_report.md)")
        return "\n".join(lines)

    # Only list models that look relevant to DEX kernels.
    models = sorted(vr.keys())
    for model in models:
        paths = sorted(vr[model])
        lines.append(f"- `{model}`:")
        for p in paths:
            lines.append(f"  - `{p}`")
    lines.append("")

    lines.append("## Generated Refs (generated/**/*_ref.py)")
    lines.append("")
    gr = _generated_ref_index()
    if not gr:
        lines.append("- (none found under generated/)")
        return "\n".join(lines)

    for stem in sorted(gr.keys()):
        paths = sorted(gr[stem])
        lines.append(f"- `{stem}`:")
        for p in paths:
            lines.append(f"  - `{p}`")

    return "\n".join(lines)


def main() -> int:
    core_root = REPO_ROOT / "src" / "core"
    state_root = REPO_ROOT / "src" / "state"
    test_idx = _test_import_index()

    mods: list[ModuleInfo] = []
    for root in (core_root, state_root):
        for path in _iter_py_files(root):
            tree = _parse_ast(path)
            imports = _imports_from_tree(tree)
            mod = _module_name_for_path(path)
            imported_by = sorted(test_idx.get(mod, set()))
            mods.append(
                ModuleInfo(
                    path=path,
                    module=mod,
                    is_state=str(path).startswith(str(state_root)),
                    has_step=_defines_step(tree),
                    kernel_py_imports=_kernel_imports(imports),
                    esso_imports=_esso_imports(imports),
                    imported_by_tests=tuple(imported_by),
                )
            )

    mods.sort(key=lambda m: m.module)
    report = _render_markdown(mods)

    out_dir = REPO_ROOT / "internal" / "coverage_maps"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "functional_core_coverage_map.auto.md"
    out_path.write_text(report, encoding="utf-8")
    print(str(out_path.relative_to(REPO_ROOT)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
