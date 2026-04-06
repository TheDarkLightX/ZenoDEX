#!/usr/bin/env python3
"""
Generate a Tau spec coverage map (internal).

This is a discovery report (not a proof). It helps answer:
  - Which `src/tau_specs/**/*.tau` files exist?
  - Which are referenced by `src/integration/tau_witness.py`?
  - Which are imported by runtime gates (`tau_gate.py`, `zusd_tau_gate.py`)?
  - Which are referenced by tests (best-effort string scan)?

Output: internal/coverage_maps/tau_spec_coverage_map.auto.md
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
TAU_SPECS_DIR = REPO_ROOT / "src" / "tau_specs"
INTEGRATION_DIR = REPO_ROOT / "src" / "integration"
TESTS_DIR = REPO_ROOT / "tests"


@dataclass(frozen=True)
class WitnessRef:
    name: str  # Python constant name in tau_witness.py
    spec_id: str | None
    rel_path: str | None  # repo-relative path like "src/tau_specs/recommended/xxx.tau"
    gate_output: str | None


def _iter_files(root: Path, suffix: str) -> list[Path]:
    out: list[Path] = []
    for p in root.rglob(f"*{suffix}"):
        if "__pycache__" in p.parts:
            continue
        out.append(p)
    out.sort()
    return out


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _parse_ast(path: Path) -> ast.AST:
    return ast.parse(_read_text(path), filename=str(path))


def _extract_tau_files() -> set[str]:
    files = set()
    if not TAU_SPECS_DIR.is_dir():
        return files
    for p in _iter_files(TAU_SPECS_DIR, ".tau"):
        files.add(str(p.relative_to(REPO_ROOT)))
    return files


def _eval_tau_path_expr(expr: ast.AST) -> str | None:
    """
    Evaluate expressions of the form:
      RECOMMENDED_SPECS_DIR / "foo.tau"
      TAU_SPECS_DIR / "bar.tau"

    Returns repo-relative path string, or None if unsupported.
    """
    if not isinstance(expr, ast.BinOp) or not isinstance(expr.op, ast.Div):
        return None
    if not isinstance(expr.left, ast.Name):
        return None
    if not isinstance(expr.right, ast.Constant) or not isinstance(expr.right.value, str):
        return None
    base = expr.left.id
    fname = expr.right.value
    if not fname.endswith(".tau"):
        return None
    if base == "RECOMMENDED_SPECS_DIR":
        return str(Path("src/tau_specs/recommended") / fname)
    if base == "TAU_SPECS_DIR":
        return str(Path("src/tau_specs") / fname)
    return None


def _extract_tau_witness_refs() -> dict[str, WitnessRef]:
    witness_path = INTEGRATION_DIR / "tau_witness.py"
    if not witness_path.exists():
        return {}
    tree = _parse_ast(witness_path)
    refs: dict[str, WitnessRef] = {}
    for node in tree.body if isinstance(tree, ast.Module) else []:
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        tgt = node.targets[0]
        if not isinstance(tgt, ast.Name):
            continue
        name = tgt.id
        call = node.value
        if not isinstance(call, ast.Call):
            continue
        if not isinstance(call.func, ast.Name) or call.func.id != "TauSpecRef":
            continue
        spec_id: str | None = None
        rel_path: str | None = None
        gate_output: str | None = None
        for kw in call.keywords or []:
            if not isinstance(kw, ast.keyword) or kw.arg is None:
                continue
            if kw.arg == "spec_id" and isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str):
                spec_id = kw.value.value
            elif kw.arg == "gate_output" and isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str):
                gate_output = kw.value.value
            elif kw.arg == "path":
                rel_path = _eval_tau_path_expr(kw.value)
        refs[name] = WitnessRef(name=name, spec_id=spec_id, rel_path=rel_path, gate_output=gate_output)
    return refs


def _extract_tau_witness_imports(py_path: Path) -> set[str]:
    tree = _parse_ast(py_path)
    names: set[str] = set()
    for node in ast.walk(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        if (node.module or "") != "tau_witness":
            continue
        # from .tau_witness import ... has level=1
        for alias in node.names:
            if alias.name == "*":
                continue
            names.add(alias.name)
    return names


def _scan_tests_for_tau_paths(*, known_tau_paths: Iterable[str]) -> set[str]:
    """
    Best-effort scan: find any string literal containing a repo-relative `.tau` path.
    """
    if not TESTS_DIR.is_dir():
        return set()
    known = set(known_tau_paths)
    if not known:
        return set()
    # Regex for potential path-like strings; we later filter by known set membership.
    pat = re.compile(r"src/tau_specs/[A-Za-z0-9_./-]+\.tau")
    hit: set[str] = set()
    for p in _iter_files(TESTS_DIR, ".py"):
        txt = _read_text(p)
        for m in pat.finditer(txt):
            s = m.group(0)
            if s in known:
                hit.add(s)
    return hit


def _render_report(
    *,
    tau_paths: set[str],
    witness_refs: dict[str, WitnessRef],
    used_by_tau_gate: set[str],
    used_by_zusd_tau_gate: set[str],
    used_by_trace_cases: set[str],
    tested_paths: set[str],
) -> str:
    witness_paths = {r.rel_path for r in witness_refs.values() if r.rel_path}
    used_paths_tau_gate = {witness_refs[n].rel_path for n in used_by_tau_gate if n in witness_refs and witness_refs[n].rel_path}
    used_paths_zusd = {witness_refs[n].rel_path for n in used_by_zusd_tau_gate if n in witness_refs and witness_refs[n].rel_path}
    used_paths_trace = {witness_refs[n].rel_path for n in used_by_trace_cases if n in witness_refs and witness_refs[n].rel_path}

    lines: list[str] = []
    lines.append("# Tau Spec Coverage Map (auto)")
    lines.append("")
    lines.append("This is a discovery report (not a proof).")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Tau specs on disk: {len(tau_paths)}")
    lines.append(f"- Referenced by `src/integration/tau_witness.py`: {len(witness_paths)}")
    lines.append(f"- Imported by runtime gate `src/integration/tau_gate.py`: {len(used_paths_tau_gate)}")
    lines.append(f"- Imported by runtime gate `src/integration/zusd_tau_gate.py`: {len(used_paths_zusd)}")
    lines.append(f"- Imported by trace catalog `src/integration/tau_trace_cases.py`: {len(used_paths_trace)}")
    lines.append(f"- Referenced by tests (string scan, best-effort): {len(tested_paths)}")
    lines.append("")

    lines.append("## Specs")
    lines.append("")
    lines.append("| Spec Path | In tau_witness | tau_gate | zusd_tau_gate | tau_trace_cases | Referenced in tests |")
    lines.append("|---|---:|---:|---:|---:|---:|")
    for rel in sorted(tau_paths):
        in_witness = "yes" if rel in witness_paths else ""
        in_tau_gate = "yes" if rel in used_paths_tau_gate else ""
        in_zusd = "yes" if rel in used_paths_zusd else ""
        in_trace = "yes" if rel in used_paths_trace else ""
        in_tests = "yes" if rel in tested_paths else ""
        lines.append(f"| {rel} | {in_witness} | {in_tau_gate} | {in_zusd} | {in_trace} | {in_tests} |")
    lines.append("")

    lines.append("## Gaps (high-signal)")
    lines.append("")
    missing_from_witness = sorted(tau_paths - witness_paths)
    if missing_from_witness:
        lines.append("- Specs on disk but not referenced by tau_witness (may be legacy/experimental):")
        for p in missing_from_witness[:40]:
            lines.append(f"  - `{p}`")
        if len(missing_from_witness) > 40:
            lines.append(f"  - ... ({len(missing_from_witness) - 40} more)")
    else:
        lines.append("- All specs on disk are referenced by tau_witness.")
    lines.append("")

    runtime_but_untested = sorted((used_paths_tau_gate | used_paths_zusd) - tested_paths)
    if runtime_but_untested:
        lines.append("- Specs imported by runtime gates but not referenced by tests (best-effort scan):")
        for p in runtime_but_untested[:40]:
            lines.append(f"  - `{p}`")
        if len(runtime_but_untested) > 40:
            lines.append(f"  - ... ({len(runtime_but_untested) - 40} more)")
    else:
        lines.append("- All runtime-imported specs appear in tests (best-effort scan).")
    lines.append("")

    return "\n".join(lines)


def main() -> int:
    tau_paths = _extract_tau_files()
    witness_refs = _extract_tau_witness_refs()

    tau_gate_imports = _extract_tau_witness_imports(INTEGRATION_DIR / "tau_gate.py")
    zusd_imports = _extract_tau_witness_imports(INTEGRATION_DIR / "zusd_tau_gate.py")
    trace_imports = _extract_tau_witness_imports(INTEGRATION_DIR / "tau_trace_cases.py")

    tested = _scan_tests_for_tau_paths(known_tau_paths=tau_paths)

    report = _render_report(
        tau_paths=tau_paths,
        witness_refs=witness_refs,
        used_by_tau_gate=tau_gate_imports,
        used_by_zusd_tau_gate=zusd_imports,
        used_by_trace_cases=trace_imports,
        tested_paths=tested,
    )

    out_dir = REPO_ROOT / "internal" / "coverage_maps"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "tau_spec_coverage_map.auto.md"
    out_path.write_text(report, encoding="utf-8")
    print(str(out_path.relative_to(REPO_ROOT)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
