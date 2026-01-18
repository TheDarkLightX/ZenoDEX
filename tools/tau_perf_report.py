#!/usr/bin/env python3
"""
Summarize Tau trace-harness timings and relate them to spec profiles.

This is intentionally lightweight:
- No Tau execution happens here.
- It only reads the JSON produced by `tools/tau_trace_harness.py`.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple


REPO_ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class SpecTiming:
    spec_id: str
    spec_path: Path
    max_elapsed_s: float
    avg_elapsed_s: float
    cases: int


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _timings_from_report(report: Dict[str, Any]) -> Tuple[Dict[str, SpecTiming], Dict[Path, SpecTiming]]:
    results = list(report.get("results") or [])
    by_spec_id: Dict[str, List[Dict[str, Any]]] = {}
    for r in results:
        spec_id = str(r.get("spec_id") or "")
        if not spec_id:
            continue
        by_spec_id.setdefault(spec_id, []).append(r)

    spec_id_to_timing: Dict[str, SpecTiming] = {}
    spec_path_to_timing: Dict[Path, SpecTiming] = {}
    for spec_id, rows in by_spec_id.items():
        elapsed = [float(r.get("elapsed_s") or 0.0) for r in rows]
        spec_path_str = str(rows[0].get("spec_path") or "")
        spec_path = Path(spec_path_str) if spec_path_str else Path()
        timing = SpecTiming(
            spec_id=spec_id,
            spec_path=spec_path,
            max_elapsed_s=max(elapsed) if elapsed else 0.0,
            avg_elapsed_s=(sum(elapsed) / len(elapsed)) if elapsed else 0.0,
            cases=len(elapsed),
        )
        spec_id_to_timing[spec_id] = timing
        if spec_path_str:
            spec_path_to_timing[spec_path] = timing

    return spec_id_to_timing, spec_path_to_timing


def _markdown_table(rows: Iterable[List[str]]) -> str:
    rows = list(rows)
    if not rows:
        return ""
    header = rows[0]
    out = ["| " + " | ".join(header) + " |", "| " + " | ".join(["---"] * len(header)) + " |"]
    for r in rows[1:]:
        out.append("| " + " | ".join(r) + " |")
    return "\n".join(out) + "\n"


def _format_s(v: Optional[float]) -> str:
    if v is None:
        return ""
    return f"{v:.2f}"


def _resolve_repo_path(p: str) -> Path:
    path = Path(p)
    if path.is_absolute():
        return path
    return (REPO_ROOT / path).resolve()


def _iter_profile_variants(profiles: Dict[str, Any]) -> Iterable[Tuple[str, str, str, str]]:
    components = dict(profiles.get("components") or {})
    for component_id, component in components.items():
        for variant in list(component.get("variants") or []):
            variant_id = str(variant.get("variant_id") or "")
            profile = str(variant.get("profile") or "")
            spec_path = str(variant.get("spec_path") or "")
            if not (variant_id and profile and spec_path):
                continue
            yield component_id, variant_id, profile, spec_path


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument(
        "--report-json",
        default=str(REPO_ROOT / "generated" / "tau_trace_harness_report.json"),
        help="Path to generated tau trace harness report JSON",
    )
    p.add_argument(
        "--profiles-json",
        default=str(REPO_ROOT / "src" / "tau_specs" / "recommended" / "spec_profiles.json"),
        help="Path to spec profile mapping JSON",
    )
    p.add_argument("--out", default="", help="Write markdown to this path (defaults to stdout)")
    args = p.parse_args(argv)

    report_path = _resolve_repo_path(str(args.report_json))
    if not report_path.exists():
        raise SystemExit(f"report not found: {report_path}")

    report = _load_json(report_path)
    spec_id_to_timing, spec_path_to_timing = _timings_from_report(report)

    profiles_path = _resolve_repo_path(str(args.profiles_json))
    profiles = _load_json(profiles_path) if profiles_path.exists() else {}

    md: List[str] = []
    md.append("# Tau timing summary (trace harness)\n")
    md.append(f"Source: `{report_path.relative_to(REPO_ROOT)}`\n")

    rows = [["spec_id", "max_elapsed_s", "avg_elapsed_s", "cases", "spec_path"]]
    for timing in sorted(spec_id_to_timing.values(), key=lambda t: t.max_elapsed_s, reverse=True):
        rel = str(timing.spec_path)
        try:
            rel = str(timing.spec_path.relative_to(REPO_ROOT))
        except Exception:
            pass
        rows.append([timing.spec_id, _format_s(timing.max_elapsed_s), _format_s(timing.avg_elapsed_s), str(timing.cases), rel])
    md.append("## By spec_id\n")
    md.append(_markdown_table(rows))

    if profiles:
        md.append("## By component variant\n")
        md.append("This table joins spec profiles with observed trace timings when available.\n")

        prof_defs: Dict[str, Any] = dict(profiles.get("profiles") or {})
        rows2 = [["component", "variant", "profile", "budget_s", "max_elapsed_s", "spec_path"]]
        for component_id, variant_id, profile, spec_path in _iter_profile_variants(profiles):
            budget = prof_defs.get(profile, {}).get("timeout_budget_s_on_dev_machine")
            resolved = _resolve_repo_path(spec_path)
            timing = spec_path_to_timing.get(resolved)
            rel = spec_path
            rows2.append(
                [
                    component_id,
                    variant_id,
                    profile,
                    str(budget) if budget is not None else "",
                    _format_s(timing.max_elapsed_s) if timing else "",
                    rel,
                ]
            )
        md.append(_markdown_table(rows2))

    text = "\n".join(md).strip() + "\n"
    out_path = str(args.out).strip()
    if out_path:
        Path(out_path).write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

