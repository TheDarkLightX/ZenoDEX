#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import (
    ROOT,
    extract_always_exprs,
    extract_stream_types,
    inline_definitions,
    normalize_spec_text,
    parse_definitions,
)
from tools.check_tau_formal_plan import DEFAULT_PLAN, validate_tau_formal_plan


_DATA_TOKENS = ("+", "-", "*", "/", "<", ">", "<=", ">=", "bv[", "#x")


def _sort_stream_name(name: str) -> tuple[int, str]:
    suffix = name[1:]
    if suffix.isdigit():
        return int(suffix), name
    return 10**9, name


def _load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError(f"{path}: expected JSON object")
    return raw


def _load_execution_map(path: Path) -> dict[str, dict[str, Any]]:
    raw = _load_json(path)
    entries = raw.get("entries", [])
    if not isinstance(entries, list):
        raise ValueError(f"{path}: entries must be a list")
    out: dict[str, dict[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        spec_id = str(entry.get("spec_id", "")).strip()
        if spec_id:
            out[spec_id] = entry
    return out


def _stable_repo_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return str(path)


def _profile_map(plan_path: Path = DEFAULT_PLAN) -> dict[str, dict[str, str]]:
    result = validate_tau_formal_plan(plan_path)
    if result.errors:
        raise ValueError("proof plan invalid:\n" + "\n".join(result.errors))
    return result.assignments


def _classify_definition(body: str) -> str:
    return "data_predicate" if any(token in body for token in _DATA_TOKENS) else "control_predicate"


def _shorten(text: str, limit: int = 160) -> str:
    compact = re.sub(r"\s+", " ", text.strip())
    if len(compact) <= limit:
        return compact
    return compact[: limit - 3] + "..."


def _strip_outer_parens(expr: str) -> str:
    current = expr.strip()
    while current.startswith("(") and current.endswith(")"):
        depth = 0
        balanced = True
        for idx, ch in enumerate(current):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx != len(current) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        current = current[1:-1].strip()
    return current


def _split_top_level_and(expr: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    idx = 0
    while idx < len(expr):
        ch = expr[idx]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif depth == 0 and expr.startswith("&&", idx):
            parts.append(expr[start:idx].strip())
            idx += 2
            start = idx
            continue
        idx += 1
    tail = expr[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def _extract_output_equation_rows(spec_text: str) -> list[dict[str, str]]:
    defs = parse_definitions(spec_text)
    always_exprs = extract_always_exprs(spec_text)
    rows: list[dict[str, str]] = []
    for expr in always_exprs:
        expanded_expr = _strip_outer_parens(inline_definitions(expr, defs))
        for part in _split_top_level_and(expanded_expr):
            clause = _strip_outer_parens(part)
            iff_match = re.match(
                r"^(o\d+)\[([^\]]+)\]:([A-Za-z0-9_\[\]]+)\s*=\s*1:sbf\s*<->\s*(.+)$",
                clause,
            )
            if iff_match:
                rows.append(
                    {
                        "name": iff_match.group(1),
                        "index": iff_match.group(2),
                        "type": iff_match.group(3),
                        "style": "iff_true",
                        "expr": iff_match.group(4).strip(),
                    }
                )
                continue
            assign_match = re.match(
                r"^(o\d+)\[([^\]]+)\]:([A-Za-z0-9_\[\]]+)\s*=\s*(.+)$",
                clause,
            )
            if assign_match:
                rows.append(
                    {
                        "name": assign_match.group(1),
                        "index": assign_match.group(2),
                        "type": assign_match.group(3),
                        "style": "direct_assign",
                        "expr": assign_match.group(4).strip(),
                    }
                )
    deduped: dict[tuple[str, str], dict[str, str]] = {}
    for row in rows:
        deduped[(row["name"], row["index"])] = row
    return [
        deduped[key]
        for key in sorted(
            deduped,
            key=lambda item: (_sort_stream_name(item[0]), item[1]),
        )
    ]


def _spec_packet(
    *,
    spec_path: Path,
    execution_entry: dict[str, Any] | None,
    assignment: dict[str, str] | None,
) -> dict[str, Any]:
    spec_text = normalize_spec_text(spec_path.read_text(encoding="utf-8"))
    stream_types = extract_stream_types(spec_text)
    defs = parse_definitions(spec_text)
    always_exprs = extract_always_exprs(spec_text)

    input_streams = {k: v for k, v in stream_types.items() if k.startswith("i")}
    output_streams = {k: v for k, v in stream_types.items() if k.startswith("o")}
    sbf_inputs = sorted((name for name, ty in input_streams.items() if ty == "sbf"), key=_sort_stream_name)
    bv_inputs = sorted((name for name, ty in input_streams.items() if ty != "sbf"), key=_sort_stream_name)

    def_rows = []
    for name, definition in sorted(defs.items()):
        def_rows.append(
            {
                "name": name,
                "kind": _classify_definition(definition.body),
                "params": list(definition.params),
                "body": definition.body,
                "body_short": _shorten(definition.body, 220),
            }
        )

    control_helpers = [row["name"] for row in def_rows if row["kind"] == "control_predicate"]
    data_helpers = [row["name"] for row in def_rows if row["kind"] == "data_predicate"]
    equation_rows = _extract_output_equation_rows(spec_text)
    covered_outputs = sorted({row["name"] for row in equation_rows}, key=_sort_stream_name)

    packet: dict[str, Any] = {
        "spec_id": spec_path.stem,
        "spec_path": spec_path.relative_to(ROOT).as_posix(),
        "profile": assignment["profile"] if assignment else "",
        "rule": assignment["rule"] if assignment else "",
        "temporal": bool(re.search(r"\b[io]\d+\[(?!t\])[^]]+\]", spec_text)),
        "input_streams": {name: input_streams[name] for name in sorted(input_streams, key=_sort_stream_name)},
        "output_streams": {name: output_streams[name] for name in sorted(output_streams, key=_sort_stream_name)},
        "control_surface": {
            "sbf_inputs": sbf_inputs,
            "bv_inputs": bv_inputs,
            "always_count": len(always_exprs),
            "always_short": [_shorten(expr, 220) for expr in always_exprs],
            "control_helper_names": control_helpers,
        },
        "data_surface": {
            "data_helper_names": data_helpers,
            "definitions": def_rows,
        },
        "equation_surface": {
            "extractable": covered_outputs == sorted(output_streams, key=_sort_stream_name),
            "equation_count": len(equation_rows),
            "covered_outputs": covered_outputs,
            "rows": [
                {
                    "name": row["name"],
                    "index": row["index"],
                    "type": row["type"],
                    "style": row["style"],
                    "expr_short": _shorten(row["expr"], 220),
                }
                for row in equation_rows
            ],
        },
        "execution": {
            "status": execution_entry.get("status", "missing") if execution_entry else "missing",
            "runner": execution_entry.get("runner", "") if execution_entry else "",
            "observed_output_signatures": execution_entry.get("observed_output_signatures", []) if execution_entry else [],
            "error_messages": [err.get("message", "") for err in execution_entry.get("errors", [])] if execution_entry else [],
        },
    }
    return packet


def build_semantic_view(
    *,
    spec_ids: list[str],
    execution_census_path: Path,
) -> dict[str, Any]:
    execution_map = _load_execution_map(execution_census_path)
    assignments = _profile_map()
    packets = []
    spec_root = ROOT / "src" / "tau_specs" / "recommended"
    for spec_id in spec_ids:
        spec_path = spec_root / f"{spec_id}.tau"
        if not spec_path.exists():
            raise FileNotFoundError(f"spec not found: {spec_path}")
        rel = spec_path.relative_to(spec_root).as_posix()
        packets.append(
            _spec_packet(
                spec_path=spec_path,
                execution_entry=execution_map.get(spec_id),
                assignment=assignments.get(rel),
            )
        )

    return {
        "schema": "zenodex/tau/semantic-view/v1",
        "execution_census_ref": _stable_repo_path(execution_census_path),
        "spec_count": len(packets),
        "packets": packets,
    }


def _render_markdown(view: dict[str, Any]) -> str:
    lines = [
        "# Tau Semantic View",
        "",
        f"Execution census: `{view['execution_census_ref']}`",
        f"Spec count: `{view['spec_count']}`",
        "",
    ]
    for packet in view["packets"]:
        lines.append(f"## {packet['spec_id']}")
        lines.append("")
        lines.append(f"- Profile: `{packet['profile']}`")
        lines.append(f"- Rule: `{packet['rule']}`")
        lines.append(f"- Temporal: `{packet['temporal']}`")
        lines.append(f"- Execution: `{packet['execution']['status']}` via `{packet['execution']['runner']}`")
        if packet["execution"]["observed_output_signatures"]:
            lines.append(
                f"- Observed output signatures: `{', '.join(packet['execution']['observed_output_signatures'])}`"
            )
        if packet["execution"]["error_messages"]:
            lines.append(f"- Execution errors: `{packet['execution']['error_messages'][0]}`")
        lines.append(
            f"- Control surface: sbf inputs `{', '.join(packet['control_surface']['sbf_inputs']) or '(none)'}`, "
            f"bv inputs `{', '.join(packet['control_surface']['bv_inputs']) or '(none)'}`, "
            f"always clauses `{packet['control_surface']['always_count']}`"
        )
        if packet["control_surface"]["control_helper_names"]:
            lines.append(
                f"- Control helpers: `{', '.join(packet['control_surface']['control_helper_names'])}`"
            )
        if packet["data_surface"]["data_helper_names"]:
            lines.append(
                f"- Data helpers: `{', '.join(packet['data_surface']['data_helper_names'])}`"
            )
        lines.append(
            f"- Equation surface: extractable `{packet['equation_surface']['extractable']}`, "
            f"equations `{packet['equation_surface']['equation_count']}`, "
            f"covered outputs `{', '.join(packet['equation_surface']['covered_outputs']) or '(none)'}`"
        )
        for expr in packet["control_surface"]["always_short"][:2]:
            lines.append(f"- Always: `{expr}`")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate a control/data semantic view for selected Tau specs.")
    parser.add_argument("--execution-census", default="formal/tau/recommended_execution_census_best.json")
    parser.add_argument("--spec-id", action="append", default=[], help="Spec id(s) to include.")
    parser.add_argument("--spec-list-json", default="", help="Optional JSON file containing a list of spec ids.")
    parser.add_argument("--all-recommended", action="store_true", help="Include all recommended Tau specs.")
    parser.add_argument("--out-json", default="formal/tau/semantic_view.json")
    parser.add_argument("--out-md", default="formal/tau/semantic_view.md")
    args = parser.parse_args()

    spec_ids = [value.strip() for value in args.spec_id if value.strip()]
    if args.spec_list_json:
        raw = json.loads(Path(args.spec_list_json).read_text(encoding="utf-8"))
        if not isinstance(raw, list):
            raise SystemExit("--spec-list-json must contain a JSON list")
        spec_ids.extend(str(value).strip() for value in raw if str(value).strip())
    if args.all_recommended:
        spec_root = ROOT / "src" / "tau_specs" / "recommended"
        spec_ids.extend(path.stem for path in sorted(spec_root.glob("*.tau")))
    if not spec_ids:
        raise SystemExit("at least one --spec-id or --spec-list-json is required")

    deduped = []
    seen = set()
    for spec_id in spec_ids:
        if spec_id in seen:
            continue
        seen.add(spec_id)
        deduped.append(spec_id)

    view = build_semantic_view(
        spec_ids=deduped,
        execution_census_path=Path(args.execution_census),
    )

    out_json = Path(args.out_json)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(view, indent=2) + "\n", encoding="utf-8")

    out_md = Path(args.out_md)
    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_md.write_text(_render_markdown(view), encoding="utf-8")

    print(f"spec count: {view['spec_count']}")
    print(f"wrote {out_json}")
    print(f"wrote {out_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
