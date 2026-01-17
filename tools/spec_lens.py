#!/usr/bin/env python3
"""
Spec Lens: Human-friendly viewer for Tau specs.

Features:
- Lists each always-clause with numbering
- Shows line-by-line focus with nearby comments
- Extracts input/output descriptions from comment headers
- Supports lightweight metadata tags in comments:
    # @section: Name
    # @input i1: description
    # @output o1: description
    # @rule o7: description
    # @note: free-form text
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

SECTION_TAG = "@section:"
INPUT_TAG = "@input"
OUTPUT_TAG = "@output"
RULE_TAG = "@rule"
NOTE_TAG = "@note:"

INPUT_LINE_RE = re.compile(r"^#\s*i(\d+)(?:\.\.i(\d+))?\s*=\s*(.+)$")
OUTPUT_LINE_RE = re.compile(r"^#\s*o(\d+)(?:\.\.o(\d+))?\s*=\s*(.+)$")
TAG_INPUT_RE = re.compile(r"^#\s*@input\s+(i\d+)\s*:\s*(.+)$")
TAG_OUTPUT_RE = re.compile(r"^#\s*@output\s+(o\d+)\s*:\s*(.+)$")
TAG_RULE_RE = re.compile(r"^#\s*@rule\s+([a-zA-Z0-9_]+)\s*:\s*(.+)$")
TAG_SECTION_RE = re.compile(r"^#\s*@section\s*:\s*(.+)$")
TAG_NOTE_RE = re.compile(r"^#\s*@note\s*:\s*(.+)$")

CLAUSE_OUTPUT_RE = re.compile(r"\bo(\d+)\[[^\]]+\]\s*:")
CLAUSE_OUTPUT_RE_NO_TYPE = re.compile(r"\bo(\d+)\[[^\]]+\]\s*=")
REF_INPUT_RE = re.compile(r"\bi(\d+)\[")
REF_OUTPUT_RE = re.compile(r"\bo(\d+)\[")
CLAUSE_EQUIV_RE = re.compile(r"\bo(\d+)\[[^\]]+\]\s*(?::\w+)?\s*=\s*1:sbf\s*<->\s*(.+)")
CLAUSE_BOOL_RE = re.compile(r"\bo(\d+)\[[^\]]+\]\s*(?::\w+)?\s*=\s*(.+)")
FUNC_CALL_RE = re.compile(r"^([a-zA-Z_][a-zA-Z0-9_]*)\((.*)\)$")

@dataclass
class Clause:
    index: int
    text: str
    section: Optional[str]
    comments: List[str]
    outputs: List[str]
    inputs: List[str]
    refs: List[str]

@dataclass
class SpecDoc:
    spec_path: str
    inputs: Dict[str, str]
    outputs: Dict[str, str]
    rules: Dict[str, str]
    notes: List[str]
    sections: List[str]
    clauses: List[Clause]

PHRASE_MAP = {
    "canonical": "order ids are in strict increasing order",
    "no_sandwich": "prices are monotonic across the window (no sandwich)",
    "stable": "price change is within the stability threshold",
    "cpmm_ok": "the CPMM invariant holds for this swap",
    "balance_ok": "the balance transition is valid",
    "token_ok": "the protocol token transition is valid",
    "swap_constraints": "the CPMM swap inputs are valid and non-negative",
    "swap_exact_in_constraints": "exact-in swap constraints and reserve transitions are valid",
    "swap_exact_out_constraints": "exact-out swap constraints and reserve transitions are valid",
    "fee_rate_ok": "the fee matches the expected rate (with rounding tolerance)",
    "buyback_share_ok": "the buyback share matches the expected split",
    "buyback_ok": "buyback checks pass",
    "burn_ok": "burn amount equals buyback amount",
    "burn_floor_ok": "burn respects the minimum supply floor",
    "unit_ok": "amounts align to the fixed-point unit scale",
    "rebate_rate_ok": "rebate amount matches the rebate rate (with rounding tolerance)",
    "rebate_cap_ok": "rebate is within the cap and not above the fee",
    "thresholds_ok": "tier thresholds are ordered correctly",
    "weight_tier_ok": "claimed weight matches the lock-duration tier",
    "weighted_stake_ok": "weighted stake equals stake times weight",
    "fee_bps_valid": "fee basis points is within 0..10000",
    "is_zero_32": "value is zero",
    "is_positive_32": "value is positive",
    "is_positive": "value is positive",
    "value_gte": "value A is greater than or equal to value B",
    "value_gte_32": "value A is greater than or equal to value B",
    "one_hot_3": "exactly one of three flags is true",
    "token_transfer_valid": "transfer decreases sender, increases receiver, and keeps supply constant",
    "token_mint_valid": "mint increases receiver and total supply",
    "token_burn_valid": "burn decreases sender and total supply",
    "token_supply_eq": "token supply remains unchanged",
    "token_supply_inc": "token supply increases by amount",
    "token_supply_dec": "token supply decreases by amount",
    "add_32": "32-bit add with carry is valid",
    "sub_32": "32-bit subtraction with borrow is valid",
    "param_update_ok": "the next parameter is within bounds and step limit",
    "floor_bounds_ok": "the next floor is within its min/max bounds",
    "floor_step_ok": "the floor change is within the allowed step",
    "delay_ok": "the timelock delay has elapsed",
    "gate_ok": "execution is gated by approval",
    "apply_param": "output takes next value if gate is true, otherwise current",
}


def _expand_range(prefix: str, start: int, end: int) -> List[str]:
    if end < start:
        start, end = end, start
    return [f"{prefix}{i}" for i in range(start, end + 1)]


def _parse_io_lines(lines: List[str]) -> Tuple[Dict[str, str], Dict[str, str]]:
    inputs: Dict[str, str] = {}
    outputs: Dict[str, str] = {}
    for line in lines:
        m_in = INPUT_LINE_RE.match(line)
        if m_in:
            a = int(m_in.group(1))
            b = m_in.group(2)
            desc = m_in.group(3).strip()
            if b:
                for k in _expand_range("i", a, int(b)):
                    inputs[k] = desc
            else:
                inputs[f"i{a}"] = desc
            continue
        m_out = OUTPUT_LINE_RE.match(line)
        if m_out:
            a = int(m_out.group(1))
            b = m_out.group(2)
            desc = m_out.group(3).strip()
            if b:
                for k in _expand_range("o", a, int(b)):
                    outputs[k] = desc
            else:
                outputs[f"o{a}"] = desc
    return inputs, outputs


def _parse_tags(lines: List[str]) -> Tuple[Dict[str, str], Dict[str, str], Dict[str, str], List[str]]:
    tag_inputs: Dict[str, str] = {}
    tag_outputs: Dict[str, str] = {}
    rules: Dict[str, str] = {}
    notes: List[str] = []
    for line in lines:
        m = TAG_INPUT_RE.match(line)
        if m:
            tag_inputs[m.group(1)] = m.group(2).strip()
            continue
        m = TAG_OUTPUT_RE.match(line)
        if m:
            tag_outputs[m.group(1)] = m.group(2).strip()
            continue
        m = TAG_RULE_RE.match(line)
        if m:
            rules[m.group(1)] = m.group(2).strip()
            continue
        m = TAG_NOTE_RE.match(line)
        if m:
            notes.append(m.group(1).strip())
            continue
    return tag_inputs, tag_outputs, rules, notes


def _find_always_start(lines: List[str]) -> int:
    for idx, line in enumerate(lines):
        if line.strip().startswith("always"):
            return idx
    return -1


def _split_clauses(lines: List[str], start_idx: int) -> Tuple[List[Clause], List[str]]:
    clauses: List[Clause] = []
    section_stack: List[str] = []
    current_section: Optional[str] = None
    pending_comments: List[str] = []
    buf: List[str] = []
    depth = 0
    in_always = False

    def flush_clause():
        nonlocal buf, pending_comments, current_section
        text = " ".join(buf).strip()
        if not text:
            buf = []
            pending_comments = []
            return
        text = text.rstrip(".")
        outputs = _extract_outputs(text)
        inputs, refs = _extract_refs(text)
        clauses.append(Clause(
            index=len(clauses) + 1,
            text=text,
            section=current_section,
            comments=pending_comments[:],
            outputs=outputs,
            inputs=inputs,
            refs=refs,
        ))
        buf = []
        pending_comments = []

    for idx in range(start_idx, len(lines)):
        raw = lines[idx]
        line = raw.strip()
        if not in_always:
            if line.startswith("always"):
                in_always = True
                # remove leading "always"
                line = line[len("always"):].strip()
            else:
                continue
        if not line:
            continue
        if line.startswith("#"):
            sec = TAG_SECTION_RE.match(line)
            if sec:
                current_section = sec.group(1).strip()
                if current_section not in section_stack:
                    section_stack.append(current_section)
            else:
                pending_comments.append(line.lstrip("# ").strip())
            continue

        i = 0
        while i < len(line):
            ch = line[i]
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth = max(0, depth - 1)
            # detect top-level &&
            if ch == "&" and i + 1 < len(line) and line[i + 1] == "&" and depth == 0:
                buf.append(line[:i].strip())
                flush_clause()
                line = line[i + 2 :].strip()
                i = 0
                continue
            i += 1
        buf.append(line)

    flush_clause()
    return clauses, section_stack


def _extract_outputs(text: str) -> List[str]:
    outs = set()
    for m in CLAUSE_OUTPUT_RE.finditer(text):
        outs.add(f"o{m.group(1)}")
    for m in CLAUSE_OUTPUT_RE_NO_TYPE.finditer(text):
        outs.add(f"o{m.group(1)}")
    return sorted(outs)


def _extract_refs(text: str) -> Tuple[List[str], List[str]]:
    inputs = sorted({f"i{m.group(1)}" for m in REF_INPUT_RE.finditer(text)})
    outputs = sorted({f"o{m.group(1)}" for m in REF_OUTPUT_RE.finditer(text)})
    return inputs, outputs


def _clean_expr(expr: str) -> str:
    expr = expr.strip()
    if expr.startswith("(") and expr.endswith(")"):
        expr = expr[1:-1].strip()
    return expr


def _split_top(expr: str, op: str) -> List[str]:
    parts: List[str] = []
    buf: List[str] = []
    depth = 0
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        if depth == 0 and expr.startswith(op, i):
            parts.append("".join(buf).strip())
            buf = []
            i += len(op)
            continue
        buf.append(ch)
        i += 1
    if buf:
        parts.append("".join(buf).strip())
    return parts


def _ref_desc(token: str, doc: SpecDoc) -> str:
    if token.startswith("i"):
        desc = doc.inputs.get(token, "")
        return f"{token} ({desc})" if desc else token
    if token.startswith("o"):
        desc = doc.outputs.get(token, "")
        return f"{token} ({desc})" if desc else token
    return token


def _explain_expr(expr: str, doc: SpecDoc) -> str:
    expr = _clean_expr(expr)
    parts = _split_top(expr, "&&")
    if len(parts) > 1:
        return " and ".join(_explain_expr(p, doc) for p in parts)
    parts = _split_top(expr, "||")
    if len(parts) > 1:
        return " or ".join(_explain_expr(p, doc) for p in parts)

    func = FUNC_CALL_RE.match(expr)
    if func:
        name = func.group(1)
        phrase = PHRASE_MAP.get(name)
        if phrase:
            return phrase
    pretty = expr
    pretty = re.sub(r"\b([io]\d+)\[t\]", lambda m: _ref_desc(m.group(1), doc), pretty)
    pretty = pretty.replace("&&", " and ").replace("||", " or ")
    pretty = pretty.replace("<->", " iff ").replace("->", " implies ")
    pretty = pretty.replace("=", " equals ")
    return pretty


def _outputs_only_conjunction(expr: str) -> Optional[List[str]]:
    expr = _clean_expr(expr)
    outputs = re.findall(r"o(\d+)\[t(?:-[0-9]+)?\]", expr)
    if not outputs:
        return None
    tmp = re.sub(r"o\d+\[t(?:-[0-9]+)?\]", "", expr)
    tmp = tmp.replace("&&", "&")
    allowed = set("()&|! \t")
    if any(ch not in allowed for ch in tmp):
        return None
    return [f"o{o}" for o in outputs]


def _append_rule_notes(base: str, clause: Clause, func_name: Optional[str], doc: SpecDoc) -> str:
    notes: List[str] = []
    for o in clause.outputs:
        if o in doc.rules:
            notes.append(doc.rules[o])
    if func_name and func_name in doc.rules:
        notes.append(doc.rules[func_name])
    if not notes:
        return base
    return base + " Details: " + " ".join(notes)


def explain_clause(clause: Clause, doc: SpecDoc) -> str:
    text = clause.text
    m = CLAUSE_EQUIV_RE.search(text)
    if m:
        out = f"o{m.group(1)}"
        desc = doc.outputs.get(out, "")
        out_name = f"{out} ({desc})" if desc else out
        rhs = m.group(2).strip()
        rhs_explain = _explain_expr(rhs, doc)
        func = FUNC_CALL_RE.match(_clean_expr(rhs))
        func_name = func.group(1) if func else None
        return _append_rule_notes(f"{out_name} is true exactly when {rhs_explain}.", clause, func_name, doc)

    m = CLAUSE_BOOL_RE.search(text)
    if m:
        out = f"o{m.group(1)}"
        desc = doc.outputs.get(out, "")
        out_name = f"{out} ({desc})" if desc else out
        rhs = m.group(2).strip()
        outputs_only = _outputs_only_conjunction(rhs)
        if outputs_only:
            parts = []
            for o in outputs_only:
                parts.append(_ref_desc(o, doc))
            joined = ", ".join(parts)
            return _append_rule_notes(f"{out_name} is true when all of: {joined}.", clause, None, doc)
        rhs_explain = _explain_expr(rhs, doc)
        func = FUNC_CALL_RE.match(_clean_expr(rhs))
        func_name = func.group(1) if func else None
        return _append_rule_notes(f"{out_name} is set to {rhs_explain}.", clause, func_name, doc)

    return _explain_expr(text, doc)


def load_spec(path: Path) -> SpecDoc:
    lines = path.read_text(encoding="utf-8").splitlines()
    base_inputs, base_outputs = _parse_io_lines(lines)
    tag_inputs, tag_outputs, rules, notes = _parse_tags(lines)
    inputs = {**base_inputs, **tag_inputs}
    outputs = {**base_outputs, **tag_outputs}

    start_idx = _find_always_start(lines)
    clauses, sections = _split_clauses(lines, start_idx if start_idx >= 0 else len(lines))
    return SpecDoc(
        spec_path=str(path),
        inputs=inputs,
        outputs=outputs,
        rules=rules,
        notes=notes,
        sections=sections,
        clauses=clauses,
    )


def print_list(doc: SpecDoc) -> None:
    print(f"Spec: {doc.spec_path}")
    for clause in doc.clauses:
        section = f"[{clause.section}] " if clause.section else ""
        outs = f"{'/'.join(clause.outputs)} " if clause.outputs else ""
        preview = clause.text
        if len(preview) > 120:
            preview = preview[:117] + "..."
        print(f"{clause.index:>3}. {section}{outs}{preview}")


def print_focus(doc: SpecDoc, idx: int, explain: bool) -> None:
    if idx < 1 or idx > len(doc.clauses):
        print(f"Clause {idx} out of range (1..{len(doc.clauses)})")
        return
    clause = doc.clauses[idx - 1]
    print(f"Clause {clause.index}")
    if clause.section:
        print(f"Section: {clause.section}")
    if clause.comments:
        print("Comments:")
        for c in clause.comments:
            print(f"- {c}")
    print("Text:")
    print(clause.text)
    if clause.outputs:
        print("Outputs:")
        for o in clause.outputs:
            desc = doc.outputs.get(o, "")
            tail = f" - {desc}" if desc else ""
            print(f"- {o}{tail}")
    if clause.inputs:
        print("Inputs:")
        for i in clause.inputs:
            desc = doc.inputs.get(i, "")
            tail = f" - {desc}" if desc else ""
            print(f"- {i}{tail}")
    if clause.refs:
        print("Refs:")
        for r in clause.refs:
            if r in clause.outputs:
                continue
            desc = doc.outputs.get(r, "")
            tail = f" - {desc}" if desc else ""
            print(f"- {r}{tail}")
    for o in clause.outputs:
        if o in doc.rules:
            print(f"Rule note for {o}: {doc.rules[o]}")
    if explain:
        print("Explain:")
        print(explain_clause(clause, doc))


def print_sections(doc: SpecDoc) -> None:
    if not doc.sections:
        print("No @section tags found.")
        return
    print("Sections:")
    for s in doc.sections:
        print(f"- {s}")


def print_json(doc: SpecDoc) -> None:
    out = asdict(doc)
    print(json.dumps(out, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description="Spec Lens: readable view for Tau specs")
    parser.add_argument("spec", help="Path to .tau spec")
    parser.add_argument("--list", action="store_true", help="List all clauses (default)")
    parser.add_argument("--focus", type=int, help="Show a specific clause by number")
    parser.add_argument("--sections", action="store_true", help="List @section tags")
    parser.add_argument("--json", action="store_true", help="Emit JSON")
    parser.add_argument("--explain", action="store_true", help="Include controlled-English explanations")

    args = parser.parse_args()
    doc = load_spec(Path(args.spec))

    if args.json:
        print_json(doc)
        return
    if args.sections:
        print_sections(doc)
        return
    if args.focus:
        print_focus(doc, args.focus, args.explain)
        return

    # default: list
    if args.explain:
        print(f"Spec: {doc.spec_path}")
        for clause in doc.clauses:
            section = f"[{clause.section}] " if clause.section else ""
            explain = explain_clause(clause, doc)
            if len(explain) > 140:
                explain = explain[:137] + "..."
            print(f"{clause.index:>3}. {section}{explain}")
        return
    print_list(doc)


if __name__ == "__main__":
    main()
