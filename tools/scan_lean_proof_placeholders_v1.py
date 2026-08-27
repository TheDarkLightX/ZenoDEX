#!/usr/bin/env python3
"""Fail-closed placeholder scanner for Lean 4 proof files.

This is the repository-owned replacement for machine-local placeholder checks.
It differs from a naive line-regex scan in three ways that matter for
admission gating:

1.  It strips Lean comments and string literals before applying token rules, so
    ordinary prose in a doc comment (``-- we admit nothing here``) does not
    block, while a real ``sorry`` in tactic position does.
2.  ``axiom``, ``constant``, and ``unsafe`` are matched in *declaration
    position* only, after optional attributes and modifiers, so the words are
    not flagged inside identifiers or prose.
3.  Every path problem is an error, not a skip. A missing path, an explicitly
    passed non-proof file, an unreadable file, an empty or whitespace-only
    proof file, or a directory containing no proof files all exit non-zero. A
    scan that examined nothing never reports success.

Exit codes:
    0   every scanned file is clean
    1   at least one placeholder was found
    2   usage or IO error (fail closed)
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

DEFAULT_SUFFIX = ".lean"

# Optional attributes, then optional declaration modifiers, then the keyword.
_DECL_PREFIX = (
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:private|protected|scoped|local|noncomputable|nonrec)[ \t]+)*"
)

# Rules applied to comment-stripped, string-stripped Lean source.
TOKEN_RULES: dict[str, re.Pattern[str]] = {
    "lean_sorry": re.compile(r"\bsorry\b"),
    "lean_sorry_ax": re.compile(r"\bsorryAx\b"),
    "lean_admit": re.compile(r"\badmit\b"),
    "lean_native_decide": re.compile(r"\bnative_decide\b"),
    "lean_unsafe_declaration": re.compile(_DECL_PREFIX + r"unsafe\b", re.MULTILINE),
}

AXIOM_RULE_NAME = "lean_axiom_declaration"
AXIOM_RULE = re.compile(_DECL_PREFIX + r"axiom\b", re.MULTILINE)
CONSTANT_RULE_NAME = "lean_constant_declaration"
CONSTANT_RULE = re.compile(_DECL_PREFIX + r"constant\b", re.MULTILINE)


@dataclass(frozen=True)
class Match:
    path: str
    line: int
    rule: str
    snippet: str


class ScanError(Exception):
    """Raised for any condition that must fail closed."""


def strip_lean_noncode(text: str) -> str:
    """Blank out comments and string literals, preserving offsets and lines.

    Lean 4 block comments nest, and ``'`` is a legal identifier character, so
    character literals are deliberately not treated as quoting. Replaced
    characters become spaces (newlines are kept) so reported line numbers stay
    correct.
    """
    out: list[str] = []
    index = 0
    length = len(text)
    depth = 0
    in_line_comment = False
    in_string = False
    while index < length:
        char = text[index]
        pair = text[index : index + 2]
        if char == "\n":
            out.append("\n")
            in_line_comment = False
            index += 1
            continue
        if in_line_comment:
            out.append(" ")
            index += 1
            continue
        if depth > 0:
            if pair == "/-":
                depth += 1
                out.append("  ")
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                out.append("  ")
                index += 2
                continue
            out.append(" ")
            index += 1
            continue
        if in_string:
            if char == "\\" and index + 1 < length and text[index + 1] != "\n":
                out.append("  ")
                index += 2
                continue
            if char == '"':
                in_string = False
            out.append(" ")
            index += 1
            continue
        if pair == "/-":
            depth = 1
            out.append("  ")
            index += 2
            continue
        if pair == "--":
            in_line_comment = True
            out.append("  ")
            index += 2
            continue
        if char == '"':
            in_string = True
            out.append(" ")
            index += 1
            continue
        out.append(char)
        index += 1
    if depth != 0:
        raise ScanError("unterminated block comment")
    if in_string:
        raise ScanError("unterminated string literal")
    return "".join(out)


def _line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def scan_text(path: str, text: str, *, check_axioms: bool) -> list[Match]:
    code = strip_lean_noncode(text)
    raw_lines = text.splitlines()
    rules = dict(TOKEN_RULES)
    if check_axioms:
        rules[AXIOM_RULE_NAME] = AXIOM_RULE
        rules[CONSTANT_RULE_NAME] = CONSTANT_RULE
    matches: list[Match] = []
    for rule_name, pattern in rules.items():
        for found in pattern.finditer(code):
            line = _line_of(code, found.start())
            snippet = raw_lines[line - 1].strip() if line - 1 < len(raw_lines) else ""
            matches.append(Match(path=path, line=line, rule=rule_name, snippet=snippet))
    matches.sort(key=lambda item: (item.path, item.line, item.rule))
    return matches


def collect_files(paths: list[Path], *, suffix: str) -> list[Path]:
    collected: list[Path] = []
    for path in paths:
        if not path.exists():
            raise ScanError(f"path does not exist: {path}")
        if path.is_dir():
            found = sorted(p for p in path.rglob(f"*{suffix}") if p.is_file())
            if not found:
                raise ScanError(f"directory contains no {suffix} proof files: {path}")
            collected.extend(found)
            continue
        if path.suffix != suffix:
            raise ScanError(f"not a {suffix} proof file: {path}")
        collected.append(path)
    if not collected:
        raise ScanError("no proof files were scanned")
    ordered: list[Path] = []
    seen: set[Path] = set()
    for path in collected:
        resolved = path.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        ordered.append(path)
    return ordered


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Fail-closed placeholder scanner for Lean proof files.",
    )
    parser.add_argument("paths", nargs="+", help="Proof files or directories to scan")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of text")
    parser.add_argument(
        "--suffix",
        default=DEFAULT_SUFFIX,
        help=f"Proof file suffix to accept (default: {DEFAULT_SUFFIX})",
    )
    parser.add_argument(
        "--allow-axioms",
        action="store_true",
        help=(
            "Do not flag axiom or constant declarations. "
            "Unproved-declaration checking is on by default."
        ),
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    check_axioms = not args.allow_axioms
    try:
        files = collect_files([Path(p) for p in args.paths], suffix=args.suffix)
        matches: list[Match] = []
        for file_path in files:
            try:
                text = file_path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as exc:
                raise ScanError(f"cannot read {file_path}: {exc}") from exc
            if not text.strip():
                raise ScanError(f"empty or whitespace-only proof file: {file_path}")
            matches.extend(scan_text(str(file_path), text, check_axioms=check_axioms))
    except ScanError as exc:
        payload = {
            "blocked": True,
            "match_count": 0,
            "matches": [],
            "scanned_files": [],
            "axiom_check": check_axioms,
            "error": str(exc),
        }
        if args.json:
            json.dump(payload, sys.stdout, indent=2)
            sys.stdout.write("\n")
        else:
            print(f"error: {exc}", file=sys.stderr)
        return 2

    payload = {
        "blocked": bool(matches),
        "match_count": len(matches),
        "matches": [asdict(m) for m in matches],
        "scanned_files": [str(p) for p in files],
        "axiom_check": check_axioms,
        "error": None,
    }
    if args.json:
        json.dump(payload, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        for match in matches:
            print(f"{match.path}:{match.line}: {match.rule}: {match.snippet}")
        if matches:
            print(f"Found {len(matches)} placeholder blocker(s).")
        else:
            print(f"No proof placeholders found in {len(files)} file(s).")
    return 1 if matches else 0


if __name__ == "__main__":
    raise SystemExit(main())
