#!/usr/bin/env python3
from __future__ import annotations

import argparse
import io
import sys
import tokenize
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TARGETS = ("src", "tests", "tools", ".github")
SCANNED_SUFFIXES = {".py", ".sh", ".yaml", ".yml", ".json", ".toml", ".md"}
BANNED_DIR_NAMES = {"node_modules", ".venv", "external", "internal", "generated", "runs"}
BIDI_AND_FORMAT_CONTROLS = {
    "\u061c",
    "\u200e",
    "\u200f",
    "\u202a",
    "\u202b",
    "\u202c",
    "\u202d",
    "\u202e",
    "\u2066",
    "\u2067",
    "\u2068",
    "\u2069",
}


def _iter_target_files(targets: list[str]) -> list[Path]:
    files: list[Path] = []
    for raw_target in targets:
        candidate = (ROOT / raw_target).resolve()
        if not candidate.exists():
            continue
        if candidate.is_file():
            if candidate.suffix in SCANNED_SUFFIXES:
                files.append(candidate)
            continue
        for path in sorted(candidate.rglob("*")):
            if any(part in BANNED_DIR_NAMES for part in path.parts):
                continue
            if path.is_file() and path.suffix in SCANNED_SUFFIXES:
                files.append(path)
    return files


def _has_suspicious_control(ch: str) -> bool:
    return ch in BIDI_AND_FORMAT_CONTROLS or unicodedata.category(ch) == "Cf"


def _scan_controls(path: Path, text: str) -> list[str]:
    issues: list[str] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        for colno, ch in enumerate(line, start=1):
            if _has_suspicious_control(ch):
                issues.append(
                    f"{path.relative_to(ROOT)}:{lineno}:{colno}: disallowed Unicode format/control char U+{ord(ch):04X}"
                )
    return issues


def _scan_python_identifiers(path: Path, text: str) -> list[str]:
    issues: list[str] = []
    reader = io.StringIO(text).readline
    try:
        tokens = tokenize.generate_tokens(reader)
    except tokenize.TokenError as exc:
        return [f"{path.relative_to(ROOT)}:1:1: failed to tokenize for Unicode safety scan: {exc}"]

    for tok in tokens:
        if tok.type != tokenize.NAME:
            continue
        if tok.string.isascii():
            continue
        normalized = unicodedata.normalize("NFKC", tok.string)
        issues.append(
            f"{path.relative_to(ROOT)}:{tok.start[0]}:{tok.start[1] + 1}: non-ASCII identifier '{tok.string}' "
            f"(NFKC='{normalized}') is not allowed"
        )
    return issues


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Fail-closed scan for Unicode source hazards. Rejects bidi/format-control characters in scanned "
            "source/config files and rejects non-ASCII Python identifiers."
        )
    )
    parser.add_argument("targets", nargs="*", default=list(DEFAULT_TARGETS))
    args = parser.parse_args(argv)

    issues: list[str] = []
    for path in _iter_target_files(args.targets):
        text = path.read_text(encoding="utf-8")
        issues.extend(_scan_controls(path, text))
        if path.suffix == ".py":
            issues.extend(_scan_python_identifiers(path, text))

    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        print(
            f"error: Unicode safety scan found {len(issues)} issue(s); remove bidi/control chars and non-ASCII Python identifiers",
            file=sys.stderr,
        )
        return 1

    print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
