#!/usr/bin/env python3
"""Check that charter-cited repo paths exist.

This is intentionally narrow: it checks backticked strings in
`docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md` that look like repo-local paths and
ignores branch names, formulas, IDs, and symbols.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CHARTER = ROOT / "docs" / "ZENODEX_MECHANISM_DESIGN_AND_MATH.md"


def _looks_like_path(text: str) -> bool:
    if "/" not in text:
        return False
    if text.startswith("codex/"):
        return False
    if any(ch in text for ch in " <>"):
        return False
    if text.startswith(("H-", "O-")):
        return False
    return text.startswith(
        (
            "docs/",
            "experiments/",
            "lean-mathlib/",
            "src/",
            "tools/",
        )
    )


def main() -> int:
    text = CHARTER.read_text(encoding="utf-8")
    missing: list[str] = []
    for match in re.finditer(r"`([^`]+)`", text):
        raw = match.group(1).strip().strip(".,;:")
        if _looks_like_path(raw) and not (ROOT / raw).exists():
            missing.append(raw)

    if missing:
        print("missing charter paths:")
        for path in sorted(set(missing)):
            print(f"  {path}")
        return 1
    print("charter grounding ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
