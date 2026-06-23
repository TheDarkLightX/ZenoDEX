from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

SEARCH_GLOBS = (
    "README.md",
    "docs/**/*.md",
    "docs/**/*.tex",
    "lean-mathlib/Proofs/**/*.lean",
    "src/**/*.md",
    "src/**/*.py",
    "tests/**/*.py",
    "tools/**/*.py",
    "internal/**/*.json",
)

FORBIDDEN_SNIPPETS = (
    "Standard " + "reading",
    "/workspace" + "/",
    "/workspace" + "/" + "ZenoDEX",
)

# Reject any absolute /home/<user>/ path in tracked text surfaces —
# machine-specific paths must never be committed.
FORBIDDEN_PATTERNS = (
    r"/home/[a-zA-Z0-9_]+/",
)


def _iter_text_paths() -> list[Path]:
    paths: set[Path] = set()
    for pattern in SEARCH_GLOBS:
        paths.update(path for path in ROOT.glob(pattern) if path.is_file())
    return sorted(paths)


def test_public_text_surfaces_do_not_leak_local_workspace_or_old_gloss() -> None:
    hits: list[str] = []
    for path in _iter_text_paths():
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT)
        for snippet in FORBIDDEN_SNIPPETS:
            if snippet in text:
                hits.append(f"{rel}: contains {snippet!r}")
        for pattern in FORBIDDEN_PATTERNS:
            for match in re.finditer(pattern, text):
                # Allow /home/ in this test file itself (the pattern definition).
                if rel == Path("tests/test_public_text_hygiene.py"):
                    continue
                hits.append(f"{rel}: matches {pattern!r} at {match.start()}: {match.group()!r}")

    assert hits == []
