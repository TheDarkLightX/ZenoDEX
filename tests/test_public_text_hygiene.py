from __future__ import annotations

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
)

FORBIDDEN_SNIPPETS = (
    "Standard " + "reading",
    "/home/" + "trevormoc",
    "/workspace" + "/",
    "/workspace" + "/" + "ZenoDEX",
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

    assert hits == []
