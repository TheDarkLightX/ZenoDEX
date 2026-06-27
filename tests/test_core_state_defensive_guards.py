from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _python_files_under(relative: str) -> list[Path]:
    return sorted((ROOT / relative).rglob("*.py"))


def test_core_and_state_runtime_code_do_not_use_strippable_asserts() -> None:
    """Consensus/runtime guards must survive `python -O`."""

    findings: list[str] = []
    for path in _python_files_under("src/core") + _python_files_under("src/state"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Assert):
                findings.append(f"{path.relative_to(ROOT)}:{node.lineno}")

    assert findings == []


def test_nonce_intent_pool_state_modules_do_not_broad_catch_exception() -> None:
    """Small state canonicalizers should only flatten expected validation errors."""

    checked = (
        ROOT / "src/state/nonces.py",
        ROOT / "src/state/intents.py",
        ROOT / "src/state/pools.py",
    )
    findings: list[str] = []
    for path in checked:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.ExceptHandler):
                caught = node.type
                if isinstance(caught, ast.Name) and caught.id == "Exception":
                    findings.append(f"{path.relative_to(ROOT)}:{node.lineno}")

    assert findings == []
