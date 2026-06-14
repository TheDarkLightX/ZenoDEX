from __future__ import annotations

import ast
from pathlib import Path


def _batch_clearing_tree() -> ast.Module:
    source_path = Path(__file__).resolve().parents[2] / "src/core/batch_clearing.py"
    return ast.parse(source_path.read_text(encoding="utf-8"))


def test_batch_clearing_has_no_bare_runtime_asserts() -> None:
    tree = _batch_clearing_tree()

    assert not [
        node.lineno
        for node in ast.walk(tree)
        if isinstance(node, ast.Assert)
    ]


def test_batch_clearing_has_no_broad_exception_handlers() -> None:
    tree = _batch_clearing_tree()

    assert not [
        node.lineno
        for node in ast.walk(tree)
        if isinstance(node, ast.ExceptHandler)
        and isinstance(node.type, ast.Name)
        and node.type.id == "Exception"
    ]
