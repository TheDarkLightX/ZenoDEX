from __future__ import annotations

import ast
from pathlib import Path


def test_batch_clearing_has_no_bare_runtime_asserts() -> None:
    source_path = Path(__file__).resolve().parents[2] / "src/core/batch_clearing.py"
    tree = ast.parse(source_path.read_text(encoding="utf-8"))

    assert not [
        node.lineno
        for node in ast.walk(tree)
        if isinstance(node, ast.Assert)
    ]
