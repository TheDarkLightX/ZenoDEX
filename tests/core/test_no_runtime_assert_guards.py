from __future__ import annotations

import ast
from pathlib import Path

CORE_RUNTIME_ASSERT_FREE_FILES = (
    Path("src/core/batch_clearing.py"),
    Path("src/core/homological_arbitrage.py"),
    Path("src/core/settlement_strong_validator.py"),
    Path("src/core/split_routing.py"),
    Path("src/core/split_routing_dispatch.py"),
)


def test_core_value_moving_hotspots_do_not_use_runtime_assert_guards() -> None:
    """
    Runtime `assert` statements are stripped by `python -O`.

    These files sit on value-moving or routing decision paths, so internal
    invariants must be explicit checks, deterministic rejects, or deterministic
    errors that survive optimized execution.
    """

    offenders: list[str] = []
    for path in CORE_RUNTIME_ASSERT_FREE_FILES:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Assert):
                offenders.append(f"{path}:{node.lineno}")

    assert offenders == []
