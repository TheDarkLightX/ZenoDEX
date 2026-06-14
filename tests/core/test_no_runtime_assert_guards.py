from __future__ import annotations

import ast
from pathlib import Path

AUTHORITY_RUNTIME_ASSERT_FREE_FILES = (
    Path("src/integration/settlement_signer_registry.py"),
    Path("src/integration/zeno_key_manager.py"),
    Path("src/integration/zenodex_external_threshold_bls.py"),
)


def _assert_files_have_no_runtime_asserts(paths: tuple[Path, ...]) -> None:
    offenders: list[str] = []
    for path in paths:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Assert):
                offenders.append(f"{path}:{node.lineno}")

    assert offenders == []


def test_core_value_moving_code_does_not_use_runtime_assert_guards() -> None:
    """
    Runtime `assert` statements are stripped by `python -O`.

    Core code sits on value-moving or routing decision paths, so internal
    invariants must be explicit checks, deterministic rejects, or deterministic
    errors that survive optimized execution.
    """

    core_paths = tuple(sorted(Path("src/core").glob("*.py")))

    _assert_files_have_no_runtime_asserts(core_paths)


def test_authority_hotspots_do_not_use_runtime_assert_guards() -> None:
    """Key/signature authority checks must fail explicitly under optimized Python."""

    _assert_files_have_no_runtime_asserts(AUTHORITY_RUNTIME_ASSERT_FREE_FILES)
