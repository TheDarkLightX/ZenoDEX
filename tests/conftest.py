from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

ESSO_ROOT = ROOT / "external" / "ESSO"
if ESSO_ROOT.is_dir():
    esso_path = str(ESSO_ROOT)
    if esso_path not in sys.path:
        sys.path.insert(0, esso_path)
    pythonpath = os.environ.get("PYTHONPATH", "")
    if esso_path not in pythonpath.split(os.pathsep):
        os.environ["PYTHONPATH"] = esso_path if not pythonpath else f"{esso_path}{os.pathsep}{pythonpath}"


def _esso_cli_available() -> bool:
    if os.environ.get("ZENO_SKIP_ESSO") == "1":
        return False
    return importlib.util.find_spec("ESSO") is not None


def pytest_collection_modifyitems(config: pytest.Config, items: list[pytest.Item]) -> None:
    if _esso_cli_available():
        return

    skip_esso = pytest.mark.skip(reason="ESSO private toolchain is not installed")
    formal_root = ROOT / "tests" / "formal"
    kernels_root = ROOT / "tests" / "kernels"
    for item in items:
        item_path = Path(str(item.fspath))
        if item_path.parent == formal_root and item_path.name.startswith("test_esso_"):
            item.add_marker(skip_esso)
        if item_path.parent == kernels_root and "shell_lint_and_verify" in item.name:
            item.add_marker(skip_esso)
