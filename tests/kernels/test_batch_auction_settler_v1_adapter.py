from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


MODEL = Path("src/kernels/dex/batch_auction_settler_v1.yaml")
ADAPTER = "src.kernels.python.batch_auction_settler_v1_adapter:make_adapter"
ROOT = Path(__file__).resolve().parents[2]
ESSO_ROOT = ROOT / "external" / "ESSO"


def _esso_env() -> dict[str, str]:
    env = os.environ.copy()
    if ESSO_ROOT.is_dir():
        current = env.get("PYTHONPATH")
        env["PYTHONPATH"] = str(ESSO_ROOT) if not current else f"{ESSO_ROOT}:{current}"
        return env
    if importlib.util.find_spec("ESSO") is None:
        pytest.skip("ESSO is required for batch-auction shell adapter verification")
    return env


def test_batch_auction_settler_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    env = _esso_env()
    lint_path = tmp_path / "shell_lint.json"
    verify_path = tmp_path / "shell_verify.json"

    subprocess.check_call(
        [
            sys.executable,
            "-m",
            "ESSO",
            "shell-lint",
            str(MODEL),
            "--adapter",
            ADAPTER,
            "--output",
            str(lint_path),
        ],
        env=env,
    )
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call(
        [
            sys.executable,
            "-m",
            "ESSO",
            "verify-shell",
            str(MODEL),
            "--adapter",
            ADAPTER,
            "--traces",
            "16",
            "--max-steps",
            "8",
            "--determinism-trials",
            "2",
            "--output",
            str(verify_path),
        ],
        env=env,
    )
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True
