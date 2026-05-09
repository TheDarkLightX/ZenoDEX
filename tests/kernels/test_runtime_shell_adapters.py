from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
ESSO_ROOT = ROOT / "external" / "ESSO"

CASES = [
    (
        Path("src/kernels/dex/perp_epoch_isolated_v3.yaml"),
        "src.kernels.python.perp_epoch_isolated_v3_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml"),
        "src.kernels.python.perp_epoch_clearinghouse_2p_v0_1_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml"),
        "src.kernels.python.perp_epoch_clearinghouse_3p_transfer_v0_1_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/dex_global_conservation_v1.yaml"),
        "src.kernels.python.dex_global_conservation_v1_adapter:make_adapter",
    ),
]


def _esso_env() -> dict[str, str]:
    env = os.environ.copy()
    if ESSO_ROOT.is_dir():
        pythonpath = env.get("PYTHONPATH", "")
        env["PYTHONPATH"] = str(ESSO_ROOT) if not pythonpath else f"{ESSO_ROOT}:{pythonpath}"
    return env


def _require_esso(env: dict[str, str]) -> None:
    proc = subprocess.run(
        [sys.executable, "-c", "import ESSO"],
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    if proc.returncode != 0:
        pytest.skip("ESSO is not available")


@pytest.mark.parametrize(("model", "adapter"), CASES)
def test_runtime_shell_adapters_shell_lint_and_verify(
    tmp_path: Path,
    model: Path,
    adapter: str,
) -> None:
    env = _esso_env()
    _require_esso(env)
    lint_path = tmp_path / f"{model.stem}_shell_lint.json"
    verify_path = tmp_path / f"{model.stem}_verify_shell.json"

    subprocess.check_call(
        [
            sys.executable,
            "-m",
            "ESSO",
            "shell-lint",
            str(model),
            "--adapter",
            adapter,
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
            str(model),
            "--adapter",
            adapter,
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
