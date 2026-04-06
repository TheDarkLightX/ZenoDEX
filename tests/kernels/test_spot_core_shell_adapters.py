from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest


CASES = [
    (
        Path("src/kernels/dex/cpmm_swap_v8.yaml"),
        "src.kernels.python.cpmm_swap_v8_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/lp_mint_v8.yaml"),
        "src.kernels.python.lp_mint_v8_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/vault_manager.yaml"),
        "src.kernels.python.vault_manager_adapter:make_adapter",
    ),
    (
        Path("src/kernels/dex/dex_step_core_v2.yaml"),
        "src.kernels.python.dex_step_core_v2_adapter:make_adapter",
    ),
]


@pytest.mark.parametrize(("model", "adapter"), CASES)
def test_spot_core_shell_adapters_shell_lint_and_verify(
    tmp_path: Path,
    model: Path,
    adapter: str,
) -> None:
    lint_path = tmp_path / f"{model.stem}_shell_lint.json"
    verify_path = tmp_path / f"{model.stem}_verify_shell.json"

    subprocess.check_call(
        [
            "python3",
            "-m",
            "ESSO",
            "shell-lint",
            str(model),
            "--adapter",
            adapter,
            "--output",
            str(lint_path),
        ]
    )
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call(
        [
            "python3",
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
        ]
    )
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True
