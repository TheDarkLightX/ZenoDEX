from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path


MODEL = Path("src/kernels/dex/proof_mining_manager_v1.yaml")
ADAPTER = "src.kernels.python.proof_mining_manager_v1_adapter:make_adapter"
_ESSO_PYTHONPATH = str((Path(__file__).resolve().parents[2] / "external" / "ESSO"))


def _esso_cli_env() -> dict[str, str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH")
    env["PYTHONPATH"] = _ESSO_PYTHONPATH if not existing else f"{_ESSO_PYTHONPATH}:{existing}"
    return env


def test_proof_mining_manager_v1_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    lint_path = tmp_path / "shell_lint.json"
    verify_path = tmp_path / "shell_verify.json"

    subprocess.check_call(
        [
            "python3",
            "-m",
            "ESSO",
            "shell-lint",
            str(MODEL),
            "--adapter",
            ADAPTER,
            "--output",
            str(lint_path),
        ],
        env=_esso_cli_env(),
    )
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call(
        [
            "python3",
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
        env=_esso_cli_env(),
    )
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True
