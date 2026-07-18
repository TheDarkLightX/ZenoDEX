from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
MODEL = (
    ROOT
    / "src"
    / "kernels"
    / "dex"
    / "generic_token_authority_composition_v1.yaml"
)


def _esso_environment() -> dict[str, str]:
    environment = os.environ.copy()
    esso_root = ROOT / "external" / "ESSO"
    existing = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = (
        str(esso_root) if not existing else f"{esso_root}:{existing}"
    )
    return environment


@pytest.mark.skipif(
    os.environ.get("ZENO_SKIP_ESSO") == "1",
    reason="ESSO checks disabled",
)
def test_esso_generic_token_composition_is_deterministically_inductive() -> None:
    environment = _esso_environment()
    validate = subprocess.run(
        [sys.executable, "-m", "ESSO", "validate", str(MODEL)],
        cwd=ROOT,
        env=environment,
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )
    assert validate.returncode == 0, validate.stderr or validate.stdout

    verify = subprocess.run(
        [
            sys.executable,
            "-m",
            "ESSO",
            "verify-multi",
            str(MODEL),
            "--solvers",
            "z3,cvc5",
            "--determinism-trials",
            "2",
            "--timeout-ms",
            "10000",
        ],
        cwd=ROOT,
        env=environment,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    combined = (verify.stdout or "") + "\n" + (verify.stderr or "")
    assert verify.returncode == 0, combined
    assert '"verdict": "VERIFIED"' in combined
    assert '"solvers_agreed": true' in combined
    assert '"determinism": true' in combined
