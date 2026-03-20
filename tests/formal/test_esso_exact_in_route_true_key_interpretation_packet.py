from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "exact_in_route_true_key_interpretation_packet_v1.yaml"


@pytest.mark.skipif(os.environ.get("ZENO_SKIP_ESSO") == "1", reason="ESSO checks disabled")
def test_esso_exact_in_route_true_key_interpretation_packet_verifies() -> None:
    validate = subprocess.run(
        ["python3", "-m", "ESSO", "validate", str(MODEL)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert validate.returncode == 0, validate.stderr or validate.stdout

    verify = subprocess.run(
        [
            "python3",
            "-m",
            "ESSO",
            "verify-multi",
            str(MODEL),
            "--solvers",
            "z3,cvc5",
            "--determinism-trials",
            "2",
            "--timeout-ms",
            "5000",
        ],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert verify.returncode == 0, verify.stderr or verify.stdout
    combined = (verify.stdout or "") + "\n" + (verify.stderr or "")
    assert "VERIFIED" in combined, combined
