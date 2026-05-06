from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "zusd_oracle_recovery_lifecycle_v1.yaml"
ESSO_AVAILABLE = importlib.util.find_spec("ESSO") is not None


def test_esso_zusd_oracle_recovery_public_replay_accepts() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_oracle_esso_zusd_recovery_replay.py",
            "--format",
            "json",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.esso_zusd_recovery_replay.v1"
    assert receipt["status"] == "accepted"
    assert receipt["assignment_count"] == 256
    assert receipt["assignment_mismatch_count"] == 0
    assert receipt["witness_case_count"] == 10
    assert receipt["failed_witness_count"] == 0


@pytest.mark.skipif(os.environ.get("ZENO_SKIP_ESSO") == "1", reason="ESSO checks disabled")
def test_esso_zusd_oracle_recovery_lifecycle_v1_verifies() -> None:
    if not ESSO_AVAILABLE:  # pragma: no cover
        pytest.skip("ESSO verification toolchain not installed")
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
