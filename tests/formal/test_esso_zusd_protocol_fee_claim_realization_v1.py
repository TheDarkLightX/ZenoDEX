from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "zusd_protocol_fee_claim_realization_v1.yaml"
ESSO_ROOT = Path(os.environ["ESSO_ROOT"]) if os.environ.get("ESSO_ROOT") else None
ESSO_AVAILABLE = importlib.util.find_spec("ESSO") is not None or (
    ESSO_ROOT is not None and (ESSO_ROOT / "ESSO").is_dir()
)


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
def test_esso_zusd_protocol_fee_claim_realization_v1_verifies() -> None:
    env = os.environ.copy()
    if ESSO_ROOT is not None:
        prior_pythonpath = env.get("PYTHONPATH")
        env["PYTHONPATH"] = str(ESSO_ROOT) + (
            os.pathsep + prior_pythonpath if prior_pythonpath else ""
        )
    validate = subprocess.run(
        [sys.executable, "-m", "ESSO", "validate", str(MODEL)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=90,
        env=env,
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
            "5000",
        ],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=90,
        env=env,
    )
    assert verify.returncode == 0, verify.stderr or verify.stdout
    report = json.loads(verify.stdout)
    assert report["ok"] is True
    assert report["determinism"] is True
    assert report["report"]["verdict"] == "VERIFIED"
    assert report["report"]["solvers_agreed"] is True
    assert report["report"]["failed_queries"] == 0
