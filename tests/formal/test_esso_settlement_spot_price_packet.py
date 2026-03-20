from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "settlement_spot_price_packet_v1.yaml"


@pytest.mark.skipif(importlib.util.find_spec("ESSO") is None, reason="ESSO is not available")
def test_esso_settlement_spot_price_packet_verifies() -> None:
    result = subprocess.run(
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
    )
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report["ok"] is True
    assert report["determinism"] is True
    assert report["report"]["verdict"] == "VERIFIED"
    assert report["report"]["solvers_agreed"] is True
    assert report["report"]["failed_queries"] == 0
    assert report["queries"]["init_implies_inv"]["final_result"] == "unsat"
    assert report["queries"]["inductive_rebuild_packet"]["final_result"] == "unsat"
