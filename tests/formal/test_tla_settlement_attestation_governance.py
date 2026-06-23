from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "formal" / "tla" / "SettlementAttestationGovernance.tla"
CFG = ROOT / "formal" / "tla" / "SettlementAttestationGovernance.cfg"
TLA_JAR = Path(os.environ.get("TLA_JAR", ROOT / "external" / "tla-tools" / "tla2tools.jar"))


@pytest.mark.skipif(not shutil.which("java"), reason="java is not available")
@pytest.mark.skipif(not TLA_JAR.is_file(), reason="tla2tools.jar is not installed")
def test_tla_settlement_attestation_governance_model_checks() -> None:
    result = subprocess.run(
        [
            shutil.which("java") or "java",
            "-XX:+UseParallelGC",
            "-cp",
            str(TLA_JAR),
            "tlc2.TLC",
            "-cleanup",
            "-config",
            str(CFG),
            str(MODEL),
        ],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    assert result.returncode == 0, result.stdout + "\n" + result.stderr
    assert "Model checking completed. No error has been found." in result.stdout
