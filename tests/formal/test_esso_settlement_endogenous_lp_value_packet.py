from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "settlement_endogenous_lp_value_packet_v1.yaml"


def test_esso_settlement_endogenous_lp_value_packet_verifies() -> None:
    subprocess.run(["python3", "-m", "ESSO", "validate", str(MODEL)], cwd=ROOT, check=True)
    subprocess.run(
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
        cwd=ROOT,
        check=True,
    )
