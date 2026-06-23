from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROOFS_ROOT = ROOT / "lean-mathlib"


def test_lean_tau_tcp_view_contracts_compiles() -> None:
    result = subprocess.run(
        ["lake", "build", "Proofs.ZenoDEXTauTcpViewContracts"],
        cwd=PROOFS_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout
