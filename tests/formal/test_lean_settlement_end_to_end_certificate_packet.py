from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROOFS_ROOT = ROOT / "lean-mathlib"


def test_lean_settlement_end_to_end_certificate_packet_compiles() -> None:
    result = subprocess.run(
        ["lake", "build", "Proofs.ZenoDEXSettlementEndToEndCertificatePacket"],
        cwd=PROOFS_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout
