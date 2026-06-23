from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def test_lean_exact_out_many_pool_guarded_quote_packet_compiles() -> None:
    result = subprocess.run(
        ["lake", "build", "Proofs.ZenoDEXExactOutManyPoolGuardedQuotePacket"],
        cwd=str(ROOT / "lean-mathlib"),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout
