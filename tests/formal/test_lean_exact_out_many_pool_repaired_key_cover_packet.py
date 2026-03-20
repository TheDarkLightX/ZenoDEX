from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LEAN_FILE = ROOT / "lean-mathlib" / "Proofs" / "ZenoDEXExactOutManyPoolRepairedKeyCoverPacket.lean"


def test_lean_exact_out_many_pool_repaired_key_cover_packet_compiles() -> None:
    result = subprocess.run(
        ["lake", "env", "lean", str(LEAN_FILE.relative_to(ROOT / "lean-mathlib"))],
        cwd=str(ROOT / "lean-mathlib"),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout
