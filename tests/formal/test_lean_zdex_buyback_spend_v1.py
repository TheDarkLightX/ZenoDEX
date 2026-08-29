from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_zdex_buyback_spend_v1_builds_without_placeholders() -> None:
    proof_path = ROOT / "lean-mathlib" / "Proofs" / "ZDEXBuybackSpendV1.lean"
    proof_source = proof_path.read_text(encoding="utf-8")

    assert "sorry" not in proof_source
    assert "admit" not in proof_source
    subprocess.run(
        ["lean", str(proof_path)],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
