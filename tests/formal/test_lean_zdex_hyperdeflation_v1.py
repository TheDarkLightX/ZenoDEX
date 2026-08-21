from __future__ import annotations

import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_zdex_hyperdeflation_v1_builds_without_placeholders() -> None:
    proof_path = ROOT / "lean-mathlib" / "Proofs" / "ZDEXHyperdeflationV1.lean"
    proof_source = proof_path.read_text(encoding="utf-8")
    lean_project = Path(
        os.environ.get("ZENODEX_LEAN_PROJECT_ROOT", ROOT / "lean-mathlib")
    )

    assert "sorry" not in proof_source
    assert "admit" not in proof_source
    subprocess.run(
        ["lake", "env", "lean", str(proof_path)],
        cwd=lean_project,
        check=True,
    )
