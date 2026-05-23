from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_disaster_class_closure_builds() -> None:
    subprocess.run(
        [
            "lake",
            "env",
            "lean",
            "Proofs/DisasterClassClosure.lean",
        ],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
