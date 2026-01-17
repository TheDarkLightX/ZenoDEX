from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


def test_lean_rounding_file_typechecks() -> None:
    lean = shutil.which("lean")
    if not lean:
        # Optional dev dependency; skip in environments without Lean.
        return
    root = Path(__file__).resolve().parents[2]
    target = root / "formal" / "rounding.lean"
    proc = subprocess.run([lean, str(target)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr

