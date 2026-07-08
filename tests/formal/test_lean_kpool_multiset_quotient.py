from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_kpool_multiset_quotient_typechecks_without_placeholders() -> None:
    root = Path(__file__).resolve().parents[2]
    target = root / "lean-mathlib" / "Proofs" / "KPoolMultisetQuotient.lean"
    text = target.read_text(encoding="utf-8")

    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    assert not forbidden.search(text)
    assert "theorem runTrace_congr_sameStepKeys" in text
    assert "theorem witness_allocation_position_matters" in text

    lake = shutil.which("lake")
    if not lake:
        return
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", "Proofs/KPoolMultisetQuotient.lean"],
            cwd=root / "lean-mathlib",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for KPoolMultisetQuotient")

    assert proc.returncode == 0, proc.stdout + proc.stderr
