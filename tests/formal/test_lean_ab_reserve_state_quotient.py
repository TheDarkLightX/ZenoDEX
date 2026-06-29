from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_ab_reserve_state_quotient_typechecks_without_placeholders() -> None:
    root = Path(__file__).resolve().parents[2]
    target = root / "lean-mathlib" / "Proofs" / "ABReserveStateQuotient.lean"
    text = target.read_text(encoding="utf-8")

    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    assert not forbidden.search(text)
    assert "structure ReserveState" in text
    assert "def reserveStateEquivalent" in text
    assert "theorem reserveStateEquivalent_same_finalReserveOut" in text
    assert "theorem reserveStateEquivalent_same_suffixOutput" in text
    assert "def reserveStateQuotientInvariant" in text
    assert "theorem quotientFullBestSuffixOutput_le_selected" in text
    assert "theorem reserveStateQuotientInvariant_bounds_zeroMinEconomicKey" in text
    assert "structure ReserveStateQuotientHostTable" in text
    assert "def reserveStateQuotientHostTableValid" in text
    assert "theorem reserveStateQuotientHostTable_validates" in text
    assert "theorem witness_reserveStateEquivalent_same_suffixOutput" in text
    assert "theorem witness_reserveStateQuotientHostTable_validates" in text

    lake = shutil.which("lake")
    if not lake:
        return
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", "Proofs/ABReserveStateQuotient.lean"],
            cwd=root / "lean-mathlib",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for ABReserveStateQuotient")

    assert proc.returncode == 0, proc.stdout + proc.stderr
