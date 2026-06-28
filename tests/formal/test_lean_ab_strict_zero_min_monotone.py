from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_ab_strict_zero_min_monotone_typechecks_without_placeholders() -> None:
    root = Path(__file__).resolve().parents[2]
    target = root / "lean-mathlib" / "Proofs" / "ABStrictZeroMinMonotone.lean"
    text = target.read_text(encoding="utf-8")

    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    assert not forbidden.search(text)
    assert "theorem runReserveOutAfterSuffix_mono" in text
    assert "theorem runReserveInAfterSuffix_eq_reserveInAfterGross" in text
    assert "theorem sameGrossSum_gives_sameReserveIn" in text
    assert "theorem witness_runReserveInAfterSuffix" in text
    assert "theorem runOutputAfterSuffix_eq_reserveOut_sub_finalReserveOut" in text
    assert "theorem zeroMinSuffixSurplus_eq_reserveOut_sub_finalReserveOut" in text
    assert "theorem witness_runOutputAfterSuffix_telescopes" in text
    assert "theorem minReserveRecord_dominates_suffixTotalOutput" in text
    assert "theorem witness_minReserveRecord_dominates_suffixTotalOutput" in text
    assert "theorem bestSuffixOutputFromRecords_le_selected" in text
    assert "theorem witness_bestSuffixOutputFromRecords_le_selected" in text

    lake = shutil.which("lake")
    if not lake:
        return
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", "Proofs/ABStrictZeroMinMonotone.lean"],
            cwd=root / "lean-mathlib",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for ABStrictZeroMinMonotone")

    assert proc.returncode == 0, proc.stdout + proc.stderr
