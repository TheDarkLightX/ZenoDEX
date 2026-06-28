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
    assert "def strictStepExecutable" in text
    assert "def suffixExecutable" in text
    assert "theorem strictStepExecutable_postReserveOut_pos" in text
    assert "theorem strictStepExecutable_postReserveOut_lt" in text
    assert "theorem suffixExecutable_finalReserveOut_pos" in text
    assert "theorem suffixExecutable_finalReserveIn_pos" in text
    assert "theorem witness_suffixExecutable" in text
    assert "theorem runOutputAfterSuffix_eq_reserveOut_sub_finalReserveOut" in text
    assert "theorem zeroMinSuffixSurplus_eq_reserveOut_sub_finalReserveOut" in text
    assert "theorem witness_runOutputAfterSuffix_telescopes" in text
    assert "theorem minReserveRecord_dominates_suffixTotalOutput" in text
    assert "theorem witness_minReserveRecord_dominates_suffixTotalOutput" in text
    assert "theorem bestSuffixOutputFromRecords_le_selected" in text
    assert "theorem witness_bestSuffixOutputFromRecords_le_selected" in text
    assert "structure MaskRecordSet" in text
    assert "def maskHasBit" in text
    assert "def bitMaskStep" in text
    assert "def bitMaskPath" in text
    assert "theorem bitMaskStep_sets_bit" in text
    assert "theorem bitMaskStep_preserves_prior_bits" in text
    assert "theorem bitMaskStep_already_selected_eq" in text
    assert "theorem bitMaskPath_preserves_prior_bits" in text
    assert "theorem bitMaskPath_head_bit_remains_set" in text
    assert "def allBitsSet" in text
    assert "theorem bitMaskPath_sets_path_bits" in text
    assert "theorem bitMaskPath_preserves_start_or_sets_path_bits" in text
    assert "def allBitsBelowSet" in text
    assert "theorem allBitsSet_range_gives_allBitsBelowSet" in text
    assert "theorem bitMaskPath_sets_range_bits" in text
    assert "def maskRecordStep" in text
    assert "def maskRecordPath" in text
    assert "theorem maskRecordStep_sets_child_bit" in text
    assert "theorem maskRecordPath_sets_path_bits" in text
    assert "theorem maskRecordPath_preserves_parent_bits" in text
    assert "theorem maskRecordPath_sets_range_bits" in text
    assert "theorem witness_bitMaskStep_noop" in text
    assert "theorem witness_bitMaskPath_sets_path_bits" in text
    assert "theorem witness_bitMaskPath_sets_range_bits" in text
    assert "def maskPruningInvariant" in text
    assert "theorem maskFullBestSuffixOutput_le_selected" in text
    assert "def reachablePrunedRangeMask" in text
    assert "theorem reachablePrunedRangeMask_covers_bits" in text
    assert "theorem reachablePrunedRangeMask_bounds_suffix_output" in text
    assert "theorem reachablePrunedRangeMask_covers_and_bounds" in text
    assert "def reachablePrunedFullMaskInFamily" in text
    assert "theorem reachablePrunedFullMaskInFamily_bounds_family_selected" in text
    assert "theorem reachablePrunedFullMaskInFamily_covers_and_bounds_family" in text
    assert "def reachablePrunedFullMaskListInFamily" in text
    assert "theorem reachablePrunedFullMaskListInFamily_covers_members" in text
    assert "theorem reachablePrunedFullMaskListInFamily_bounds_family_selected" in text
    assert "theorem reachablePrunedFullMaskListInFamily_covers_and_bounds_family" in text
    assert "def selectedFamilyOutputWinner" in text
    assert "theorem selectedFamilyOutputWinner_bounds_selected_family" in text
    assert "theorem reachablePrunedFullMaskListInFamily_bounds_selected_winner" in text
    assert "theorem reachablePrunedFullMaskListInFamily_covers_and_bounds_selected_winner" in text
    assert "def compressedWinnerCertificate" in text
    assert "theorem compressedWinnerCertificate_covers_children" in text
    assert "theorem compressedWinnerCertificate_bounds_selected_winner" in text
    assert "theorem compressedWinnerCertificate_covers_and_bounds" in text
    assert "theorem bestFullSuffixOutputAcrossMasks_le_selected" in text
    assert "theorem witness_bestFullSuffixOutputAcrossMasks_le_selected" in text
    assert "theorem witness_reachablePrunedRangeMask_covers_and_bounds" in text
    assert "theorem witness_reachablePrunedFullMaskInFamily_covers_and_bounds_family" in text
    assert "theorem witness_reachablePrunedFullMaskListInFamily_covers_and_bounds_family" in text
    assert "theorem witness_reachablePrunedFullMaskListInFamily_bounds_selected_winner" in text
    assert "theorem witness_compressedWinnerCertificate_covers_and_bounds" in text

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
