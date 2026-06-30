from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_kpool_split_concavity_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/KPoolSplitConcavity.lean"
    source = lean_dir / target
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
    combined = (proc.stdout + proc.stderr).lower()
    assert "sorry" not in combined, f"sorry placeholder found in {target}"
    assert "error:" not in combined, f"error in {target}: {proc.stderr}"
    text = source.read_text(encoding="utf-8")
    assert "FixedPoolTermCont" in text
    assert "splitFunctionListCoordSliceCont_concave" in text
    assert "selectedFullPoolListCont" in text
    assert "selectedFullPoolListCont_eq_take_drop_of_lt" in text
    assert "selectedFullPoolListOrderedCont_remainderBeforeActive_eq_take_drop_of_lt" in text
    assert "splitFunctionSelectedListCoordSliceCont_eq_listCoordSliceCont" in text
    assert "splitFunctionSelectedListCoordSliceCont_concave" in text
    assert "fixedPoolInputSumCont_perm" in text
    assert "fixedPoolOutputSumCont_perm" in text
    assert "splitFunctionListCoordSliceCont_eq_of_perm_fixed" in text
    assert "SelectedPoolOrderCont" in text
    assert "selectedFullPoolListOrderedCont" in text
    assert "selectedActiveIndexOrderedCont" in text
    assert "selectedRemainderIndexOrderedCont" in text
    assert "selectedActiveIndexOrderedCont_lt" in text
    assert "selectedRemainderIndexOrderedCont_lt" in text
    assert "selectedFullPoolListOrderedCont_get_active" in text
    assert "selectedFullPoolListOrderedCont_get_remainder" in text
    assert "selectedActiveIndexOrderedCont_ne_remainderIndex" in text
    assert "selectedFixedPoolListOrderedCont" in text
    assert "selectedRemainderIndexAfterActiveEraseOrderedCont" in text
    assert "selectedFullPoolListOrderedCont_erase_active_then_remainder_eq_fixed" in text
    assert "selectedFullPoolListCont_erase_active_then_remainder_eq_take_drop_of_lt" in text
    assert (
        "selectedFullPoolListOrderedCont_remainderBeforeActive_erase_active_then_remainder_eq_take_drop_of_lt"
        in text
    )
    assert "splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont" in text
    assert "splitFunctionSelectedListOrderedCoordSliceCont_concave" in text
    assert "splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont_of_perm_fixed" in text
    assert "splitFunctionSelectedListOrderedCoordSliceCont_concave_of_perm_fixed" in text
    assert "UnorderedSelectionCertificateCont" in text
    assert "unorderedSelectionCertificate_full_eq" in text
    assert "unorderedSelectionCertificate_fixed_perm" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_eq_listCoordSliceCont" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave" in text
    assert "unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont" in text
    assert "unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_activeBeforeRemainderIndex" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_remainderBeforeActiveIndex" in text
    assert "IdentifiedFixedPoolTermCont" in text
    assert "identifiedPoolTermsCont_perm" in text
    assert "IdentifiedActiveBeforeRemainderSelectionCont" in text
    assert "IdentifiedRemainderBeforeActiveSelectionCont" in text
    assert "identifiedActiveBeforeRemainderSelection_ids_distinct" in text
    assert "identifiedRemainderBeforeActiveSelection_ids_distinct" in text
    assert "unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont" in text
    assert "unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedActiveBeforeRemainder" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedRemainderBeforeActive" in text
    assert "IdOrderedIdentifiedPoolPresentationCont" in text
    assert "idOrderedIdentifiedPoolPresentation_ids_distinct" in text
    assert "identifiedActiveBeforeRemainderSelectionOfIdOrderedCont" in text
    assert "identifiedRemainderBeforeActiveSelectionOfIdOrderedCont" in text
    assert "unorderedSelectionCertificateOfIdOrderedActiveBeforeRemainderCont" in text
    assert "unorderedSelectionCertificateOfIdOrderedRemainderBeforeActiveCont" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_idOrderedActiveBeforeRemainder" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_idOrderedRemainderBeforeActive" in text
    assert "StableIdSortedPresentationCertificateCont" in text
    assert "stableIdSortedPresentationCertificate_erased_perm" in text
    assert "stableIdSortedPresentationCertificate_ids_distinct" in text
    assert "identifiedActiveBeforeRemainderSelectionOfStableIdSortedCertCont" in text
    assert "identifiedRemainderBeforeActiveSelectionOfStableIdSortedCertCont" in text
    assert "unorderedSelectionCertificateOfStableIdSortedActiveBeforeRemainderCont" in text
    assert "unorderedSelectionCertificateOfStableIdSortedRemainderBeforeActiveCont" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_stableIdSortedActiveBeforeRemainder" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_stableIdSortedRemainderBeforeActive" in text
    assert "stableIdSortedPoolsCont" in text
    assert "stableIdSortedPoolsCont_perm" in text
    assert "stableIdSortedPoolsCont_pairwise_id_le" in text
    assert "stableIdSortedPoolsCont_ids_strict" in text
    assert "stableIdSortedPoolsCont_pairwise_id_lt" in text
    assert "stableIdSortedPoolsCont_eq_of_perm_unique_ids" in text
    assert "stableIdMergeSortPresentationCont" in text
    assert "stableIdMergeSortPresentationCont_pools_eq_of_perm_unique_ids" in text
    assert "stableIdMergeSortPresentationCertificateCont" in text
    assert "stableIdMergeSortPresentationCertificate_output_pools_eq_of_perm_unique_ids" in text
    assert "stableIdMergeSortPresentationCertificate_erased_perm" in text
    assert "unorderedSelectionCertificateOfStableIdMergeSortActiveBeforeRemainderCont" in text
    assert "unorderedSelectionCertificateOfStableIdMergeSortRemainderBeforeActiveCont" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_stableIdMergeSortActiveBeforeRemainder" in text
    assert "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_stableIdMergeSortRemainderBeforeActive" in text
    assert "IdentifiedFinsetPresentationCont" in text
    assert "identifiedFinsetToList" in text
    assert "identifiedFinsetToList_ids_nodup" in text
    assert "identifiedFinsetToList_perm_of_eq_ids" in text
    assert "stableIdSortedPoolsCont_eq_of_finset_eq" in text
    assert "splitFunctionConcave_of_finsetActiveBeforeRemainder" in text
    assert "splitFunctionConcave_of_finsetRemainderBeforeActive" in text
    assert "IdentifiedMultisetPresentationCont" in text
    assert "identifiedMultisetToList" in text
    assert "identifiedMultisetToList_ids_nodup" in text
    assert "identifiedMultisetToList_perm_of_eq" in text
    assert "stableIdSortedPoolsCont_eq_of_multiset_eq" in text
    assert "stableIdMergeSortPresentationCertificate_output_pools_eq_of_multiset_eq" in text
    assert "splitFunctionConcave_of_multisetActiveBeforeRemainder" in text
    assert "splitFunctionConcave_of_multisetRemainderBeforeActive" in text
    assert "stableIdSortedPoolsCont_index_lt_of_id_lt" in text
    assert "MultisetStableIdActiveBeforeRemainderSelectionCont" in text
    assert "MultisetStableIdRemainderBeforeActiveSelectionCont" in text
    assert "multisetStableIdActiveBeforeRemainderSelection_index_order" in text
    assert "multisetStableIdRemainderBeforeActiveSelection_index_order" in text
    assert "StableIdSortedLookupWitnessCont" in text
    assert "stableIdSortedLookupWitness_index_unique" in text
    assert "stableIdSortedLookupWitness_index_lt_of_id_lt" in text
    assert "MultisetStableIdLookupActiveBeforeRemainderSelectionCont" in text
    assert "MultisetStableIdLookupRemainderBeforeActiveSelectionCont" in text
    assert "multisetStableIdActiveBeforeRemainderSelectionOfLookupCont" in text
    assert "multisetStableIdRemainderBeforeActiveSelectionOfLookupCont" in text
    assert "multisetStableIdLookupActiveBeforeRemainderSelection_index_order" in text
    assert "multisetStableIdLookupRemainderBeforeActiveSelection_index_order" in text
    assert "unorderedSelectionCertificateOfMultisetStableIdActiveBeforeRemainderCont" in text
    assert "unorderedSelectionCertificateOfMultisetStableIdRemainderBeforeActiveCont" in text
    assert "unorderedSelectionCertificateOfMultisetStableIdLookupActiveBeforeRemainderCont" in text
    assert "unorderedSelectionCertificateOfMultisetStableIdLookupRemainderBeforeActiveCont" in text
    assert (
        "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_multisetStableIdActiveBeforeRemainder"
        in text
    )
    assert (
        "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_multisetStableIdRemainderBeforeActive"
        in text
    )
    assert (
        "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_multisetStableIdLookupActiveBeforeRemainder"
        in text
    )
    assert (
        "splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_multisetStableIdLookupRemainderBeforeActive"
        in text
    )
    assert "splitFunction5PoolCont_concave_coord3" in text
