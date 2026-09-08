"""Retained consumers for the finite asset-lane recomposition proof.

The fixture reuses the shared-projection closure, copies the exact pinned
candidate source into a fresh Lean subject, and compiles it after the existing
Std-only dependencies.  The consumers cover theorem signatures, a reachable
accepted filtered issue with complete burn/reissue tables, and semantic false
controls for row and identity loss.  They make no runtime, resource, or
publication claim.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

import pytest

from tests.formal.test_lean_asset_lane_shared_projection_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_shared_projection_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_shared_projection_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile
from tests.formal.test_lean_registered_supply_support_v1 import (
    lean as lean,
)

MODULE = "AssetLaneFiniteRecompositionV2"
NAMESPACE = f"Proofs.{MODULE}"
PROOFS = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs"
SOURCE = PROOFS / f"{MODULE}.lean"
SOURCE_SHA256 = "8ba5fdbc475acdf52261dacb55f103afca78f44ddbe28f1a57a4514716c91d5a"
OPEN = f"""open Proofs
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1 Proofs.RegisteredSupplyViewV1
open {NAMESPACE}
attribute [local instance] lexOrd
"""


@pytest.fixture(scope="module")
def finite_recomposition_lean(shared_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    captured = shared_lean.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes(source)
    checked = _compile(shared_lean, captured, shared_lean.library / "Proofs" / f"{MODULE}.olean")
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""
    return shared_lean


def _probe(subject: LeanSubject, name: str, body: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(subject, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    return checked.stdout


def test_exact_recomposition_contracts_and_standard_axioms(
    finite_recomposition_lean: LeanSubject,
) -> None:
    contracts = {
        "managed_balance_recompose": """∀ (managed : List Asset) (rows : List AmountRow)
          (asset owner : String) (deltaAtoms : Int),
          S.Unique rows → AccountsDomain rows → asset ∈ managed →
          recomposeBalances managed rows asset owner deltaAtoms =
            A.updateRows rows asset owner deltaAtoms""",
        "managed_complete_supply_recompose": """∀ (managed : List Asset) (rows : List V1SupplyRow)
          (asset : Asset) (deltaAtoms : Int),
          SourceAssetKeysUnique rows → SourceAssetKeysOrdered rows → asset ∈ managed →
          recomposeSupplies managed rows asset deltaAtoms =
            adjustComplete asset deltaAtoms rows""",
        "managed_recomposition_support": """∀ (view : SupportView) (managed : List Asset)
          (asset : Asset) (deltaAtoms : Int), CanonicalView view →
          (∀ key ∈ managed, key ∈ view.registeredAssetKeys) → asset ∈ managed →
          numericRows (recomposeSupplies managed (decode view) asset deltaAtoms) =
              adjustSparse asset deltaAtoms view.numericSupplyRows ∧
            recomposeSupplies managed (decode view) asset deltaAtoms =
              decode ⟨view.registeredAssetKeys,
                adjustSparse asset deltaAtoms view.numericSupplyRows⟩ ∧
            (recomposeSupplies managed (decode view) asset deltaAtoms).map
                V1SupplyRow.asset = view.registeredAssetKeys ∧
            CanonicalView
              ⟨view.registeredAssetKeys,
                adjustSparse asset deltaAtoms view.numericSupplyRows⟩""",
        "accepted_managed_recomposition": """∀ {view : SupportView} {managed : List Asset}
          {rows : List AmountRow} {release : String} {policy : M.Policy}
          {roots : M.RootModel} {ctx : M.Context} {command : M.Command},
          CanonicalView view →
          (∀ key ∈ managed, key ∈ view.registeredAssetKeys) →
          policy.asset ∈ managed → S.Unique rows → AccountsDomain rows →
          (M.transition roots ctx
            (A.project release policy (H.selectRows managed rows)
              (supplyFor (view.numericSupplyRows.filter
                (fun row => decide (row.asset ∈ managed))) policy.asset)) command).verdict =
            .accepted →
          A.project release policy
              (recomposeBalances managed rows command.asset command.accountOwner
                (M.signedAmount command))
              (supplyFor (numericRows (recomposeSupplies managed (decode view)
                command.asset (M.signedAmount command))) policy.asset) =
            (M.transition roots ctx
              (A.project release policy (H.selectRows managed rows)
                (supplyFor (view.numericSupplyRows.filter
                  (fun row => decide (row.asset ∈ managed))) policy.asset)) command).post""",
    }
    source_code = SOURCE.read_text()
    for name in contracts:
        assert re.search(rf"^theorem {name}\b", source_code, flags=re.MULTILINE)
    code = re.sub(r"/-.*?-/", "", source_code, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None

    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    output = _probe(finite_recomposition_lean, "RecompositionContracts", body)
    assert output.count("depends on axioms") + output.count("does not depend on any axioms") == len(
        contracts
    )
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


def test_runtime_tuple_key_consumer_has_standard_axioms(
    finite_recomposition_lean: LeanSubject,
) -> None:
    output = _probe(
        finite_recomposition_lean,
        "RuntimeTupleKeyConsumer",
        r"""
namespace RuntimeTupleKeyControls

def runtimeKey (row : AmountRow) : String × String × String :=
  (row.asset, row.owner, row.custodyDomain)

theorem runtime_key_compare (left right : AmountRow)
    (domain : left.custodyDomain = right.custodyDomain) :
    compare (runtimeKey left) (runtimeKey right) =
      compare (S.balanceWire left) (S.balanceWire right) := by
  simp [runtimeKey, S.balanceWire, lexOrd, compareLex, compareOn, domain]

theorem runtime_keys_unique (rows : List AmountRow) (unique : S.Unique rows) :
    (rows.map runtimeKey).Nodup := by
  apply List.pairwise_map.mpr
  have pairs : rows.Pairwise (fun a b => C.amountKey a ≠ C.amountKey b) :=
    List.pairwise_map.mp unique
  apply pairs.imp
  intro a b different same
  have asset := congrArg (fun key => key.1) same
  have owner := congrArg (fun key => key.2.1) same
  have domain := congrArg (fun key => key.2.2) same
  apply different
  simp only [C.amountKey, runtimeKey] at asset owner domain ⊢
  simp only [asset, owner, domain]

theorem full_recomposition_with_actual_runtime_key (managed : List Asset)
    (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique rows) (accounts : AccountsDomain rows) (selected : asset ∈ managed) :
    C.sortOn runtimeKey
      (outsideBalances managed rows ++
        A.updateRows (H.selectRows managed rows) asset owner deltaAtoms) =
      A.updateRows rows asset owner deltaAtoms := by
  have perm :
      (outsideBalances managed rows ++
        A.updateRows (H.selectRows managed rows) asset owner deltaAtoms).Perm
          (A.updateRows rows asset owner deltaAtoms) := by
    rw [← managed_balance_recompose managed rows asset owner deltaAtoms unique accounts selected]
    exact (C.sortOn_perm S.balanceWire _).symm
  apply sortOn_eq_of_perm_keys runtimeKey _ _ perm
  · exact runtime_keys_unique _ (A.updateRows_unique rows asset owner deltaAtoms unique)
  · have ordered := C.sortOn_ordered S.balanceWire
      (S.putAmount (S.accountKey asset owner)
        (C.lookupLast (S.accountKey asset owner) rows + deltaAtoms) rows)
    change (A.updateRows rows asset owner deltaAtoms).Pairwise _ at ordered
    have accountPost := updateRows_accounts rows asset owner deltaAtoms accounts
    apply ordered.imp_of_mem
    intro a b ma mb orderedAB
    rw [runtime_key_compare a b ((accountPost a ma).trans (accountPost b mb).symm)]
    exact orderedAB

#print axioms RuntimeTupleKeyControls.runtime_key_compare
#print axioms RuntimeTupleKeyControls.runtime_keys_unique
#print axioms RuntimeTupleKeyControls.full_recomposition_with_actual_runtime_key

end RuntimeTupleKeyControls
""",
    )
    assert output.count("depends on axioms") + output.count("does not depend on any axioms") == 3
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


def test_independent_reachable_issue_and_complete_table_lifecycle(
    finite_recomposition_lean: LeanSubject,
) -> None:
    _probe(
        finite_recomposition_lean,
        "RecompositionConcreteControls",
        r"""
namespace IndependentControls

namespace L
export ManagedAssetLifecycleRefinementV2 (Policy Command RootModel Context StateWellFormed
  CommandWellFormed transition signedAmount ordinaryPolicy issueCommand issueContext lifecycleRoots)
end L

def managed : List Asset := ["GBP", "USD"]

def balances : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"frank", "VND", "accounts", 11⟩]

def issue : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"alice", "USD", "accounts", 2⟩,
   ⟨"frank", "VND", "accounts", 11⟩]

def reissue : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"bob", "USD", "accounts", 1⟩,
   ⟨"frank", "VND", "accounts", 11⟩]

def complete : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 0⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def issued : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 2⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def reissued : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 1⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def policy : L.Policy :=
  { L.ordinaryPolicy with asset := "USD", assetOriginRoot := some "origin-usd" }

def command : L.Command :=
  { L.issueCommand with asset := "USD", assetOriginRoot := some "origin-usd", amountAtoms := 2 }

def view : SupportView := encode complete

def filtered : ManagedAssetLifecycleRefinementV2.LifecycleState :=
  A.project "release-v2" policy (H.selectRows managed balances)
    (supplyFor (view.numericSupplyRows.filter
      (fun row => decide (row.asset ∈ managed))) policy.asset)

theorem balances_unique : S.Unique balances := by
  unfold S.Unique
  decide

theorem balances_accounts : AccountsDomain balances := by
  simp [AccountsDomain, balances, S.accounts]

theorem complete_unique : SourceAssetKeysUnique complete := by
  unfold SourceAssetKeysUnique
  decide

theorem complete_ordered : SourceAssetKeysOrdered complete := by
  unfold SourceAssetKeysOrdered
  decide

theorem view_canonical : CanonicalView view :=
  canonical_encode complete complete_unique complete_ordered

theorem managed_covered : ∀ key ∈ managed, key ∈ view.registeredAssetKeys := by
  simp [managed, view, encode, complete]

theorem accepts_filtered_issue :
    (M.transition L.lifecycleRoots L.issueContext filtered command).verdict = .accepted := by
  decide

theorem issue_rows :
    recomposeBalances managed balances "USD" "alice" 2 = issue := by
  rw [managed_balance_recompose managed balances "USD" "alice" 2 balances_unique
    balances_accounts (by decide)]
  simp +decide [A.updateRows, balances, issue, C.lookupLast, C.amountKey, S.accountKey,
    S.putAmount, S.makeAmount, S.eraseKey, S.accounts, C.sortOn, S.balanceWire,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem burn_rows :
    recomposeBalances managed issue "USD" "alice" (-2) = balances := by
  rw [managed_balance_recompose managed issue "USD" "alice" (-2)
    (by unfold S.Unique; decide)
    (by simp [AccountsDomain, issue, S.accounts]) (by decide)]
  simp +decide [A.updateRows, balances, issue, C.amountKey, S.accountKey,
    S.putAmount, S.eraseKey, S.accounts, C.sortOn, S.balanceWire,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem reissue_rows :
    recomposeBalances managed balances "USD" "bob" 1 = reissue := by
  rw [managed_balance_recompose managed balances "USD" "bob" 1 balances_unique
    balances_accounts (by decide)]
  simp +decide [A.updateRows, balances, reissue, C.lookupLast, C.amountKey, S.accountKey,
    S.putAmount, S.makeAmount, S.eraseKey, S.accounts, C.sortOn, S.balanceWire,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem issue_supply :
    recomposeSupplies managed complete "USD" 2 = issued := by
  rw [managed_complete_supply_recompose managed complete "USD" 2 complete_unique
    complete_ordered (by decide)]
  decide

theorem burn_supply :
    recomposeSupplies managed issued "USD" (-2) = complete := by
  rw [managed_complete_supply_recompose managed issued "USD" (-2)
    (by unfold SourceAssetKeysUnique; decide)
    (by unfold SourceAssetKeysOrdered; decide) (by decide)]
  decide

theorem reissue_supply :
    recomposeSupplies managed complete "USD" 1 = reissued := by
  rw [managed_complete_supply_recompose managed complete "USD" 1 complete_unique
    complete_ordered (by decide)]
  decide

theorem burn_then_reissue :
    recomposeBalances managed (recomposeBalances managed balances "USD" "alice" 2)
        "USD" "alice" (-2) = balances ∧
      recomposeBalances managed
        (recomposeBalances managed (recomposeBalances managed balances "USD" "alice" 2)
          "USD" "alice" (-2)) "USD" "bob" 1 = reissue ∧
      recomposeSupplies managed (recomposeSupplies managed complete "USD" 2) "USD" (-2) =
        complete ∧
      recomposeSupplies managed
        (recomposeSupplies managed (recomposeSupplies managed complete "USD" 2) "USD" (-2))
        "USD" 1 = reissued := by
  rw [issue_rows, burn_rows, reissue_rows, issue_supply, burn_supply, reissue_supply]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem zero_identity_and_unrelated_rows :
    numericRows issued =
        [⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩, ⟨"USD", 2⟩, ⟨"VND", 11⟩] ∧
      numericRows complete =
        [⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩, ⟨"VND", 11⟩] ∧
      numericRows reissued =
        [⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩, ⟨"USD", 1⟩, ⟨"VND", 11⟩] ∧
      issued.map V1SupplyRow.asset = complete.map V1SupplyRow.asset ∧
      reissued.map V1SupplyRow.asset = complete.map V1SupplyRow.asset := by
  decide

theorem issue_post_matches_filtered_transition :
    A.project "release-v2" policy issue
        (supplyFor (numericRows issued) "USD") =
      (M.transition L.lifecycleRoots L.issueContext filtered command).post := by
  have materialized := accepted_managed_recomposition view_canonical managed_covered
    (show policy.asset ∈ managed by decide) balances_unique balances_accounts
    accepts_filtered_issue
  change A.project "release-v2" policy
      (recomposeBalances managed balances "USD" "alice" 2)
      (supplyFor (numericRows (recomposeSupplies managed
        (decode (encode complete)) "USD" 2)) "USD") = _ at materialized
  rw [decode_encode complete complete_unique, issue_rows, issue_supply] at materialized
  exact materialized

end IndependentControls
""",
    )


_FALSE_LAWS = (
    (
        "RecompositionMissingComplement",
        'recomposeBalances managed balances "USD" "alice" 2 = missing_complement',
        "actual_issue",
    ),
    (
        "RecompositionDuplicatedLeaf",
        'recomposeBalances managed balances "USD" "alice" 2 = duplicated_leaf',
        "actual_issue",
    ),
    (
        "RecompositionMisattributedLeaf",
        'recomposeBalances managed balances "USD" "alice" 2 = misattributed_leaf',
        "actual_issue",
    ),
    (
        "RecompositionLostZeroIdentity",
        'recomposeSupplies managed complete "USD" 2 = lost_zero_identity',
        "actual_supply",
    ),
    (
        "RecompositionDuplicatedZeroIdentity",
        'recomposeSupplies managed complete "USD" 2 = duplicated_zero_identity',
        "actual_supply",
    ),
    (
        "RecompositionWrongCompleteOrder",
        'recomposeSupplies managed complete "USD" 2 = wrong_complete_order',
        "actual_supply",
    ),
)


def _mutant_body(law: str, rewrite: str) -> str:
    return f"""
namespace Mutant

def managed : List Asset := ["GBP", "USD"]

def balances : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"frank", "VND", "accounts", 11⟩]

def issue : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"alice", "USD", "accounts", 2⟩,
   ⟨"frank", "VND", "accounts", 11⟩]

def complete : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 0⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def issued : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 2⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def missing_complement : List AmountRow :=
  [⟨"dana", "GBP", "accounts", 3⟩, ⟨"erin", "JPY", "accounts", 5⟩,
   ⟨"alice", "USD", "accounts", 2⟩, ⟨"frank", "VND", "accounts", 11⟩]

def duplicated_leaf : List AmountRow :=
  issue.take 4 ++ [⟨"alice", "USD", "accounts", 2⟩] ++ issue.drop 4

def misattributed_leaf : List AmountRow :=
  issue.map (fun row => if row.asset = "USD" then {{ row with owner := "mallory" }} else row)

def lost_zero_identity : List V1SupplyRow :=
  [⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩, ⟨"USD", 2⟩,
   ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def duplicated_zero_identity : List V1SupplyRow :=
  issued ++ [⟨"AUD", 0⟩]

def wrong_complete_order : List V1SupplyRow :=
  [⟨"ZZZ", 0⟩, ⟨"VND", 11⟩, ⟨"USD", 2⟩, ⟨"JPY", 5⟩,
   ⟨"GBP", 3⟩, ⟨"EUR", 7⟩, ⟨"AUD", 0⟩]

theorem actual_issue :
    recomposeBalances managed balances "USD" "alice" 2 = issue := by
  rw [managed_balance_recompose managed balances "USD" "alice" 2
    (by unfold S.Unique; decide)
    (by simp [AccountsDomain, balances, S.accounts]) (by decide)]
  simp +decide [A.updateRows, balances, issue, C.lookupLast, C.amountKey, S.accountKey,
    S.putAmount, S.makeAmount, S.eraseKey, S.accounts, C.sortOn, S.balanceWire,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem actual_supply :
    recomposeSupplies managed complete "USD" 2 = issued := by
  rw [managed_complete_supply_recompose managed complete "USD" 2
    (by unfold SourceAssetKeysUnique; decide)
    (by unfold SourceAssetKeysOrdered; decide) (by decide)]
  decide

example : {law} := by
  rw [{rewrite}]
  decide

end Mutant
"""


@pytest.mark.parametrize("name,law,rewrite", _FALSE_LAWS)
def test_false_recomposition_laws_fail_with_semantic_diagnostics(
    finite_recomposition_lean: LeanSubject, name: str, law: str, rewrite: str
) -> None:
    path = finite_recomposition_lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{_mutant_body(law, rewrite)}")
    checked = _compile(finite_recomposition_lean, path)
    diagnostic = checked.stdout + checked.stderr
    assert checked.returncode != 0
    assert checked.stderr == ""
    assert checked.stdout.count("error:") == 1, checked.stdout
    assert "Tactic `decide` proved that the proposition" in diagnostic
    assert "is false" in diagnostic
    assert "unexpected token" not in diagnostic
    assert "type mismatch" not in diagnostic
    assert "unknown identifier" not in diagnostic
    assert "application type mismatch" not in diagnostic
