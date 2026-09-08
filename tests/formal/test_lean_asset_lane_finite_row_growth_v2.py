"""Derived account-row capacity; no complete resource or runtime claim."""

from __future__ import annotations

import hashlib
import re
import subprocess
from pathlib import Path

import pytest

from tests.formal.test_lean_asset_lane_finite_recomposition_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_finite_recomposition_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_finite_recomposition_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_lane_finite_recomposition_v2 import lean as lean
from tests.formal.test_lean_asset_lane_finite_recomposition_v2 import shared_lean as shared_lean
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "AssetLaneFiniteRowGrowthV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "087a35bea18666fcb51c17285ad0846cfd54501d4f9c769522300d6c8baeb4cf"
PREAMBLE = f"""import {NAMESPACE}
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open {NAMESPACE}
attribute [local instance] lexOrd
"""


@pytest.fixture(scope="module")
def row_growth_lean(finite_recomposition_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    subject = finite_recomposition_lean
    path = subject.source / "Proofs" / f"{MODULE}.lean"
    path.write_bytes(source)
    result = _compile(subject, path, subject.library / "Proofs" / f"{MODULE}.olean")
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return subject


def _consumer(subject: LeanSubject, name: str, body: str) -> subprocess.CompletedProcess[str]:
    path = subject.source / f"{name}.lean"
    path.write_text(PREAMBLE + body)
    return _compile(subject, path)


def test_exact_row_count_capacity_and_accepted_model_contracts(
    row_growth_lean: LeanSubject,
) -> None:
    contracts = {
        "updateRows_length": """∀ (rows : List AmountRow) (asset owner : String)
          (deltaAtoms : Int), S.Unique rows →
          (A.updateRows rows asset owner deltaAtoms).length +
              (if S.accountKey asset owner ∈ rows.map C.amountKey then 1 else 0) =
            rows.length +
              (if C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 then 1 else 0)""",
        "recomposeBalances_capacity_iff": """∀ (managed : List Asset) (rows : List AmountRow)
          (asset owner : String) (deltaAtoms : Int) (capacity : Nat), S.Unique rows →
          R.AccountsDomain rows → asset ∈ managed →
          ((R.recomposeBalances managed rows asset owner deltaAtoms).length ≤ capacity ↔
            rows.length +
                (if C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 then 1 else 0) ≤
              capacity + (if S.accountKey asset owner ∈ rows.map C.amountKey then 1 else 0))""",
        "account_lookup_zero_iff_absent": """∀ (rows : List AmountRow) (asset owner : String),
          S.Unique rows → S.PositiveAccounts rows →
          (C.lookupLast (S.accountKey asset owner) rows = 0 ↔
            S.accountKey asset owner ∉ rows.map C.amountKey)""",
        "full_burn_then_reissue_length": """∀ (rows : List AmountRow) (asset owner : String)
          (deltaAtoms : Int), S.Unique rows →
          0 < C.lookupLast (S.accountKey asset owner) rows → 0 < deltaAtoms →
          let burned := A.updateRows rows asset owner (-C.lookupLast (S.accountKey asset owner) rows)
          S.accountKey asset owner ∉ burned.map C.amountKey ∧
            (A.updateRows burned asset owner deltaAtoms).length = rows.length""",
        "dormant_issue_at_4096_exceeds": """∀ (managed : List Asset) (rows : List AmountRow)
          (asset owner : String) (deltaAtoms : Int), S.Unique rows → S.PositiveAccounts rows →
          asset ∈ managed → rows.length = 4096 → 0 < deltaAtoms →
          C.lookupLast (S.accountKey asset owner) rows = 0 →
          (R.recomposeBalances managed rows asset owner deltaAtoms).length = 4097 ∧
            ¬ (R.recomposeBalances managed rows asset owner deltaAtoms).length ≤ 4096""",
        "accepted_managed_recomposition_length": """∀ {managed : List Asset}
          {rows : List AmountRow} {release : String} {policy : M.Policy} {supplyAtoms : Int}
          {roots : M.RootModel} {ctx : M.Context} {command : M.Command}, S.Unique rows →
          R.AccountsDomain rows → policy.asset ∈ managed →
          (M.transition roots ctx (A.project release policy
            (Proofs.AssetLaneSharedProjectionV2.selectRows managed rows) supplyAtoms)
            command).verdict = .accepted →
          command.asset = policy.asset ∧ command.asset ∈ managed ∧
            (R.recomposeBalances managed rows command.asset command.accountOwner
              (M.signedAmount command)).length +
              (if S.accountKey policy.asset command.accountOwner ∈ rows.map C.amountKey then 1 else 0) =
            rows.length +
              (if C.lookupLast (S.accountKey policy.asset command.accountOwner) rows +
                M.signedAmount command ≠ 0 then 1 else 0)""",
    }
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    result = _consumer(row_growth_lean, "RowGrowthContracts", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    assert result.stdout.count("depends on axioms") + result.stdout.count(
        "does not depend on any axioms"
    ) == len(contracts)
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    code = re.sub(r"/-.*?-/", "", SOURCE.read_text(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


def test_independent_overflow_characterization_and_headroom(row_growth_lean: LeanSubject) -> None:
    result = _consumer(
        row_growth_lean,
        "RowGrowthOverflowConsumer",
        """
namespace IndependentCapacity
theorem overflow_iff_full_source_and_new_nonzero_key (managed : List Asset)
    (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int) (capacity : Nat)
    (unique : S.Unique rows) (accounts : R.AccountsDomain rows) (selected : asset ∈ managed)
    (sourceWithin : rows.length ≤ capacity) :
    capacity < (R.recomposeBalances managed rows asset owner deltaAtoms).length ↔
      rows.length = capacity ∧
        (owner, asset, "accounts") ∉ rows.map C.amountKey ∧
        C.lookupLast (owner, asset, "accounts") rows + deltaAtoms ≠ 0 := by
  have count := recomposeBalances_length managed rows asset owner deltaAtoms unique accounts selected
  change (R.recomposeBalances managed rows asset owner deltaAtoms).length +
      (if (owner, asset, "accounts") ∈ rows.map C.amountKey then 1 else 0) =
    rows.length + (if C.lookupLast (owner, asset, "accounts") rows + deltaAtoms ≠ 0 then 1 else 0)
    at count
  by_cases present : (owner, asset, "accounts") ∈ rows.map C.amountKey <;>
    by_cases nonzero : C.lookupLast (owner, asset, "accounts") rows + deltaAtoms ≠ 0 <;>
      simp [present, nonzero] at count ⊢ <;> omega

theorem one_row_of_headroom_suffices (managed : List Asset)
    (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int) (capacity : Nat)
    (unique : S.Unique rows) (accounts : R.AccountsDomain rows) (selected : asset ∈ managed)
    (headroom : rows.length < capacity) :
    (R.recomposeBalances managed rows asset owner deltaAtoms).length ≤ capacity := by
  have count := recomposeBalances_length managed rows asset owner deltaAtoms unique accounts selected
  split at count <;> split at count <;> omega
#print axioms IndependentCapacity.overflow_iff_full_source_and_new_nonzero_key
#print axioms IndependentCapacity.one_row_of_headroom_suffices
end IndependentCapacity
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    assert (
        result.stdout.count("depends on axioms")
        + result.stdout.count("does not depend on any axioms")
        == 2
    )
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


ROWS = """
def rows : List AmountRow :=
  [⟨"carol", "AAA", "accounts", 5⟩, ⟨"alice", "TOK", "accounts", 3⟩]
theorem unique : S.Unique rows := by unfold S.Unique; decide
theorem positive : S.PositiveAccounts rows := by unfold S.PositiveAccounts; decide
theorem accounts : R.AccountsDomain rows := fun row member => (positive row member).1
"""


def test_owner_specific_growth_and_burn_reissue_history(row_growth_lean: LeanSubject) -> None:
    result = _consumer(
        row_growth_lean,
        "RowGrowthHistory",
        ROWS
        + """
example : (R.recomposeBalances ["TOK"] rows "TOK" "bob" 1).length = 3 := by
  rw [R.managed_balance_recompose ["TOK"] rows "TOK" "bob" 1 unique accounts (by decide)]
  exact dormant_issue_length rows "TOK" "bob" 1 unique positive (by decide) (by decide)
example : (A.updateRows rows "TOK" "alice" 1).length = 2 :=
  funded_issue_length rows "TOK" "alice" 1 unique (by decide) (by decide)
example : (A.updateRows rows "TOK" "alice" (-3)).length + 1 = 2 :=
  full_burn_length rows "TOK" "alice" unique (by decide)
example : (A.updateRows rows "TOK" "alice" (-1)).length = 2 := by
  unfold A.updateRows
  rw [(C.sortOn_perm S.balanceWire _).length_eq]
  decide
example : (A.updateRows rows "TOK" "bob" 0).length = 2 := by
  unfold A.updateRows
  rw [(C.sortOn_perm S.balanceWire _).length_eq]
  decide
example : (A.updateRows (A.updateRows rows "TOK" "alice" (-3)) "TOK" "alice" 1).length = 2 :=
  (full_burn_then_reissue_length rows "TOK" "alice" 1 unique (by decide) (by decide)).2
example : (Proofs.AssetLaneSharedProjectionV2.selectRows ["TOK"] rows).length = 1 := by decide
example : (A.updateRows (Proofs.AssetLaneSharedProjectionV2.selectRows ["TOK"] rows)
    "TOK" "bob" 1).length = 2 := by
  unfold A.updateRows
  rw [(C.sortOn_perm S.balanceWire _).length_eq]
  decide
example : ¬ (R.recomposeBalances ["TOK"] rows "TOK" "bob" 1).length ≤ 2 := by
  have count := (recompose_at_capacity ["TOK"] rows "TOK" "bob" 1 2 unique positive
    (by decide) rfl (by decide)).1 (by decide)
  omega
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""


@pytest.mark.parametrize(
    "name,law",
    (
        ("WrongOwner", '(A.updateRows rows "TOK" "bob" 1).length = 2'),
        ("WrongAsset", '(A.updateRows rows "NEW" "alice" 1).length = 2'),
        (
            "DuplicateKey",
            """(A.updateRows [⟨"alice", "TOK", "accounts", 2⟩,
            ⟨"alice", "TOK", "accounts", 3⟩] "TOK" "alice" 1).length + 1 = 2 + 1""",
        ),
        (
            "StoredZero",
            """S.accountKey "TOK" "alice" ∉
            ([⟨"alice", "TOK", "accounts", 0⟩] : List AmountRow).map C.amountKey""",
        ),
        ("ZeroCreatesRow", '(A.updateRows rows "TOK" "bob" 0).length = 3'),
    ),
)
def test_kernel_rejects_missing_cardinality_premises(
    row_growth_lean: LeanSubject, name: str, law: str
) -> None:
    proof = (
        "decide"
        if name == "StoredZero"
        else ("unfold A.updateRows\n  rw [(C.sortOn_perm S.balanceWire _).length_eq]\n  decide")
    )
    result = _consumer(row_growth_lean, name, ROWS + f"\nexample : {law} := by\n  {proof}\n")
    assert result.returncode != 0
    assert result.stderr == ""
    assert result.stdout.count("error:") == 1, result.stdout
    assert "Tactic `decide` proved that the proposition" in result.stdout
    assert "is false" in result.stdout
