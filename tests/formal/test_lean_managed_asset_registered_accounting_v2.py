"""Independent consumers for matched finite balance and sparse supply updates.

This gate qualifies a constructed physical-accounting projection. It does not
qualify global metadata, admission, authentication or publication, and deliberately
keeps nonzero custody/reserves and an unrelated dormant identity in its controls.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

import pytest

from tests.formal.test_lean_managed_asset_finite_accounting_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile
from tests.formal.test_lean_registered_supply_support_v1 import lean as lean
from tests.formal.test_lean_registered_supply_update_v1 import SOURCE_SHA256 as UPDATE_SHA256
from tests.formal.test_lean_registered_supply_view_v1 import SOURCE_SHA256 as VIEW_SHA256

MODULE = "ManagedAssetRegisteredAccountingV2"
NAMESPACE = f"Proofs.{MODULE}"
PROOFS = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs"
SOURCE_SHA256 = "98a58eb4cc0b4ae14ece5cfac1dba0aa8c4ab31c9f11b3ff31f2dacf81aa0250"
OPEN = f"""open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1
open Proofs.RegisteredSupplyViewV1 Proofs.ManagedAssetFiniteAccountingV2 {NAMESPACE}
"""


@pytest.fixture(scope="module")
def composition_lean(accounting_lean: LeanSubject) -> LeanSubject:
    for name, digest in (
        ("RegisteredSupplyUpdateV1", UPDATE_SHA256),
        ("RegisteredSupplyViewV1", VIEW_SHA256),
        (MODULE, SOURCE_SHA256),
    ):
        source = (PROOFS / f"{name}.lean").read_bytes()
        assert hashlib.sha256(source).hexdigest() == digest
        captured = accounting_lean.source / "Proofs" / f"{name}.lean"
        captured.write_bytes(source)
        checked = _compile(
            accounting_lean, captured, accounting_lean.library / "Proofs" / f"{name}.olean"
        )
        assert checked.returncode == 0, checked.stdout + checked.stderr
        assert checked.stdout == checked.stderr == ""
    return accounting_lean


def _probe(subject: LeanSubject, name: str, body: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(subject, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    return checked.stdout


def test_independent_consumers_bind_physical_composition(composition_lean: LeanSubject) -> None:
    contracts = {
        "accountingPost_owned": """∀ (pre : GlobalState) (keys : List Asset) (a owner : String)
          (d : Int), CanonicalView ⟨keys, pre.supplies⟩ → a ∈ keys → S.Unique pre.balances →
          OwnedMatchesSupply pre → OwnedMatchesSupply (accountingPost pre a owner d)""",
        "accepted_accounting_materialization": """∀ {pre : GlobalState} {keys : List Asset}
          {roots : M.RootModel} {ctx : M.Context} {release : String} {policy : M.Policy} {cmd : M.Command},
          CanonicalView ⟨keys, pre.supplies⟩ → policy.asset ∈ keys → S.Unique pre.balances →
          (M.transition roots ctx (project release policy pre.balances
            (supplyFor pre.supplies policy.asset)) cmd).verdict = .accepted →
          project release policy (accountingPost pre cmd.asset cmd.accountOwner (M.signedAmount cmd)).balances
            (supplyFor (accountingPost pre cmd.asset cmd.accountOwner (M.signedAmount cmd)).supplies policy.asset) =
          (M.transition roots ctx (project release policy pre.balances
            (supplyFor pre.supplies policy.asset)) cmd).post""",
        "accepted_accounting_owned": """∀ {pre : GlobalState} {keys : List Asset}
          {roots : M.RootModel} {ctx : M.Context} {release : String} {policy : M.Policy} {cmd : M.Command},
          CanonicalView ⟨keys, pre.supplies⟩ → policy.asset ∈ keys → S.Unique pre.balances →
          OwnedMatchesSupply pre →
          (M.transition roots ctx (project release policy pre.balances
            (supplyFor pre.supplies policy.asset)) cmd).verdict = .accepted →
          OwnedMatchesSupply (accountingPost pre cmd.asset cmd.accountOwner (M.signedAmount cmd))""",
        "accepted_accounting_well_formed": """∀ {pre : GlobalState} {keys : List Asset}
          {roots : M.RootModel} {ctx : M.Context} {release : String} {policy : M.Policy} {cmd : M.Command},
          CanonicalView ⟨keys, pre.supplies⟩ → policy.asset ∈ keys → S.Unique pre.balances →
          (∀ row ∈ pre.balances, 0 ≤ row.amountAtoms) →
          M.StateWellFormed (project release policy pre.balances (supplyFor pre.supplies policy.asset)) →
          M.CommandWellFormed cmd →
          (M.transition roots ctx (project release policy pre.balances
            (supplyFor pre.supplies policy.asset)) cmd).verdict = .accepted →
          M.StateWellFormed (project release policy
            (accountingPost pre cmd.asset cmd.accountOwner (M.signedAmount cmd)).balances
            (supplyFor (accountingPost pre cmd.asset cmd.accountOwner (M.signedAmount cmd)).supplies policy.asset))""",
    }
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    output = _probe(composition_lean, "PhysicalCompositionContracts", body)
    assert output.count("depends on axioms") + output.count("does not depend on any axioms") == 4
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    code = re.sub(r"/-.*?-/", "", (PROOFS / f"{MODULE}.lean").read_text(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


def test_accepted_leaf_preserves_all_physical_locations_and_zero_identity(
    composition_lean: LeanSubject,
) -> None:
    _probe(
        composition_lean,
        "PhysicalCompositionNonvacuity",
        """
example : OwnedMatchesSupply (accountingPost controlPre controlIssue.asset
    controlIssue.accountOwner (M.signedAmount controlIssue)) :=
  accepted_accounting_owned control_canonical (by decide) control_unique control_owned
    issue_and_burn_acceptance_control.1
example : M.StateWellFormed (project "release-v2"
    Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy
    (accountingPost controlPre "ORD" "bob" (-1)).balances
    (supplyFor (accountingPost controlPre "ORD" "bob" (-1)).supplies "ORD")) :=
  accepted_accounting_well_formed control_canonical (by decide) control_unique
    (by intro row member; simp [controlPre, exampleRows] at member
        rcases member with rfl | rfl <;> decide)
    control_leaf_pre_well_formed ⟨by decide, by decide⟩ issue_and_burn_acceptance_control.2
example : (decode ⟨controlKeys, (accountingPost controlPre "ORD" "bob" (-1)).supplies⟩).map
    V1SupplyRow.asset = controlKeys :=
  (accountingPost_support controlPre controlKeys "ORD" "bob" (-1) control_canonical
    (by decide)).2.2.2
example : amountForAsset (accountingPost controlPre "ORD" "bob" (-1)).custody "ORD" = 1 ∧
    amountForAsset (accountingPost controlPre "ORD" "bob" (-1)).reserves "ORD" = 2 := by decide
example : ¬ OwnedMatchesSupply
    { controlPre with balances := updateRows controlPre.balances "ORD" "bob" 1
                      supplies := adjustSparse "ORD" 2 controlPre.supplies } :=
  mismatched_delta_falsifies_owned_control
example : ¬ OwnedMatchesSupply { accountingPost controlPre "ORD" "bob" (-1) with custody := [] } :=
  lost_custody_falsifies_owned_control
""",
    )


def test_kernel_refutes_lost_reserve_conservation(composition_lean: LeanSubject) -> None:
    path = composition_lean.source / "LostReserveLaw.lean"
    path.write_text(
        f"import {NAMESPACE}\n{OPEN}"
        """
example : ownedFor { accountingPost controlPre "ORD" "bob" (-1) with reserves := [] } "ORD" =
    supplyFor (accountingPost controlPre "ORD" "bob" (-1)).supplies "ORD" := by
  change amountForAsset (updateRows controlPre.balances "ORD" "bob" (-1)) "ORD" + 1 + 0 = 3
  rw [updateRows_total controlPre.balances "ORD" "bob" (-1) control_unique "ORD"]
  decide
"""
    )
    checked = _compile(composition_lean, path)
    assert checked.returncode != 0
    assert checked.stdout.count("error:") == 1, checked.stdout
    assert "Tactic `decide` proved that the proposition" in checked.stdout
    assert "is false" in checked.stdout
