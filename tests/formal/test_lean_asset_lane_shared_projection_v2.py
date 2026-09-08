"""Shared-source lifecycle consumers; no complete runtime or publication claim."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

import pytest

from tests.formal.test_lean_asset_transfer_finite_accounting_v2 import SOURCE_SHA256 as TRANSFER_SHA
from tests.formal.test_lean_managed_asset_finite_accounting_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_managed_asset_registered_accounting_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile
from tests.formal.test_lean_registered_supply_support_v1 import lean as lean

MODULE = "AssetLaneSharedProjectionV2"
NAMESPACE = f"Proofs.{MODULE}"
PROOFS = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs"
SOURCE_SHA256 = "88645b58042f2272bb32898a13eeb8805403099f78f76e91143fc0f6cf08141c"
OPEN = f"""open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open {NAMESPACE}
"""


@pytest.fixture(scope="module")
def shared_lean(composition_lean: LeanSubject) -> LeanSubject:
    for name, pin in (("AssetTransferFiniteAccountingV2", TRANSFER_SHA), (MODULE, SOURCE_SHA256)):
        source = (PROOFS / f"{name}.lean").read_bytes()
        assert hashlib.sha256(source).hexdigest() == pin
        path = composition_lean.source / "Proofs" / f"{name}.lean"
        path.write_bytes(source)
        checked = _compile(
            composition_lean, path, composition_lean.library / "Proofs" / f"{name}.olean"
        )
        assert checked.returncode == 0, checked.stdout + checked.stderr
        assert checked.stdout == checked.stderr == ""
    return composition_lean


def _probe(subject: LeanSubject, name: str, body: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(subject, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    return checked.stdout


def test_exact_shared_projection_contracts_and_standard_axioms(shared_lean: LeanSubject) -> None:
    contracts = {
        "full_managed_filter_projection": """∀ (release : String) (policy : M.Policy)
          (assets : List Asset) (rows : List AmountRow) (supplies : List SupplyRow),
          policy.asset ∈ assets → S.Unique rows →
          A.project release policy (selectRows assets rows)
            (supplyFor (supplies.filter (fun row => decide (row.asset ∈ assets))) policy.asset) =
          A.project release policy rows (supplyFor supplies policy.asset)""",
        "accepted_managed_preserves_transfer_quantities": """∀ {pre : GlobalState} {keys : List Asset}
          {roots : M.RootModel} {ctx : M.Context} {release : String}
          {mp : M.Policy} {tp : T.Policy} {cmd : M.Command},
          Proofs.RegisteredSupplyViewV1.CanonicalView ⟨keys, pre.supplies⟩ → mp.asset ∈ keys →
          S.Unique pre.balances → (∀ row ∈ pre.balances, 0 ≤ row.amountAtoms) →
          M.StateWellFormed (managedView release mp pre) → M.CommandWellFormed cmd →
          (M.transition roots ctx (managedView release mp pre) cmd).verdict = .accepted →
          tp.asset = mp.asset → T.IsU128 tp.transferFeeAtoms → tp.atomDecimals = 8 →
          T.StateWellFormed (transferView release tp (afterManaged pre cmd))""",
        "accepted_transfer_preserves_managed_quantities": """∀ {pre : GlobalState}
          {roots : T.RootModel} {ctx : T.Context} {release : String}
          {tp : T.Policy} {mp : M.Policy} {cmd : T.Command}, S.Unique pre.balances →
          T.StateWellFormed (transferView release tp pre) →
          (T.transition roots ctx (transferView release tp pre) cmd).verdict = .accepted →
          tp.asset = mp.asset → M.PolicyWellFormed mp →
          M.StateWellFormed (managedView release mp (afterTransfer release tp pre cmd))""",
        "accepted_transfer_materialization": """∀ {release : String} {p : T.Policy}
          {pre : GlobalState} {cmd : T.Command} {roots : T.RootModel} {ctx : T.Context},
          S.Unique pre.balances →
          (T.transition roots ctx (transferView release p pre) cmd).verdict = .accepted →
          transferView release p (afterTransfer release p pre cmd) =
            (T.transition roots ctx (transferView release p pre) cmd).post""",
        "afterManaged_accounts_match_supply": """∀ (pre : GlobalState) (keys : List Asset)
          (cmd : M.Command), Proofs.RegisteredSupplyViewV1.CanonicalView ⟨keys, pre.supplies⟩ →
          cmd.asset ∈ keys → S.Unique pre.balances → AccountsMatchSupply pre →
          AccountsMatchSupply (afterManaged pre cmd)""",
        "afterTransfer_accounts_match_supply": """∀ (release : String) (p : T.Policy)
          (pre : GlobalState) (cmd : T.Command), S.Unique pre.balances →
          cmd.sender ≠ cmd.recipient → AccountsMatchSupply pre →
          AccountsMatchSupply (afterTransfer release p pre cmd)""",
    }
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    output = _probe(shared_lean, "SharedProjectionContracts", body)
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
    code = re.sub(r"/-.*?-/", "", (PROOFS / f"{MODULE}.lean").read_text(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


def test_fresh_and_stale_siblings_have_different_reachable_outcomes(
    shared_lean: LeanSubject,
) -> None:
    _probe(
        shared_lean,
        "SharedProjectionReachableControls",
        """
example : AccountsMatchSupply Controls.pre := Controls.account_supply_equality
example : AccountsMatchSupply (afterManaged Controls.pre Controls.issue) :=
  Controls.issued_lane_accounts_match_supply
example : (M.transition Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots
    Proofs.ManagedAssetLifecycleRefinementV2.issueContext
    (managedView "release-v2" Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy Controls.pre)
    Controls.issue).verdict = .accepted := Controls.issue_accepts
example : (T.transition Controls.transferRoots
    (Proofs.AssetTransferRefinementV2.baseContext "alice")
    (transferView "release-v2" Controls.transferPolicy (afterManaged Controls.pre Controls.issue))
    Controls.transfer).verdict = .accepted :=
  Controls.fresh_transfer_accepts_and_frozen_transfer_rejects.1
example : (T.transition Controls.transferRoots
    (Proofs.AssetTransferRefinementV2.baseContext "alice")
    (transferView "release-v2" Controls.transferPolicy Controls.pre) Controls.transfer).verdict =
    .rejected .insufficientBalance := Controls.fresh_transfer_accepts_and_frozen_transfer_rejects.2
example : (transferView "release-v2" Controls.transferPolicy
    (afterManaged Controls.pre Controls.issue)).balance "mallory" = 0 :=
  Controls.wrong_owner_has_no_issued_balance
""",
    )


@pytest.mark.parametrize(
    "name,law,proof",
    (
        (
            "FrozenSiblingLaw",
            '(transferView "release-v2" Controls.transferPolicy '
            '(afterManaged Controls.pre Controls.issue)).balance "alice" = 0',
            "rw [Controls.issued_transfer_projection]\n  decide",
        ),
        (
            "WrongOwnerLaw",
            '(transferView "release-v2" Controls.transferPolicy '
            '(afterManaged Controls.pre Controls.issue)).balance "mallory" = 1',
            "rw [Controls.issued_transfer_projection]\n  decide",
        ),
        (
            "UncoveredFilterLaw",
            'supplyFor ([⟨"ORD", 1⟩].filter '
            '(fun row : SupplyRow => decide (row.asset ∈ ([] : List Asset)))) "ORD" = 1',
            "decide",
        ),
    ),
)
def test_kernel_rejects_false_shared_projection_laws(
    shared_lean: LeanSubject, name: str, law: str, proof: str
) -> None:
    path = shared_lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}example : {law} := by\n  {proof}\n")
    checked = _compile(shared_lean, path)
    assert checked.returncode != 0
    assert checked.stdout.count("error:") == 1, checked.stdout
    assert "Tactic `decide` proved that the proposition" in checked.stdout
    assert "is false" in checked.stdout


def test_issue_transfer_burn_refreshes_the_recipient_managed_view(
    shared_lean: LeanSubject,
) -> None:
    output = _probe(
        shared_lean,
        "SharedProjectionReverseLifecycle",
        """
namespace ReviewControls

def issued : GlobalState := afterManaged Controls.pre Controls.issue
def transferred : GlobalState :=
  afterTransfer "release-v2" Controls.transferPolicy issued Controls.transfer
def burn : M.Command :=
  { Proofs.ManagedAssetLifecycleRefinementV2.burnCommand with amountAtoms := 1 }

def staleModel : M.LifecycleState :=
  ⟨"release-v2", Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy,
    fun owner => if owner = "alice" then 1 else 0, 1, 1⟩

def freshModel : M.LifecycleState :=
  ⟨"release-v2", Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy,
    Proofs.AssetTransferRefinementV2.postBalance Controls.issuedTransfer Controls.transfer, 1, 1⟩

theorem issued_unique : S.Unique issued.balances :=
  Proofs.ManagedAssetFiniteAccountingV2.updateRows_unique Controls.pre.balances
    Controls.issue.asset Controls.issue.accountOwner _ Controls.unique

theorem stale_projection :
    managedView "release-v2" Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy issued =
      staleModel := by
  exact congrArg (fun state : T.TransferState =>
    (⟨state.moduleReleaseId, Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy,
      state.balance, state.supplyAtoms, state.accountTotalAtoms⟩ : M.LifecycleState))
    Controls.issued_transfer_projection

theorem fresh_projection :
    managedView "release-v2" Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy transferred =
      freshModel := by
  have materialized := accepted_transfer_materialization issued_unique
    Controls.fresh_transfer_accepts_and_frozen_transfer_rejects.1
  dsimp only [issued] at materialized
  rw [Controls.issued_transfer_projection] at materialized
  have accepted : (T.transition Controls.transferRoots
      (Proofs.AssetTransferRefinementV2.baseContext "alice") Controls.issuedTransfer
      Controls.transfer).verdict = .accepted := by decide
  rw [(Proofs.AssetTransferRefinementV2.accepted_post_and_effects accepted).1] at materialized
  exact congrArg (fun state : T.TransferState =>
    (⟨state.moduleReleaseId, Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy,
      state.balance, state.supplyAtoms, state.accountTotalAtoms⟩ : M.LifecycleState)) materialized

/-- The finite issue -> transfer -> burn history refreshes both sibling views.
Freezing the managed view before the transfer changes the actual burn verdict. -/
theorem recipient_burn_accepts_fresh_and_rejects_frozen :
    (M.transition Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots
      Proofs.ManagedAssetLifecycleRefinementV2.issueContext
      (managedView "release-v2" Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy Controls.pre)
      Controls.issue).verdict = .accepted ∧
    (T.transition Controls.transferRoots (Proofs.AssetTransferRefinementV2.baseContext "alice")
      (transferView "release-v2" Controls.transferPolicy issued) Controls.transfer).verdict = .accepted ∧
    (M.transition Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots
      Proofs.ManagedAssetLifecycleRefinementV2.burnContext
      (managedView "release-v2" Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy transferred)
      burn).verdict = .accepted ∧
    (M.transition Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots
      Proofs.ManagedAssetLifecycleRefinementV2.burnContext
      (managedView "release-v2" Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy issued)
      burn).verdict = .rejected .insufficientBalance ∧
    freshModel.balance "bob" = 1 ∧ staleModel.balance "bob" = 0 := by
  rw [fresh_projection, stale_projection]
  exact ⟨Controls.issue_accepts, Controls.fresh_transfer_accepts_and_frozen_transfer_rejects.1,
    by decide, by decide, by decide, by decide⟩

end ReviewControls

#print axioms ReviewControls.issued_unique
#print axioms ReviewControls.stale_projection
#print axioms ReviewControls.fresh_projection
#print axioms ReviewControls.recipient_burn_accepts_fresh_and_rejects_frozen
""",
    )
    assert output.count("depends on axioms") == 4
    assert "sorryAx" not in output
