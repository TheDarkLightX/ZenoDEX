"""Finite-row theorem consumers and actual V2 leaf materialization vectors.

The proof concerns an explicit row representation of the lifecycle model.
Runtime comparisons are finite; codecs, admission ceilings, authenticated
policy selection, shared continuation and publication are separate obligations.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

import pytest

from tests.core import test_registered_supply_update_runtime_v1 as runtime
from tests.formal.test_lean_registered_supply_holdings_v1 import FORMAL_SOURCE_PINS
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile
from tests.formal.test_lean_registered_supply_support_v1 import lean as lean

MODULE = "ManagedAssetFiniteAccountingV2"
NAMESPACE = f"Proofs.{MODULE}"
PROOFS = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs"
SOURCE_SHA256 = "5c81d4caca4f02930e4c20dd432fdecb808a8460f5da11e0e4fa3ce577e50795"
DEPENDENCIES = (
    "AssetTransferRefinementV1",
    "AssetTransferCustodyCompletionV1",
    "CheckedSignedDeltaRefinementV1",
    "AssetTransferCustodyCompositionV1",
    "CheckedEconomicAggregationV1",
    "CheckedEpochEconomicTablesV1",
    "CanonicalEpochEconomicRowsV1",
    "AssetTransferSparseTablesV1",
    "AssetTransferSparseTraceV1",
    "AssetTransferSparseSupplyV1",
    "AssetTransferRefinementV2",
    "ManagedAssetLifecycleRefinementV2",
    MODULE,
)
PINS = {
    **FORMAL_SOURCE_PINS,
    "AssetTransferRefinementV2": "4401a6bb2718285768f510c91690bbff4d0928b05e2a57f6a8985379f5ff2772",
    "ManagedAssetLifecycleRefinementV2": (
        "e3054b8d7580486dadc70ad36e6ac0e3a8b4435504779421081b475acbde2983"
    ),
    MODULE: SOURCE_SHA256,
}
OPEN = f"""open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open {NAMESPACE}
"""


@pytest.fixture(scope="module")
def accounting_lean(lean: LeanSubject) -> LeanSubject:
    for name in DEPENDENCIES:
        source = (PROOFS / f"{name}.lean").read_bytes()
        assert hashlib.sha256(source).hexdigest() == PINS[name]
        captured = lean.source / "Proofs" / f"{name}.lean"
        captured.write_bytes(source)
        checked = _compile(lean, captured, lean.library / "Proofs" / f"{name}.olean")
        assert checked.returncode == 0, checked.stdout + checked.stderr
        assert checked.stdout == checked.stderr == ""
    return lean


def _probe(subject: LeanSubject, name: str, body: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(subject, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    return checked.stdout


def test_independent_consumers_bind_finite_accounting_contract(
    accounting_lean: LeanSubject,
) -> None:
    contracts = {
        "updateRows_lookup": """∀ (rows : List AmountRow) (a owner : String) (d : Int),
          S.Unique rows → ∀ qa qo : String,
          C.lookupLast (S.accountKey qa qo) (updateRows rows a owner d) =
            if a = qa ∧ owner = qo then C.lookupLast (S.accountKey qa qo) rows + d
            else C.lookupLast (S.accountKey qa qo) rows""",
        "updateRows_total": """∀ (rows : List AmountRow) (a owner : String) (d : Int),
          S.Unique rows → ∀ q : String, amountForAsset (updateRows rows a owner d) q =
            amountForAsset rows q + (if a = q then d else 0)""",
        "accepted_materialization": """∀ {roots : M.RootModel} {ctx : M.Context}
          {release : String} {policy : M.Policy} {rows : List AmountRow}
          {supply : Int} {cmd : M.Command}, S.Unique rows →
          (M.transition roots ctx (project release policy rows supply) cmd).verdict = .accepted →
          (M.transition roots ctx (project release policy rows supply) cmd).post =
            project release policy (updateRows rows cmd.asset cmd.accountOwner (M.signedAmount cmd))
              (supply + M.signedAmount cmd)""",
        "accepted_preserves_state_well_formed": """∀ {roots : M.RootModel} {ctx : M.Context}
          {release : String} {policy : M.Policy} {rows : List AmountRow}
          {supply : Int} {cmd : M.Command}, S.Unique rows →
          (∀ row ∈ rows, 0 ≤ row.amountAtoms) →
          M.StateWellFormed (project release policy rows supply) → M.CommandWellFormed cmd →
          (M.transition roots ctx (project release policy rows supply) cmd).verdict = .accepted →
          M.StateWellFormed (M.transition roots ctx (project release policy rows supply) cmd).post""",
        "accepted_rows_preserve_accounts": """∀ {roots : M.RootModel} {ctx : M.Context}
          {release : String} {policy : M.Policy} {rows : List AmountRow}
          {supply : Int} {cmd : M.Command}, S.Unique rows → S.PositiveAccounts rows →
          M.StateWellFormed (project release policy rows supply) → M.CommandWellFormed cmd →
          (M.transition roots ctx (project release policy rows supply) cmd).verdict = .accepted →
          S.Unique (updateRows rows cmd.asset cmd.accountOwner (M.signedAmount cmd)) ∧
          S.PositiveAccounts (updateRows rows cmd.asset cmd.accountOwner (M.signedAmount cmd))""",
    }
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    output = _probe(accounting_lean, "FiniteAccountingContracts", body)
    assert output.count("depends on axioms") + output.count("does not depend on any axioms") == 5
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    code = re.sub(r"/-.*?-/", "", (PROOFS / f"{MODULE}.lean").read_text(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


def test_finite_projection_excludes_the_detached_total_counterexample(
    accounting_lean: LeanSubject,
) -> None:
    _probe(
        accounting_lean,
        "FiniteAccountingCounterexample",
        """
example : M.StateWellFormed examplePre := example_pre_well_formed
example : M.StateWellFormed detachedTotal := detached_total_passes_old_quantity_premises
example : detachedTotal.accountTotalAtoms ≠ amountForAsset exampleRows "ORD" :=
  detached_total_burn_counterexample.1
example : (M.transition Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots
    Proofs.ManagedAssetLifecycleRefinementV2.burnContext detachedTotal exampleBurn).post.accountTotalAtoms
      = -1 := detached_total_burn_counterexample.2.2
example : M.StateWellFormed (M.transition Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots
    Proofs.ManagedAssetLifecycleRefinementV2.burnContext examplePre exampleBurn).post :=
  accepted_preserves_state_well_formed (by unfold S.Unique exampleRows; decide)
    (by intro row member; simp [exampleRows] at member; rcases member with rfl | rfl <;> decide)
    example_pre_well_formed ⟨by decide, by decide⟩
    full_account_burn_materializes_zero_with_other_asset_frame.1
""",
    )


@pytest.mark.parametrize(
    "name,law",
    (
        ("DroppedAccountCreation", 'amountForAsset (updateRows [] "USD" "alice" 1) "USD" = 0'),
        ("CrossAssetLeak", 'amountForAsset (updateRows exampleRows "ORD" "bob" 1) "EUR" = 8'),
        ("StaleTotal", 'amountForAsset (updateRows exampleRows "ORD" "bob" (-1)) "ORD" = 1'),
    ),
)
def test_kernel_rejects_false_materialization_laws(
    accounting_lean: LeanSubject,
    name: str,
    law: str,
) -> None:
    # Rewrite sorting away by the proved total equation before kernel evaluation.
    path = accounting_lean.source / f"{name}.lean"
    path.write_text(
        f"import {NAMESPACE}\n{OPEN}example : {law} := by\n"
        "  rw [updateRows_total _ _ _ _ (by unfold S.Unique; decide)]\n"
        "  decide\n"
    )
    checked = _compile(accounting_lean, path)
    assert checked.returncode != 0
    assert checked.stdout.count("error:") == 1, checked.stdout
    assert "Tactic `decide` proved that the proposition" in checked.stdout
    assert "is false" in checked.stdout


def test_actual_v2_leaf_balances_match_finite_materialization(accounting_lean: LeanSubject) -> None:
    body = """
def observeRows (rows : List AmountRow) (a : String) (d : Int) : String :=
  let post := updateRows rows a "alice" d
  reprStr [post.map (fun r => [r.owner, r.asset, r.custodyDomain, toString r.amountAtoms]),
    ["AAA", "MMM", "UNTOUCHED", "ZZZ"].map (fun q => [q, toString (amountForAsset post q)])]
"""
    expected = []
    for _, asset, supplies in runtime.V2_SUPPLY_GRID:
        local = runtime._v2_state(supplies, target_asset=asset, target_balance_atoms=0)
        local = runtime.ManagedAssetLifecycleStateV2(
            local.module_release_id,
            local.policies,
            tuple(
                runtime.EconomicAmountV2("bob", key, runtime.ACCOUNT_CUSTODY_DOMAIN_V2, amount)
                for key, amount in supplies
                if amount
            ),
            local.supplies,
        )
        for nonce, delta in enumerate((7, 3, -4, -6, 2), start=1):
            rows = (
                "["
                + ", ".join(
                    f"⟨{json.dumps(r.owner)}, {json.dumps(r.asset)}, {json.dumps(r.custody_domain)}, "
                    f"({r.amount_atoms} : Int)⟩"
                    for r in local.balances
                )
                + "]"
            )
            body += (
                f"#eval IO.println (reprStr (observeRows {rows} {json.dumps(asset)} ({delta})))\n"
            )
            local = runtime._v2_step(
                local,
                issue=delta > 0,
                asset=asset,
                amount_atoms=abs(delta),
                nonce=nonce,
            ).post_state
            expected.append(
                [
                    [
                        [r.owner, r.asset, r.custody_domain, str(r.amount_atoms)]
                        for r in local.balances
                    ],
                    [
                        [key, str(sum(r.amount_atoms for r in local.balances if r.asset == key))]
                        for key in runtime.REGISTERED_ASSETS_V2
                    ],
                ]
            )
    output = _probe(accounting_lean, "ActualV2FiniteRows", body)
    observed = [json.loads(json.loads(line)) for line in output.splitlines() if line.strip()]
    assert len(observed) == len(expected) == 15
    assert observed == expected
