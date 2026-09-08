"""Independent theorem consumers and finite supply-update runtime observations.

This proves a complete-source representation law and compares eighteen actual
leaf steps to its executable definitions. V1 also runs the global effect
projector. V2 observations cover the local leaf only. No arbitrary-view,
accepted-global-state, authentication, publisher, or whole-runtime claim follows.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

import pytest

from tests.core import test_registered_supply_update_runtime_v1 as runtime
from tests.formal.test_lean_registered_supply_support_v1 import (
    LeanSubject,
    _compile,
)
from tests.formal.test_lean_registered_supply_support_v1 import lean as lean

MODULE = "RegisteredSupplyUpdateV1"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "3dfa40d5059e54589a9c5597e332b08b0d22c1c5b55caaccad36ecccd6ace6cb"
OPEN = """open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1
"""


@pytest.fixture(scope="module")
def update_lean(lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    captured = lean.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes(source)
    compiled = _compile(lean, captured, lean.library / "Proofs" / f"{MODULE}.olean")
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    assert compiled.stdout == compiled.stderr == ""
    return lean


def _probe(subject: LeanSubject, name: str, body: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(subject, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    return checked.stdout


def test_independent_consumers_preserve_the_update_contract(update_lean: LeanSubject) -> None:
    source = SOURCE.read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    contracts = {
        "adjustComplete_keys": """∀ (a : Asset) (d : Int) (rows : List V1SupplyRow),
          (adjustComplete a d rows).map V1SupplyRow.asset = rows.map V1SupplyRow.asset""",
        "registered_supply_adjust_commutes": """∀ (rows : List V1SupplyRow) (a : Asset)
          (d : Int), SourceAssetKeysUnique rows → SourceAssetKeysOrdered rows →
          a ∈ rows.map V1SupplyRow.asset →
          numericRows (adjustComplete a d rows) = adjustSparse a d (numericRows rows)""",
        "registered_supply_adjust_roundtrip": """∀ (rows : List V1SupplyRow) (a : Asset)
          (d : Int), SourceAssetKeysUnique rows → SourceAssetKeysOrdered rows →
          a ∈ rows.map V1SupplyRow.asset →
          decode ⟨rows.map V1SupplyRow.asset, adjustSparse a d (numericRows rows)⟩ =
          adjustComplete a d rows""",
        "registered_supply_adjust_lookup": """∀ (rows : List V1SupplyRow) (a : Asset)
          (d : Int), SourceAssetKeysUnique rows → SourceAssetKeysOrdered rows →
          a ∈ rows.map V1SupplyRow.asset → ∀ other : Asset,
          supplyFor (adjustSparse a d (numericRows rows)) other =
          supplyFor (numericRows rows) other + (if other = a then d else 0)""",
        "registered_supply_adjust_sparse_admitted": """∀ (rows : List V1SupplyRow)
          (a : Asset) (d : Int), SourceAssetKeysUnique rows → SourceAssetKeysOrdered rows →
          a ∈ rows.map V1SupplyRow.asset → SourceRowsU128 rows →
          FitsU128 (supplyFor (numericRows rows) a + d) →
          SparseSupplyRowsAdmitted (adjustSparse a d (numericRows rows)) ∧
          ((adjustSparse a d (numericRows rows)).map SupplyRow.asset).Nodup ∧
          NumericAssetKeysOrdered (adjustSparse a d (numericRows rows))""",
    }
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}" for name, signature in contracts.items()
    )
    body += "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in contracts)
    output = _probe(update_lean, "UpdateContracts", body)
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


def test_nonvacuity_and_missing_registration_have_distinct_observations(
    update_lean: LeanSubject,
) -> None:
    _probe(
        update_lean,
        "UpdateDomainControls",
        """
example : numericRows (adjustComplete "USD" 1 dormantRows) =
    adjustSparse "USD" 1 (numericRows dormantRows) :=
  registered_supply_adjust_commutes dormantRows "USD" 1
    dormant_rows_admitted.1 dormant_rows_admitted.2.1 dormant_rows_admitted.2.2.2
example : decode ⟨["USD"], adjustSparse "USD" (-7) [⟨"USD", 7⟩]⟩ =
    [⟨"USD", 0⟩] := by decide
example : numericRows (adjustComplete "USD" 1 []) ≠ adjustSparse "USD" 1 [] :=
  unknown_asset_requires_membership_control.1
example : decode ⟨[], adjustSparse "USD" 1 []⟩ =
    adjustComplete "USD" 1 (decode ⟨[], []⟩) :=
  unknown_asset_requires_membership_control.2
example : ¬ FitsU128 (maxU128 + 1) :=
  overflow_and_underflow_outside_admitted_range_control.1
example : ¬ FitsU128 (-1) :=
  overflow_and_underflow_outside_admitted_range_control.2.1
""",
    )


@pytest.mark.parametrize(
    "false_law",
    (
        'adjustSparse "USD" 1 [] = []',
        'adjustComplete "USD" (-1) [⟨"USD", 1⟩] = []',
        'numericRows (adjustComplete "USD" 1 []) = adjustSparse "USD" 1 []',
    ),
    ids=("omitted-insertion", "lost-registered-zero", "unknown-support"),
)
def test_semantic_mutant_laws_fail_the_checker(
    update_lean: LeanSubject,
    false_law: str,
) -> None:
    path = update_lean.source / "FalseUpdateLaw.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}example : {false_law} := by decide\n")
    checked = _compile(update_lean, path)
    assert checked.returncode != 0
    assert "error:" in checked.stdout
    assert "proposition" in checked.stdout and "false" in checked.stdout


def _rows_term(rows: tuple[tuple[str, int], ...]) -> str:
    return (
        "[" + ",".join(f"⟨{json.dumps(asset)}, ({amount} : Int)⟩" for asset, amount in rows) + "]"
    )


def test_compiled_updates_match_eighteen_actual_leaf_steps(update_lean: LeanSubject) -> None:
    observations = []
    for _, asset, rows in runtime.V1_SUPPLY_GRID:
        v1 = runtime._v1_state(rows, target_asset=asset, target_balance_atoms=0)
        global_v1 = runtime._v1_global_state(v1)
        v2 = runtime._v2_state(rows, target_asset=asset, target_balance_atoms=0)
        for nonce, delta in enumerate((7, -7, 2), start=1):
            pre1, pre2 = runtime._pairs_v1(v1.supplies), runtime._pairs_v2(v2.supplies)
            accepted1, global_v1 = runtime._v1_step(
                v1,
                global_v1,
                issue=delta > 0,
                asset=asset,
                amount_atoms=abs(delta),
                nonce=nonce,
            )
            accepted2 = runtime._v2_step(
                v2,
                issue=delta > 0,
                asset=asset,
                amount_atoms=abs(delta),
                nonce=nonce,
            )
            v1, v2 = accepted1.post_state, accepted2.post_state
            observations.extend(
                (
                    (
                        pre1,
                        asset,
                        delta,
                        runtime._pairs_v1(v1.supplies),
                        runtime._pairs_v1(global_v1.supplies),
                    ),
                    (
                        pre2,
                        asset,
                        delta,
                        runtime._pairs_v2(v2.supplies),
                        runtime._numeric_pairs_v2(v2.supplies),
                    ),
                )
            )
    body = """
def completeView (rows : List V1SupplyRow) : List (List String) :=
  rows.map fun row => [row.asset, toString row.amountAtoms]
def sparseView (rows : List SupplyRow) : List (List String) :=
  rows.map fun row => [row.asset, toString row.amountAtoms]
def observeUpdate (rows : List V1SupplyRow) (a : Asset) (d : Int) : String :=
  reprStr [completeView (adjustComplete a d rows),
    sparseView (adjustSparse a d (numericRows rows))]
"""
    for rows, asset, delta, _, _ in observations:
        body += (
            f"#eval IO.println (reprStr (observeUpdate {_rows_term(rows)} "
            f"{json.dumps(asset)} ({delta} : Int)))\n"
        )
    output = _probe(update_lean, "ActualLeafUpdates", body)
    actual = [json.loads(json.loads(line)) for line in output.splitlines() if line.strip()]
    expected = [
        [
            [[asset, str(amount)] for asset, amount in complete],
            [[asset, str(amount)] for asset, amount in sparse],
        ]
        for _, _, _, complete, sparse in observations
    ]
    assert len(actual) == len(expected) == 18
    assert actual == expected
