"""Independent consumers for arbitrary covered sparse-supply reconstruction.

The canonical input predicate is pinned to raw input facts. No consumer supplies
a decoded source-image equality or a desired post-state. Runtime update vectors
remain in test_lean_registered_supply_update_v1.py; this gate adds representation
completeness and reusable canonical-support closure, without authentication.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

import pytest

from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile
from tests.formal.test_lean_registered_supply_support_v1 import lean as lean
from tests.formal.test_lean_registered_supply_update_v1 import update_lean as update_lean

MODULE = "RegisteredSupplyViewV1"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "8bcdf3ab4444bbb96ad41c304eec6d35fb042528a81311e63616c00ba519ee1f"
OPEN = f"""open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1 {NAMESPACE}
"""


@pytest.fixture(scope="module")
def view_lean(update_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    captured = update_lean.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes(source)
    checked = _compile(update_lean, captured, update_lean.library / "Proofs" / f"{MODULE}.olean")
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""
    return update_lean


def _probe(subject: LeanSubject, name: str, body: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(subject, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    return checked.stdout


def test_arbitrary_view_contract_has_only_raw_input_premises(view_lean: LeanSubject) -> None:
    contracts = {
        "encode_decode": """∀ (v : SupportView), CanonicalView v → encode (decode v) = v""",
        "arbitrary_view_adjust_commutes": """∀ (v : SupportView), CanonicalView v →
          ∀ (a : Asset) (d : Int), a ∈ v.registeredAssetKeys →
          numericRows (adjustComplete a d (decode v)) = adjustSparse a d v.numericSupplyRows""",
        "arbitrary_view_adjust_roundtrip": """∀ (v : SupportView), CanonicalView v →
          ∀ (a : Asset) (d : Int), a ∈ v.registeredAssetKeys →
          decode ⟨v.registeredAssetKeys, adjustSparse a d v.numericSupplyRows⟩ =
            adjustComplete a d (decode v)""",
        "arbitrary_view_adjust_lookup": """∀ (v : SupportView), CanonicalView v →
          ∀ (a : Asset) (d : Int), a ∈ v.registeredAssetKeys → ∀ other : Asset,
          supplyFor (adjustSparse a d v.numericSupplyRows) other =
            supplyFor v.numericSupplyRows other + (if other = a then d else 0)""",
        "arbitrary_view_adjust_canonical": """∀ (v : SupportView), CanonicalView v →
          ∀ (a : Asset) (d : Int), a ∈ v.registeredAssetKeys →
          CanonicalView ⟨v.registeredAssetKeys, adjustSparse a d v.numericSupplyRows⟩""",
        "arbitrary_view_adjust_admitted": """∀ (v : SupportView), CanonicalView v →
          ∀ (a : Asset) (d : Int), a ∈ v.registeredAssetKeys →
          SparseSupplyRowsAdmitted v.numericSupplyRows → FitsU128 (supplyFor v.numericSupplyRows a + d) →
          SourceRowsU128 (adjustComplete a d (decode v)) ∧
          SparseSupplyRowsAdmitted (adjustSparse a d v.numericSupplyRows) ∧
          CanonicalView ⟨v.registeredAssetKeys, adjustSparse a d v.numericSupplyRows⟩ ∧
          (adjustComplete a d (decode v)).map V1SupplyRow.asset = v.registeredAssetKeys""",
    }
    body = """
example (v : SupportView) : CanonicalView v ↔
    v.registeredAssetKeys.Nodup ∧ v.registeredAssetKeys.Pairwise (· < ·) ∧
    (v.numericSupplyRows.map SupplyRow.asset).Nodup ∧ NumericAssetKeysOrdered v.numericSupplyRows ∧
    (∀ row ∈ v.numericSupplyRows, row.amountAtoms ≠ 0) ∧
    (∀ row ∈ v.numericSupplyRows, row.asset ∈ v.registeredAssetKeys) := Iff.rfl
example (keys : List Asset) (rows : List SupplyRow)
    (ku : keys.Nodup) (ko : keys.Pairwise (· < ·))
    (nu : (rows.map SupplyRow.asset).Nodup) (no : NumericAssetKeysOrdered rows)
    (nz : ∀ row ∈ rows, row.amountAtoms ≠ 0) (covered : ∀ row ∈ rows, row.asset ∈ keys) :
    encode (decode ⟨keys, rows⟩) = ⟨keys, rows⟩ :=
  encode_decode ⟨keys, rows⟩ ⟨ku, ko, nu, no, nz, covered⟩
"""
    body += "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    output = _probe(view_lean, "ArbitraryViewContracts", body)
    assert output.count("depends on axioms") + output.count("does not depend on any axioms") == 6
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    code = re.sub(r"/-.*?-/", "", SOURCE.read_text(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


def test_interleaved_dormant_keys_support_repeated_admitted_updates(view_lean: LeanSubject) -> None:
    _probe(
        view_lean,
        "ArbitraryViewContinuation",
        """
example : encode (decode interleavedView) = interleavedView :=
  encode_decode interleavedView interleaved_view_canonical
example : SourceRowsU128 (decode interleavedView) :=
  decoded_u128 interleavedView interleaved_view_canonical interleaved_view_bounded
def issued : SupportView :=
  ⟨interleavedView.registeredAssetKeys, adjustSparse "GBP" 7 interleavedView.numericSupplyRows⟩
theorem issued_admitted : SparseSupplyRowsAdmitted issued.numericSupplyRows ∧ CanonicalView issued := by
  have result := arbitrary_view_adjust_admitted interleavedView interleaved_view_canonical "GBP" 7
    (by decide) interleaved_view_bounded (by unfold FitsU128; decide)
  exact ⟨result.2.1, result.2.2.1⟩
example : CanonicalView ⟨issued.registeredAssetKeys, adjustSparse "GBP" (-7) issued.numericSupplyRows⟩ :=
  arbitrary_view_adjust_canonical issued issued_admitted.2 "GBP" (-7) (by decide)
example : decode ⟨issued.registeredAssetKeys, adjustSparse "GBP" (-7) issued.numericSupplyRows⟩ =
    decode interleavedView := by decide
example : numericRows (adjustComplete "USD" 1 []) ≠ adjustSparse "USD" 1 [] :=
  unknown_asset_requires_membership_control.1
example : decode ⟨[], adjustSparse "USD" 1 []⟩ = adjustComplete "USD" 1 (decode ⟨[], []⟩) :=
  unknown_asset_requires_membership_control.2
""",
    )


@pytest.mark.parametrize(
    "name,view",
    (
        ("UncoveredNumericSupport", '⟨[], [⟨"USD", 1⟩]⟩'),
        ("DuplicateNumericKeys", '⟨["USD"], [⟨"USD", 2⟩, ⟨"USD", 3⟩]⟩'),
        ("StoredNumericZero", '⟨["USD"], [⟨"USD", 0⟩]⟩'),
        ("ReversedPolicyKeys", '⟨["USD", "EUR"], [⟨"EUR", 2⟩, ⟨"USD", 3⟩]⟩'),
        ("ReversedNumericKeys", '⟨["EUR", "USD"], [⟨"USD", 3⟩, ⟨"EUR", 2⟩]⟩'),
    ),
)
def test_kernel_refutes_roundtrip_when_input_conditions_are_missing(
    view_lean: LeanSubject,
    name: str,
    view: str,
) -> None:
    path = view_lean.source / f"{name}.lean"
    path.write_text(
        f"import {NAMESPACE}\n{OPEN}def input : SupportView := {view}\n"
        "example : encode (decode input) = input := by decide\n"
    )
    checked = _compile(view_lean, path)
    assert checked.returncode != 0
    assert checked.stdout.count("error:") == 1, checked.stdout
    assert "Tactic `decide` proved that the proposition" in checked.stdout
    assert "is false" in checked.stdout
