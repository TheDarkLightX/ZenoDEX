"""Independent acceptance controls for the registered-supply support bridge.

The Lean closure is copied into a fresh temporary subject and compiled with the
pinned Std-only toolchain.  Concrete controls keep zero rows in the source
representation while checking that numeric support is filtered.  Python
observations use the existing managed-asset V1 issue-from-zero and full-burn
fixtures; they establish finite row/key correspondence only.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import AssetSupplyV1

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean-mathlib"
MODULE = "RegisteredSupplySupportV1"
NAMESPACE = f"Proofs.{MODULE}"
MODULE_SOURCE = PROJECT / "Proofs" / f"{MODULE}.lean"
DEPENDENCIES = ("GlobalSettlementCoreV2", "GlobalEconomicStateRefinementV2")
PINNED_SOURCES = {
    "GlobalSettlementCoreV2":
        "2ce254367dc8e8299f82f8a93e09c1d470f3a218ed01af7efb766946a34255a4",
    "GlobalEconomicStateRefinementV2":
        "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    MODULE: "cbd01b5eef5d932843ded7d3060611c846ad0dbc4c164bd5f15cbbbfa4e14f6e",
}
OPENS = (
    "open Proofs.GlobalSettlementCoreV2 "
    "Proofs.GlobalEconomicStateRefinementV2 "
    f"{NAMESPACE}\n"
)

THEOREM_TYPES = {
    "encode_registered_keys_exact":
        "∀ (rows : List V1SupplyRow), (encode rows).registeredAssetKeys = rows.map V1SupplyRow.asset",
    "encode_registered_key_length":
        "∀ (rows : List V1SupplyRow), (encode rows).registeredAssetKeys.length = rows.length",
    "encode_numeric_key_length_no_increase":
        "∀ (rows : List V1SupplyRow), (encode rows).numericSupplyRows.length ≤ rows.length",
    "decode_registered_key_length":
        "∀ (view : SupportView), (decode view).length = view.registeredAssetKeys.length",
    "decode_registered_keys_exact":
        "∀ (view : SupportView), (decode view).map V1SupplyRow.asset = view.registeredAssetKeys",
    "supplyFor_numericRows_preserved":
        "∀ (rows : List V1SupplyRow) (asset : Asset), supplyFor (numericRows rows) asset = supplyFor (sourceRowsAsNumeric rows) asset",
    "source_supplyFor_zero_of_absent":
        "∀ {rows : List V1SupplyRow} {asset : Asset}, (∀ row ∈ rows, row.asset ≠ asset) → supplyFor (sourceRowsAsNumeric rows) asset = 0",
    "source_supplyFor_eq_member_of_unique":
        "∀ {rows : List V1SupplyRow} {row : V1SupplyRow}, SourceAssetKeysUnique rows → row ∈ rows → supplyFor (sourceRowsAsNumeric rows) row.asset = row.amountAtoms",
    "decode_encode":
        "∀ (rows : List V1SupplyRow), SourceAssetKeysUnique rows → decode (encode rows) = rows",
    "filtered_source_keys_unique":
        "∀ {rows : List V1SupplyRow}, SourceAssetKeysUnique rows → ((rows.filter nonzeroRow).map V1SupplyRow.asset).Nodup",
    "encoded_numeric_keys_unique":
        "∀ {rows : List V1SupplyRow}, SourceAssetKeysUnique rows → ((encode rows).numericSupplyRows.map SupplyRow.asset).Nodup",
    "encoded_numeric_keys_sublist":
        "∀ (rows : List V1SupplyRow), ((encode rows).numericSupplyRows.map SupplyRow.asset).Sublist (rows.map V1SupplyRow.asset)",
    "encoded_numeric_keys_pairwise_of_source":
        "∀ (rows : List V1SupplyRow) (R : Asset → Asset → Prop), List.Pairwise R (rows.map V1SupplyRow.asset) → List.Pairwise R ((encode rows).numericSupplyRows.map SupplyRow.asset)",
    "encoded_numeric_support_nonzero":
        "∀ (rows : List V1SupplyRow), ∀ row ∈ (encode rows).numericSupplyRows, row.amountAtoms ≠ 0",
    "encoded_numeric_support_admitted":
        "∀ {rows : List V1SupplyRow}, SourceRowsU128 rows → NumericSupportAdmitted (encode rows)",
    "decoded_supply_lookup":
        "∀ (view : SupportView) (asset : Asset), ∀ row ∈ decode view, row.asset = asset → row.amountAtoms = supplyFor view.numericSupplyRows asset",
    "decoded_keys_preserve_encoded_keys":
        "∀ (rows : List V1SupplyRow), (decode (encode rows)).map V1SupplyRow.asset = (encode rows).registeredAssetKeys",
    "decode_encode_registered_keys_exact":
        "∀ (rows : List V1SupplyRow), (decode (encode rows)).map V1SupplyRow.asset = rows.map V1SupplyRow.asset",
    "zero_row_numeric_projection_collides_with_empty":
        "(encode zeroRows).numericSupplyRows = (encode []).numericSupplyRows ∧ (encode zeroRows).registeredAssetKeys ≠ (encode []).registeredAssetKeys",
    "zero_row_roundtrip_keeps_registered_identity":
        "decode (encode zeroRows) = zeroRows",
    "zero_row_numeric_lookup_is_zero":
        "supplyFor (encode zeroRows).numericSupplyRows \"ZUSD\" = 0",
    "duplicate_keys_are_not_unique":
        "¬ SourceAssetKeysUnique duplicateRows",
    "duplicate_numeric_lookup_aggregates":
        "supplyFor (encode duplicateRows).numericSupplyRows \"USD\" = 5",
    "duplicate_roundtrip_is_not_lossless":
        "decode (encode duplicateRows) ≠ duplicateRows",
}


@dataclass(frozen=True)
class LeanSubject:
    executable: Path
    source: Path
    library: Path


def _compile(
    subject: LeanSubject,
    path: Path,
    output: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    command = [
        str(subject.executable),
        "-DwarningAsError=true",
        "-R",
        str(subject.source),
    ]
    if output is not None:
        command.extend(("-o", str(output)))
    environment = dict(os.environ, LEAN_PATH=str(subject.library))
    return subprocess.run(
        [*command, str(path)],
        cwd=subject.source,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=90,
    )


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    assert PROJECT.joinpath("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    located = subprocess.run(
        ["elan", "which", "lean"],
        cwd=PROJECT,
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    )
    executable = Path(located.stdout.strip())
    version = subprocess.run(
        [str(executable), "--version"],
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    )
    assert "version 4.27.0," in version.stdout
    assert MODULE_SOURCE.is_file(), MODULE_SOURCE
    assert hashlib.sha256(MODULE_SOURCE.read_bytes()).hexdigest() == PINNED_SOURCES[MODULE]

    directory = tmp_path_factory.mktemp("registered-supply-support")
    source, library = directory / "source", directory / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    for name in DEPENDENCIES:
        captured = source / "Proofs" / f"{name}.lean"
        dependency = PROJECT / "Proofs" / f"{name}.lean"
        assert hashlib.sha256(dependency.read_bytes()).hexdigest() == PINNED_SOURCES[name]
        captured.write_bytes(dependency.read_bytes())
        result = _compile(subject, captured, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""

    captured = source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes(MODULE_SOURCE.read_bytes())
    result = _compile(subject, captured, library / "Proofs" / f"{MODULE}.olean")
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPENS}{body}")
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def test_public_theorems_have_independent_consumers_and_no_forbidden_axioms(
    lean: LeanSubject,
) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == tuple(THEOREM_TYPES)

    consumers = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    consumers += "\n" + "\n".join(
        f"#print axioms {NAMESPACE}.{name}" for name in THEOREM_TYPES
    )
    output = _probe(lean, "IndependentConsumers", consumers)
    assert output.count("depends on axioms") + output.count(
        "does not depend on any axioms"
    ) == len(THEOREM_TYPES)
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


def test_zero_mixed_unsorted_max_and_identity_loss_controls(lean: LeanSubject) -> None:
    _probe(lean, "ConcreteSupportCases", r'''
def emptyRows : List V1SupplyRow := []
def allZeroRows : List V1SupplyRow := [⟨"A", 0⟩, ⟨"B", 0⟩]
def zeroPositiveRows : List V1SupplyRow := [⟨"A", 0⟩, ⟨"B", 5⟩]
def unsortedRows : List V1SupplyRow := [⟨"B", 5⟩, ⟨"A", 0⟩]
def separatedRows : List V1SupplyRow := [⟨"A", 2⟩, ⟨"M", 0⟩, ⟨"Z", 3⟩]
def maxRows : List V1SupplyRow := [⟨"MAX", maxU128⟩]
def negativeRows : List V1SupplyRow := [⟨"NEG", -1⟩]
def overflowRows : List V1SupplyRow := [⟨"OVER", maxU128 + 1⟩]
def duplicateRowsLocal : List V1SupplyRow := [⟨"A", 2⟩, ⟨"A", 3⟩]
def removedKeyView : SupportView :=
  { registeredAssetKeys := ["B"], numericSupplyRows := [⟨"B", 5⟩] }

example : decode (encode emptyRows) = emptyRows :=
  decode_encode emptyRows (by unfold SourceAssetKeysUnique; decide)
example : decode (encode allZeroRows) = allZeroRows :=
  decode_encode allZeroRows (by unfold SourceAssetKeysUnique; decide)
example : decode (encode zeroPositiveRows) = zeroPositiveRows :=
  decode_encode zeroPositiveRows (by unfold SourceAssetKeysUnique; decide)
example : decode (encode unsortedRows) = unsortedRows :=
  decode_encode unsortedRows (by unfold SourceAssetKeysUnique; decide)
example : decode (encode maxRows) = maxRows :=
  decode_encode maxRows (by unfold SourceAssetKeysUnique; decide)

example : SourceRowsU128 maxRows := by
  intro row member
  simp only [maxRows, List.mem_singleton] at member
  subst row
  unfold FitsU128 maxU128
  decide
example : NumericSupportAdmitted (encode allZeroRows) :=
  encoded_numeric_support_admitted (rows := allZeroRows) (by
    intro row member
    simp [allZeroRows] at member
    rcases member with rfl | rfl <;> unfold FitsU128 <;> decide)
example : NumericSupportAdmitted (encode zeroPositiveRows) :=
  encoded_numeric_support_admitted (rows := zeroPositiveRows) (by
    intro row member
    simp [zeroPositiveRows] at member
    rcases member with rfl | rfl <;> unfold FitsU128 <;> decide)
example : NumericSupportAdmitted (encode maxRows) :=
  encoded_numeric_support_admitted (rows := maxRows) (by
    intro row member
    simp only [maxRows, List.mem_singleton] at member
    subst row
    unfold FitsU128 maxU128
    decide)
example : ¬ SourceRowsU128 negativeRows := by
  intro admitted
  have row := admitted (⟨"NEG", (-1 : Int)⟩) (by simp [negativeRows])
  unfold FitsU128 at row
  have lower : (0 : Int) ≤ -1 := row.1
  omega
example : ¬ SourceRowsU128 overflowRows := by
  intro admitted
  have row := admitted (⟨"OVER", (maxU128 + 1 : Int)⟩) (by simp [overflowRows])
  unfold FitsU128 at row
  have upper : maxU128 + 1 ≤ maxU128 := row.2
  omega
example : ¬ NumericSupportAdmitted (encode negativeRows) := by
  intro admitted
  change ∀ row ∈ (encode negativeRows).numericSupplyRows,
    FitsU128 row.amountAtoms ∧ row.amountAtoms ≠ 0 at admitted
  have row := admitted (⟨"NEG", (-1 : Int)⟩) (by decide)
  unfold FitsU128 at row
  have lower : (0 : Int) ≤ -1 := row.1.1
  omega
example : ¬ NumericSupportAdmitted (encode overflowRows) := by
  intro admitted
  change ∀ row ∈ (encode overflowRows).numericSupplyRows,
    FitsU128 row.amountAtoms ∧ row.amountAtoms ≠ 0 at admitted
  have row := admitted (⟨"OVER", (maxU128 + 1 : Int)⟩) (by decide)
  unfold FitsU128 at row
  have upper : maxU128 + 1 ≤ maxU128 := row.1.2
  omega

example : (encode zeroPositiveRows).registeredAssetKeys = ["A", "B"] := by decide
example : (encode zeroPositiveRows).numericSupplyRows = [⟨"B", 5⟩] := by decide
example : (encode zeroPositiveRows).numericSupplyRows.length ≤ zeroPositiveRows.length :=
  encode_numeric_key_length_no_increase zeroPositiveRows
example : (decode (encode zeroPositiveRows)).map V1SupplyRow.asset = ["A", "B"] :=
  decoded_keys_preserve_encoded_keys zeroPositiveRows
example : (decode (encode unsortedRows)).map V1SupplyRow.asset = ["B", "A"] := by decide
example : (encode separatedRows).numericSupplyRows = [⟨"A", 2⟩, ⟨"Z", 3⟩] := by decide
example : ((encode separatedRows).numericSupplyRows.map SupplyRow.asset).Sublist
    (separatedRows.map V1SupplyRow.asset) :=
  encoded_numeric_keys_sublist separatedRows
example : List.Pairwise (fun left right : Asset => left < right)
    ((encode separatedRows).numericSupplyRows.map SupplyRow.asset) :=
  encoded_numeric_keys_pairwise_of_source separatedRows
    (fun left right => left < right) (by decide)

example : supplyFor (numericRows duplicateRowsLocal) "A" = 5 := by decide
example : ¬ SourceAssetKeysUnique duplicateRowsLocal := by
  simp [SourceAssetKeysUnique, duplicateRowsLocal]
example : decode (encode duplicateRowsLocal) ≠ duplicateRowsLocal := by decide
example : supplyFor (sourceRowsAsNumeric zeroPositiveRows) "A" =
    supplyFor removedKeyView.numericSupplyRows "A" := by decide
example : decode removedKeyView ≠ zeroPositiveRows := by decide
''')


def _runtime_rows_term(rows: tuple[AssetSupplyV1, ...]) -> str:
    return "[" + ",".join(
        f"⟨{json.dumps(row.asset)}, ({row.amount_atoms} : Int)⟩" for row in rows
    ) + "]"


def _lean_observe_rows(
    lean: LeanSubject,
    rows: tuple[AssetSupplyV1, ...],
) -> list[list[list[str]]]:
    body = f'''
def rowView (rows : List V1SupplyRow) : List (List String) :=
  rows.map fun row => [row.asset, toString row.amountAtoms]
def supplyView (rows : List SupplyRow) : List (List String) :=
  rows.map fun row => [row.asset, toString row.amountAtoms]
def observe (rows : List V1SupplyRow) : String :=
  reprStr [rowView (decode (encode rows)),
    supplyView (encode rows).numericSupplyRows]
def runtimeRows : List V1SupplyRow := {_runtime_rows_term(rows)}
#eval IO.println (reprStr (observe runtimeRows))
'''
    output = _probe(lean, "RuntimeRows", body)
    lines = [line for line in output.splitlines() if line.strip()]
    assert len(lines) == 1, output
    return json.loads(json.loads(lines[0]))


def _runtime_view(rows: tuple[AssetSupplyV1, ...]) -> list[list[str]]:
    return [[row.asset, str(row.amount_atoms)] for row in rows]


def test_runtime_issue_from_zero_preserves_key_and_model_rows(lean: LeanSubject) -> None:
    from src.core.managed_asset_lifecycle_module_v1 import (
        transition_managed_asset_lifecycle_v1,
    )
    from src.core.managed_asset_lifecycle_types_v1 import (
        ManagedAssetLifecycleAcceptedV1,
    )
    from tests.core.test_managed_asset_lifecycle_boundaries_v1 import (
        _command,
        _context,
        _state,
    )

    pre_state = _state(account_atoms=0, supply_atoms=0)
    before = (pre_state.supplies, pre_state.to_canonical())
    result = transition_managed_asset_lifecycle_v1(
        _context(issue=True), pre_state, _command(issue=True, amount_atoms=1)
    )
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert (pre_state.supplies, pre_state.to_canonical()) == before
    assert tuple(row.asset for row in pre_state.supplies) == tuple(
        row.asset for row in result.post_state.supplies
    ) == ("USD",)
    for state, expected in ((pre_state, [["USD", "0"]]),
                            (result.post_state, [["USD", "1"]])):
        rows = tuple(state.supplies)
        assert [row.to_canonical() for row in rows] == [
            {"asset": asset, "amount_atoms": int(amount)}
            for asset, amount in expected
        ]
        assert _lean_observe_rows(lean, rows) == [
            _runtime_view(rows),
            _runtime_view(tuple(row for row in rows if row.amount_atoms != 0)),
        ]


def test_runtime_full_burn_preserves_zero_supply_row_and_key(lean: LeanSubject) -> None:
    from src.core.managed_asset_lifecycle_module_v1 import (
        transition_managed_asset_lifecycle_v1,
    )
    from src.core.managed_asset_lifecycle_types_v1 import (
        ManagedAssetLifecycleAcceptedV1,
    )
    from tests.core.test_managed_asset_lifecycle_boundaries_v1 import (
        I128_MIN_MAGNITUDE,
        _command,
        _context,
        _state,
    )

    pre_state = _state(
        account_atoms=I128_MIN_MAGNITUDE,
        supply_atoms=I128_MIN_MAGNITUDE,
    )
    before = (pre_state.supplies, pre_state.to_canonical())
    result = transition_managed_asset_lifecycle_v1(
        _context(issue=False),
        pre_state,
        _command(issue=False, amount_atoms=I128_MIN_MAGNITUDE),
    )
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert (pre_state.supplies, pre_state.to_canonical()) == before
    assert result.post_state.balances == ()
    assert result.post_state.supplies == (AssetSupplyV1("USD", 0),)
    assert tuple(row.asset for row in result.post_state.supplies) == ("USD",)
    for state, expected in ((pre_state, [["USD", str(I128_MIN_MAGNITUDE)]]),
                            (result.post_state, [["USD", "0"]])):
        rows = tuple(state.supplies)
        assert [row.to_canonical() for row in rows] == [
            {"asset": asset, "amount_atoms": int(amount)}
            for asset, amount in expected
        ]
        assert _lean_observe_rows(lean, rows) == [
            _runtime_view(rows),
            _runtime_view(tuple(row for row in rows if row.amount_atoms != 0)),
        ]
