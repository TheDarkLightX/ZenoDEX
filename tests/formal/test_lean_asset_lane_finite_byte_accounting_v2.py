"""Retained consumers for the finite asset-lane byte accounting proof.

The target is copied into the fresh source-only subject used by the existing
row-growth fixture chain.  Consumers exercise the exact byte contracts,
reachable complete-table lifecycle, semantic false controls, and a small
explicit-number comparison against independently encoded Python rows.
Metadata-frame correspondence and runtime outcome behavior remain outside the
scope of this retained harness.
"""

from __future__ import annotations

import hashlib
import json
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
from tests.formal.test_lean_asset_lane_finite_row_growth_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "AssetLaneFiniteByteAccountingV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "f328e1ad6c282ba8cd8b17c10d45a47eb752fe33db4591da8e10be479addae97"
PREAMBLE = f"""import {NAMESPACE}
open Proofs
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1 Proofs.RegisteredSupplyViewV1
open Proofs.AssetLaneFiniteRecompositionV2
open {NAMESPACE}
attribute [local instance] lexOrd
set_option maxRecDepth 10000
"""


@pytest.fixture(scope="module")
def byte_accounting_lean(row_growth_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    subject = row_growth_lean
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


def _axiom_names(output: str) -> set[str]:
    return {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }


THEOREM_TYPES = {
    "updateRows_bytes": """∀ (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
      (_ : S.Unique rows),
      (balanceBytes (A.updateRows rows asset owner deltaAtoms)).length + oldBalanceWeight rows asset owner +
          emptyBit rows =
        (balanceBytes rows).length + newBalanceWeight rows asset owner deltaAtoms +
          postEmptyBit rows asset owner deltaAtoms""",
    "adjustComplete_bytes": """∀ (rows : List V1SupplyRow) (asset : Asset) (deltaAtoms : Int)
      (_ : SourceAssetKeysUnique rows) (_ : asset ∈ rows.map V1SupplyRow.asset),
      (supplyBytes (adjustComplete asset deltaAtoms rows)).length + oldSupplyCost rows asset =
        (supplyBytes rows).length + newSupplyCost rows asset deltaAtoms""",
    "framed_update_bytes": """∀ (opening middle closing : Bytes) (balances : List AmountRow)
      (supplies : List V1SupplyRow) (asset owner : String) (deltaAtoms : Int)
      (_ : S.Unique balances) (_ : SourceAssetKeysUnique supplies)
      (_ : asset ∈ supplies.map V1SupplyRow.asset),
      (framedBytes opening middle closing (A.updateRows balances asset owner deltaAtoms)
          (adjustComplete asset deltaAtoms supplies)).length + oldBalanceWeight balances asset owner +
          oldSupplyCost supplies asset + emptyBit balances =
        (framedBytes opening middle closing balances supplies).length +
          newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
          postEmptyBit balances asset owner deltaAtoms""",
    "framed_recomposition_bytes": """∀ (opening middle closing : Bytes) (managed : List Asset)
      (balances : List AmountRow) (supplies : List V1SupplyRow) (asset owner : String) (deltaAtoms : Int)
      (_ : S.Unique balances) (_ : R.AccountsDomain balances)
      (_ : SourceAssetKeysUnique supplies) (_ : SourceAssetKeysOrdered supplies)
      (_ : asset ∈ managed) (_ : asset ∈ supplies.map V1SupplyRow.asset),
      (framedBytes opening middle closing (R.recomposeBalances managed balances asset owner deltaAtoms)
          (R.recomposeSupplies managed supplies asset deltaAtoms)).length +
          oldBalanceWeight balances asset owner + oldSupplyCost supplies asset + emptyBit balances =
        (framedBytes opening middle closing balances supplies).length +
          newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
          postEmptyBit balances asset owner deltaAtoms""",
    "recomposition_capacity_iff": """∀ (opening middle closing : Bytes) (managed : List Asset)
      (balances : List AmountRow) (supplies : List V1SupplyRow) (asset owner : String) (deltaAtoms : Int)
      (rowLimit byteLimit : Nat) (_ : S.Unique balances)
      (_ : R.AccountsDomain balances) (_ : SourceAssetKeysUnique supplies)
      (_ : SourceAssetKeysOrdered supplies) (_ : asset ∈ managed)
      (_ : asset ∈ supplies.map V1SupplyRow.asset),
      ((R.recomposeBalances managed balances asset owner deltaAtoms).length ≤ rowLimit ∧
        (framedBytes opening middle closing (R.recomposeBalances managed balances asset owner deltaAtoms)
          (R.recomposeSupplies managed supplies asset deltaAtoms)).length ≤ byteLimit) ↔
      (balances.length +
          (if C.lookupLast (S.accountKey asset owner) balances + deltaAtoms ≠ 0 then 1 else 0) ≤
          rowLimit + (if S.accountKey asset owner ∈ balances.map C.amountKey then 1 else 0) ∧
        (framedBytes opening middle closing balances supplies).length +
            newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
            postEmptyBit balances asset owner deltaAtoms ≤
          byteLimit + oldBalanceWeight balances asset owner + oldSupplyCost supplies asset +
            emptyBit balances)""",
    "lane_capacity_4096_1048576": """∀ (release : String) (managedPolicies originRegistry transferPolicies : Bytes)
      (managed : List Asset) (balances : List AmountRow) (supplies : List V1SupplyRow)
      (asset owner : String) (deltaAtoms : Int) (_ : S.Unique balances)
      (_ : R.AccountsDomain balances) (_ : SourceAssetKeysUnique supplies)
      (_ : SourceAssetKeysOrdered supplies) (_ : asset ∈ managed)
      (_ : asset ∈ supplies.map V1SupplyRow.asset),
      ((R.recomposeBalances managed balances asset owner deltaAtoms).length ≤ 4096 ∧
        (laneBytes release managedPolicies originRegistry transferPolicies
          (R.recomposeBalances managed balances asset owner deltaAtoms)
          (R.recomposeSupplies managed supplies asset deltaAtoms)).length ≤ 1048576) ↔
      (balances.length +
          (if C.lookupLast (S.accountKey asset owner) balances + deltaAtoms ≠ 0 then 1 else 0) ≤
          4096 + (if S.accountKey asset owner ∈ balances.map C.amountKey then 1 else 0) ∧
        (laneBytes release managedPolicies originRegistry transferPolicies balances supplies).length +
            newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
            postEmptyBit balances asset owner deltaAtoms ≤
          1048576 + oldBalanceWeight balances asset owner + oldSupplyCost supplies asset +
            emptyBit balances)""",
}


def test_exact_byte_contracts_and_standard_axioms(byte_accounting_lean: LeanSubject) -> None:
    source_code = SOURCE.read_text()
    for name in THEOREM_TYPES:
        assert re.search(rf"^theorem {re.escape(name)}\b", source_code, flags=re.MULTILINE)
    code = re.sub(r"/-.*?-/", "", source_code, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    result = _consumer(byte_accounting_lean, "ByteAccountingContracts", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    assert result.stdout.count("depends on axioms") + result.stdout.count(
        "does not depend on any axioms"
    ) == len(THEOREM_TYPES)
    assert _axiom_names(result.stdout) <= {"propext", "Quot.sound", "Classical.choice"}


def test_literal_rows_empty_arrays_and_stateful_byte_lifecycle(
    byte_accounting_lean: LeanSubject,
) -> None:
    result = _consumer(
        byte_accounting_lean,
        "ByteLiteralLifecycleControls",
        r"""
namespace LiteralLifecycle

def escapedOwner : String := "ali\"ce\\x"
def escapedAsset : String := "U\"S\\D"
def escapedRow : AmountRow := ⟨escapedOwner, escapedAsset, "accounts", 9⟩

theorem printable_escapes_are_valid : ValidToken escapedOwner ∧ ValidToken escapedAsset := by
  constructor <;> unfold ValidToken <;> decide

theorem control_and_unicode_are_outside_domain : ¬ ValidToken "\n" ∧ ¬ ValidToken "é" := by
  constructor <;> unfold ValidToken <;> decide

theorem byte_exact_escaped_row :
    amountRow escapedRow =
      raw "{\"amount_atoms\":9,\"asset\":\"U\\\"S\\\\D\",\"custody_domain\":\"accounts\",\"owner\":\"ali\\\"ce\\\\x\"}" := by
  decide

theorem character_count_misses_escape_bytes :
    (raw escapedOwner).length = 8 ∧ (quoted escapedOwner).length = 12 ∧
      (quoted escapedOwner).length ≠ (raw escapedOwner).length + 2 ∧
      (raw escapedAsset).length = 5 ∧ (quoted escapedAsset).length = 9 := by
  decide

theorem decimal_width_controls :
    numberCost 0 = 1 ∧ numberCost 9 = 1 ∧ numberCost 10 = 2 ∧
      numberCost 99 = 2 ∧ numberCost 100 = 3 ∧
      numberCost (340282366920938463463374607431768211455 : Int) = 39 := by
  decide

def dormant : List V1SupplyRow := [⟨"AUD", 0⟩, ⟨"USD", 0⟩, ⟨"ZZZ", 0⟩]
def funded (atoms : Int) : List AmountRow := [⟨escapedOwner, "USD", "accounts", atoms⟩]
def supply (atoms : Int) : List V1SupplyRow := [⟨"AUD", 0⟩, ⟨"USD", atoms⟩, ⟨"ZZZ", 0⟩]

theorem u128_max_row_length :
    (amountRow ⟨escapedOwner, "USD", "accounts",
      (340282366920938463463374607431768211455 : Int)⟩).length = 119 := by
  decide

theorem complete_zero_rows_are_encoded :
    numericRows dormant = [] ∧ (supplyBytes dormant).length = 100 ∧
      (supplyBytes dormant).length ≠ (supplyBytes []).length := by
  decide

theorem empty_array_has_no_first_comma :
    (balanceBytes []).length = 2 ∧ (amountRow ⟨escapedOwner, "USD", "accounts", 1⟩).length = 81 ∧
      (balanceBytes (funded 1)).length = 83 ∧
      (balanceBytes (funded 1)).length - (balanceBytes []).length = 81 ∧
      (balanceBytes (funded 1)).length - (balanceBytes []).length ≠ 82 := by
  decide

theorem issue_from_empty_bytes (opening middle closing : Bytes) :
    (framedBytes opening middle closing (A.updateRows [] "USD" escapedOwner 1)
        (adjustComplete "USD" 1 dormant)).length =
      (framedBytes opening middle closing [] dormant).length + 81 := by
  have changed := framed_update_bytes opening middle closing [] dormant "USD" escapedOwner 1
    (by unfold S.Unique; decide) (by unfold SourceAssetKeysUnique; decide) (by decide)
  change _ + 0 + 32 + 1 = _ + 82 + 32 + 0 at changed
  omega

theorem full_burn_to_empty_bytes (opening middle closing : Bytes) :
    (framedBytes opening middle closing (A.updateRows (funded 1) "USD" escapedOwner (-1))
        (adjustComplete "USD" (-1) (supply 1))).length + 81 =
      (framedBytes opening middle closing (funded 1) (supply 1)).length := by
  have changed := framed_update_bytes opening middle closing (funded 1) (supply 1) "USD" escapedOwner (-1)
    (by unfold S.Unique; decide) (by unfold SourceAssetKeysUnique; decide) (by decide)
  change _ + 82 + 32 + 0 = _ + 0 + 32 + 1 at changed
  omega

theorem actual_row_lifecycle :
    A.updateRows [] "USD" escapedOwner 1 = funded 1 ∧
      A.updateRows (funded 1) "USD" escapedOwner (-1) = [] ∧
      A.updateRows [] "USD" escapedOwner 10 = funded 10 ∧
      adjustComplete "USD" (-1) (supply 1) = dormant := by
  simp +decide [A.updateRows, funded, C.lookupLast, C.amountKey, S.accountKey,
    S.putAmount, S.eraseKey, S.makeAmount, S.accounts, C.sortOn, S.balanceWire]

theorem issue_burn_reissue_bytes (opening middle closing : Bytes) :
    let issued := A.updateRows [] "USD" escapedOwner 1
    let burned := A.updateRows issued "USD" escapedOwner (-1)
    (framedBytes opening middle closing (A.updateRows burned "USD" escapedOwner 10)
      (adjustComplete "USD" 10 (adjustComplete "USD" (-1) (supply 1)))).length =
      (framedBytes opening middle closing [] dormant).length + 83 := by
  dsimp only
  rw [actual_row_lifecycle.1, actual_row_lifecycle.2.1, actual_row_lifecycle.2.2.2]
  have changed := framed_update_bytes opening middle closing [] dormant "USD" escapedOwner 10
    (by unfold S.Unique; decide) (by unfold SourceAssetKeysUnique; decide) (by decide)
  change _ + 0 + 32 + 1 = _ + 83 + 33 + 0 at changed
  omega

theorem funded_digit_growth (opening middle closing : Bytes) :
    (A.updateRows (funded 9) "USD" escapedOwner 1).length = 1 ∧
      (framedBytes opening middle closing (A.updateRows (funded 9) "USD" escapedOwner 1)
        (adjustComplete "USD" 1 (supply 9))).length =
      (framedBytes opening middle closing (funded 9) (supply 9)).length + 2 := by
  have changed := framed_update_bytes opening middle closing (funded 9) (supply 9) "USD" escapedOwner 1
    (by unfold S.Unique; decide) (by unfold SourceAssetKeysUnique; decide) (by decide)
  change _ + 82 + 32 + 0 = _ + 83 + 33 + 0 at changed
  have count := G.updateRows_length (funded 9) "USD" escapedOwner 1 (by unfold S.Unique; decide)
  change _ + 1 = 1 + 1 at count
  omega

theorem funded_99_to_100_growth (opening middle closing : Bytes) :
    (framedBytes opening middle closing (A.updateRows (funded 99) "USD" escapedOwner 1)
      (adjustComplete "USD" 1 (supply 99))).length =
      (framedBytes opening middle closing (funded 99) (supply 99)).length + 2 := by
  have changed := framed_update_bytes opening middle closing (funded 99) (supply 99) "USD" escapedOwner 1
    (by unfold S.Unique; decide) (by unfold SourceAssetKeysUnique; decide) (by decide)
  change _ + 83 + 33 + 0 = _ + 84 + 34 + 0 at changed
  omega

theorem exact_real_byte_cap_and_one_byte_excess (opening middle closing : Bytes) :
    ((framedBytes opening middle closing (funded 9) (supply 9)).length + 2 = 1048576 →
      (framedBytes opening middle closing (A.updateRows (funded 9) "USD" escapedOwner 1)
        (adjustComplete "USD" 1 (supply 9))).length = 1048576) ∧
    ((framedBytes opening middle closing (funded 9) (supply 9)).length + 1 = 1048576 →
      (framedBytes opening middle closing (A.updateRows (funded 9) "USD" escapedOwner 1)
        (adjustComplete "USD" 1 (supply 9))).length = 1048577 ∧
      ¬ (framedBytes opening middle closing (A.updateRows (funded 9) "USD" escapedOwner 1)
        (adjustComplete "USD" 1 (supply 9))).length ≤ 1048576) := by
  have growth := (funded_digit_growth opening middle closing).2
  omega

end LiteralLifecycle
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""


def test_compact_interleaved_aggregate_and_source_capacity_consumer(
    byte_accounting_lean: LeanSubject,
) -> None:
    result = _consumer(
        byte_accounting_lean,
        "ByteAggregateControls",
        r"""
namespace AggregateControls

namespace K
export Proofs.AssetLaneFiniteRecompositionV2.Controls (managed balances complete expectedIssue
  issuedComplete reissuedComplete balances_unique balances_accounts complete_unique complete_ordered
  literal_issue_balances literal_supply_lifecycle constructed_full_burn_and_reissue)
end K

def escapedOwner : String := "ali\"ce\\x"

theorem interleaved_unmanaged_byte_delta :
    (framedBytes [] [] []
      (R.recomposeBalances K.managed K.balances "USD" escapedOwner 1)
      (R.recomposeSupplies K.managed K.complete "USD" 1)).length =
      (framedBytes [] [] [] K.balances K.complete).length + 82 := by
  have changed := framed_recomposition_bytes [] [] [] K.managed K.balances K.complete
    "USD" escapedOwner 1 K.balances_unique K.balances_accounts K.complete_unique
    K.complete_ordered (by decide) (by decide)
  change _ + 0 + 32 + 0 = _ + 82 + 32 + 0 at changed
  omega

theorem exact_source_premise_capacity :
    ((R.recomposeBalances K.managed K.balances "USD" escapedOwner 1).length ≤ 4096 ∧
      (laneBytes "release" [] [] []
        (R.recomposeBalances K.managed K.balances "USD" escapedOwner 1)
        (R.recomposeSupplies K.managed K.complete "USD" 1)).length ≤ 1048576) ↔
    (K.balances.length +
        (if C.lookupLast (S.accountKey "USD" escapedOwner) K.balances + 1 ≠ 0 then 1 else 0) ≤
        4096 + (if S.accountKey "USD" escapedOwner ∈ K.balances.map C.amountKey then 1 else 0) ∧
      (laneBytes "release" [] [] [] K.balances K.complete).length +
          newBalanceWeight K.balances "USD" escapedOwner 1 +
          newSupplyCost K.complete "USD" 1 +
          postEmptyBit K.balances "USD" escapedOwner 1 ≤
        1048576 + oldBalanceWeight K.balances "USD" escapedOwner +
          oldSupplyCost K.complete "USD" + emptyBit K.balances) :=
  lane_capacity_4096_1048576 "release" [] [] [] K.managed K.balances K.complete
    "USD" escapedOwner 1 K.balances_unique K.balances_accounts K.complete_unique
    K.complete_ordered (by decide) (by decide)

example :
    R.recomposeBalances K.managed K.balances "USD" "alice" 2 = K.expectedIssue :=
  K.literal_issue_balances
example :
    R.recomposeSupplies K.managed K.complete "USD" 2 = K.issuedComplete :=
  K.literal_supply_lifecycle.1
example :
    R.recomposeSupplies K.managed K.issuedComplete "USD" (-2) = K.complete :=
  K.literal_supply_lifecycle.2.1
example :
    R.recomposeSupplies K.managed K.complete "USD" 1 = K.reissuedComplete :=
  K.literal_supply_lifecycle.2.2
example :
    R.recomposeBalances K.managed
        (R.recomposeBalances K.managed K.balances "USD" "alice" 2)
        "USD" "alice" (-2) = K.balances :=
  K.constructed_full_burn_and_reissue.1

end AggregateControls
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""


def _python_amount_row(owner: str, asset: str, custody: str, atoms: int) -> bytes:
    return json.dumps(
        {"amount_atoms": atoms, "asset": asset, "custody_domain": custody, "owner": owner},
        ensure_ascii=True,
        separators=(",", ":"),
    ).encode("ascii")


def _python_supply_row(asset: str, atoms: int) -> bytes:
    return json.dumps(
        {"amount_atoms": atoms, "asset": asset}, ensure_ascii=True, separators=(",", ":")
    ).encode("ascii")


def _python_array(rows: list[bytes]) -> bytes:
    return b"[" + b",".join(rows) + b"]"


def test_explicit_numeric_rendering_matches_independent_small_rows(
    byte_accounting_lean: LeanSubject,
) -> None:
    result = _consumer(
        byte_accounting_lean,
        "ByteExplicitNumbers",
        r"""
namespace ExplicitNumbers

def owner : String := "ali\"ce\\x"
def row : AmountRow := ⟨owner, "U\"S\\D", "accounts", 9⟩
def maxRow : AmountRow := ⟨owner, "U\"S\\D", "accounts",
  (340282366920938463463374607431768211455 : Int)⟩
def dormant : List V1SupplyRow := [⟨"AUD", 0⟩, ⟨"USD", 0⟩, ⟨"ZZZ", 0⟩]
def funded : List AmountRow := [⟨owner, "USD", "accounts", 9⟩]
def fundedNext : List AmountRow := [⟨owner, "USD", "accounts", 10⟩]

def render (bytes : Bytes) : String :=
  String.intercalate "," (bytes.map (fun byte => toString byte.toNat))

#eval IO.println (render (amountRow row))
#eval IO.println (render (balanceBytes []))
#eval IO.println (render (supplyBytes dormant))
#eval IO.println (render (amountRow maxRow))
#eval IO.println (render (balanceBytes funded))
#eval IO.println (render (balanceBytes fundedNext))
#eval IO.println (render (leafBytes "schema" "release" [] [] []))
#eval IO.println (render (laneBytes "release" [] [] [] [] []))

end ExplicitNumbers
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    observed = [
        bytes(int(part) for part in line.split(","))
        for line in result.stdout.splitlines()
        if line.strip()
    ]
    owner = 'ali"ce\\x'
    asset = 'U"S\\D'
    dormant = _python_array(
        [_python_supply_row(asset_name, 0) for asset_name in ("AUD", "USD", "ZZZ")]
    )
    expected = [
        _python_amount_row(owner, asset, "accounts", 9),
        b"[]",
        dormant,
        _python_amount_row(owner, asset, "accounts", (1 << 128) - 1),
        _python_array([_python_amount_row(owner, "USD", "accounts", 9)]),
        _python_array([_python_amount_row(owner, "USD", "accounts", 10)]),
        b'{"balances":[],"module_release_id":"release","policies":,"schema":"schema","supplies":[]}',
        b'{"balances":[],"managed_policies":,"module_release_id":"release","origin_registry":,"schema":"zenodex/asset-lane-state/v2","supplies":[],"transfer_policies":}',
    ]
    assert observed == expected


_BYTE_FALSE_LAWS = (
    (
        "NoEscapeBytes",
        "(quotedWithoutEscapes owner).length = (quoted owner).length",
    ),
    (
        "NoEmptyArrayCorrection",
        '(balanceBytes [⟨owner, "USD", "accounts", 1⟩]).length - (balanceBytes []).length = 82',
    ),
    (
        "NoFundedDigitGrowth",
        "(framedBytes [] [] [] funded10 supply10).length = (framedBytes [] [] [] funded9 supply9).length",
    ),
    (
        "NoZeroSupplyRows",
        '(supplyBytes [⟨"AUD", 0⟩, ⟨"USD", 2⟩, ⟨"ZZZ", 0⟩]).length = (supplyBytes [⟨"USD", 2⟩]).length',
    ),
)


def _byte_false_body(law: str) -> str:
    return f"""
namespace ByteSpecificMutant

def owner : String := "ali\\\"ce\\\\x"

def quotedWithoutEscapes (value : String) : Bytes := [34] ++ raw value ++ [34]

def funded9 : List AmountRow := [⟨owner, "USD", "accounts", 9⟩]
def funded10 : List AmountRow := [⟨owner, "USD", "accounts", 10⟩]
def supply9 : List V1SupplyRow := [⟨"AUD", 0⟩, ⟨"USD", 9⟩, ⟨"ZZZ", 0⟩]
def supply10 : List V1SupplyRow := [⟨"AUD", 0⟩, ⟨"USD", 10⟩, ⟨"ZZZ", 0⟩]

example : {law} := by
  decide

end ByteSpecificMutant
"""


@pytest.mark.parametrize("name,law", _BYTE_FALSE_LAWS)
def test_false_byte_laws_fail_with_semantic_diagnostics(
    byte_accounting_lean: LeanSubject, name: str, law: str
) -> None:
    path = byte_accounting_lean.source / f"{name}.lean"
    path.write_text(PREAMBLE + _byte_false_body(law))
    checked = _compile(byte_accounting_lean, path)
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
