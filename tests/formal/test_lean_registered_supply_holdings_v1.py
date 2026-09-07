"""Independent acceptance controls for the V1 registered-supply holdings bridge.

The formal consumer copies the producer's transitive Lean closure into a fresh
Std-only subject and compiles it with the repository-pinned toolchain.  The
primary witness keeps a complete two-asset V1 key list with one explicit zero
supply row and one positive row.  Runtime cases observe the existing managed
asset lifecycle and asset-lane projection values only; they do not promote a
Python observation to a Lean/runtime refinement claim.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from collections.abc import Callable
from pathlib import Path
from typing import TYPE_CHECKING, Final

import pytest

if TYPE_CHECKING:
    from src.core.asset_lane_projection_v1 import AssetLaneStateProjectionV1
    from src.core.asset_transfer_types_v1 import AssetTransferStateV1
    from src.core.global_settlement_types_v1 import EconomicAmountV1
    from src.core.managed_asset_lifecycle_types_v1 import ManagedAssetLifecycleStateV1

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean-mathlib"
MODULE = "RegisteredSupplyHoldingsV1"
NAMESPACE = f"Proofs.{MODULE}"
MODULE_SOURCE = PROJECT / "Proofs" / f"{MODULE}.lean"

# The producer module imports RegisteredSupplySupportV1 and the existing global
# state-closure chain.  Keep the complete transitive set explicit: this is a
# fresh source-pinned closure, not an import of the repository's compiled cache.
DEPENDENCIES: Final[tuple[str, ...]] = (
    "GlobalSettlementCoreV2",
    "GlobalEconomicStateRefinementV2",
    "RegisteredSupplySupportV1",
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
    "AssetTransferSparseStateAdmissionV1",
    "AssetTransferSparseAuthorizationV1",
    "AssetTransferPolicySelectionV1",
    "AssetTransferEffectPlanV1",
    "AssetTransferFeeMirrorEligibilityV1",
    "AssetTransferAnnotationMirrorsV1",
    "AssetTransferCustodyEffectPlanV1",
    "AssetTransferGlobalSuccessorV1",
    "AssetTransferGlobalStateClosureV1",
)

FORMAL_SOURCE_PINS: Final[dict[str, str]] = {
    "GlobalSettlementCoreV2": "2ce254367dc8e8299f82f8a93e09c1d470f3a218ed01af7efb766946a34255a4",
    "GlobalEconomicStateRefinementV2": "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    "CheckedEconomicAggregationV1": "b72155a1f32f01a5c96df725358d7fbc55d5014ee0d9894e6743516d37b04e4b",
    "CheckedEpochEconomicTablesV1": "ee6ebc40358879e168cbc245be1641a06e084a39642d5da2736caacfa60897cd",
    "AssetTransferRefinementV1": "2d9ed7beb6feb47b67afa63a40d1203bcca9004b49ba978b9927edded6a04932",
    "AssetTransferCustodyCompletionV1": "fc6869b223a427ef22d040e71276d57c1f7b5bca9b95b471d4059ae771a1f8dc",
    "CheckedSignedDeltaRefinementV1": "3a0b3e18a069b14c8fec4e705178a73cb1b3356d9813195e5e7c35b09cf74a4d",
    "AssetTransferCustodyCompositionV1": "37375e914576993767eae7484e620e54be300798785b2a57a9953e86be2f34d2",
    "CanonicalEpochEconomicRowsV1": "5ff80f22fde38729468dc237dd5b40a28bacc57302a483bf42b3e9f90122fe64",
    "AssetTransferSparseTablesV1": "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "AssetTransferSparseTraceV1": "5a77ac04b4e214ab7d0dc6cb4b77e2369e16a7914d02cffb5df1d0b88f119b83",
    "AssetTransferSparseSupplyV1": "e2c056cba91173f6c454f4b60c1adc228d9ffd7df58a9cebcdbbc0e9b46a683d",
    "AssetTransferSparseStateAdmissionV1": "82f54f4d5a5ba5e28a2ed2a96cd6b4155e70458c05d104b31eea0717aaae8649",
    "AssetTransferSparseAuthorizationV1": "91d41486e814f80a876746a1d8a542daeda77599415792b0915f4a2fccc495fa",
    "AssetTransferPolicySelectionV1": "6c330fb920885223089d774eaf6110a3007bd2790a3c69dc947f80255edff321",
    "AssetTransferEffectPlanV1": "14cea53d90e1fdc6f068e581dcc8e737526475b323100c5d6c27b9354f769de9",
    "AssetTransferFeeMirrorEligibilityV1": "03ae7a9c1db3b8355fb2cd3f09206565cee524c3c735855a0af6c5287ecc5a10",
    "AssetTransferAnnotationMirrorsV1": "81e0fae0addd597b509f7890e4fa8cb1206f6b650414a5db948fcb75633afc30",
    "AssetTransferCustodyEffectPlanV1": "77364c36dbd2f8730ec9683167915b914e2ad9a4aa5a7d9c726e69bf89f8fa23",
    "AssetTransferGlobalSuccessorV1": "8375d3cbd6bf4bd4c911527a03de5d12b7bb21df0b0135cd1dd0d1951e60dc56",
    "AssetTransferGlobalStateClosureV1": "4569ef906325cf08a0f02cca8932f07735a7dc94a5250f6e612c54e1ef7e0ddb",
    "RegisteredSupplySupportV1": "cbd01b5eef5d932843ded7d3060611c846ad0dbc4c164bd5f15cbbbfa4e14f6e",
    MODULE: "11bf6dbeb35305d8321cb24dfecec14226d0277ac4f09c531f5ae588f141ba46",
}

RUNTIME_SOURCE_PINS: Final[dict[str, str]] = {
    "src/core/asset_lane_projection_v1.py": "5420112e2dd321ce7f74604e66c13933ca714fc93467150f5cb6358f403b6839",
    "src/core/managed_asset_lifecycle_module_v1.py": "3a279bf3c5fa97d942c79f9c25025c0a24cbe7f24cfb91df5de43da38e831e36",
    "src/core/managed_asset_lifecycle_types_v1.py": "f85ffc59628b673258ad6d72a9b6f8151f9def09e9e508aa2ec060251d75f315",
    "src/core/asset_transfer_types_v1.py": "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_settlement_types_v1.py": "854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4",
    "tests/core/test_managed_asset_lifecycle_boundaries_v1.py": "c4eeff55153df89a17e20c8b37756cc7938f725fca03b4420924dff65c2aad41",
}

THEOREM_TYPES: Final[dict[str, str]] = {
    "support_relation_of_admitted_owned": (
        f"∀ {{state : {NAMESPACE}.K.State}}, "
        f"{NAMESPACE}.K.StateAdmitted state → "
        f"{NAMESPACE}.G.OwnedMatchesSupply state.economic → "
        f"{NAMESPACE}.SupportRelation state"
    ),
    "support_relation_of_invariant": (
        f"∀ {{state : {NAMESPACE}.K.State}}, "
        f"{NAMESPACE}.Z.StateInvariant state → "
        f"{NAMESPACE}.SupportRelation state"
    ),
    "support_relation_physical": (
        f"∀ {{state : {NAMESPACE}.K.State}}, "
        f"{NAMESPACE}.K.StateAdmitted state → "
        f"{NAMESPACE}.G.OwnedMatchesSupply state.economic → "
        f"state.economic.reserves = [] → ∀ asset, "
        f"{NAMESPACE}.G.supplyFor "
        f"({NAMESPACE}.R.encode ({NAMESPACE}.sourceRows state)).numericSupplyRows asset = "
        f"{NAMESPACE}.G.amountForAsset state.economic.balances asset + "
        f"{NAMESPACE}.G.amountForAsset state.economic.custody asset"
    ),
    "support_relation_physical_of_invariant": (
        f"∀ {{state : {NAMESPACE}.K.State}}, "
        f"{NAMESPACE}.Z.StateInvariant state → ∀ asset, "
        f"{NAMESPACE}.G.supplyFor "
        f"({NAMESPACE}.R.encode ({NAMESPACE}.sourceRows state)).numericSupplyRows asset = "
        f"{NAMESPACE}.G.amountForAsset state.economic.balances asset + "
        f"{NAMESPACE}.G.amountForAsset state.economic.custody asset"
    ),
    "continued_state_support_relation": (
        f"∀ {{input : {NAMESPACE}.X.Input}}, "
        f"{NAMESPACE}.X.Admitted input → "
        f"{NAMESPACE}.SupportRelation "
        f"({NAMESPACE}.Z.continuedState input)"
    ),
    "continued_state_support_relation_accepted": (
        f"∀ {{input : {NAMESPACE}.X.Input}}, "
        f"{NAMESPACE}.X.Admitted input → "
        f"({NAMESPACE}.K.step input.transfer).verdict = .accepted → "
        f"{NAMESPACE}.SupportRelation ({NAMESPACE}.Z.continuedState input) ∧ "
        f"{NAMESPACE}.Z.continuedState input = "
        f"{{ ({NAMESPACE}.X.result input).post with "
        f"economic := {NAMESPACE}.X.successor input }}"
    ),
    "continued_state_support_relation_rejected": (
        f"∀ {{input : {NAMESPACE}.X.Input}} "
        f"{{code : Proofs.AssetTransferRefinementV1.RejectCode}}, "
        f"{NAMESPACE}.X.Admitted input → "
        f"({NAMESPACE}.K.step input.transfer).verdict = .rejected code → "
        f"{NAMESPACE}.SupportRelation ({NAMESPACE}.Z.continuedState input) ∧ "
        f"{NAMESPACE}.Z.continuedState input = input.transfer.pre"
    ),
}

OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open Proofs.AssetTransferRefinementV1
open Proofs.AssetTransferPolicySelectionV1
open Proofs.AssetTransferGlobalSuccessorV1
open Proofs.AssetTransferGlobalStateClosureV1
open {NAMESPACE}
"""


class LeanSubject:
    def __init__(self, executable: Path, source: Path, library: Path) -> None:
        self.executable = executable
        self.source = source
        self.library = library


def _compile(
    subject: LeanSubject,
    path: Path,
    output: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    command = [str(subject.executable), "-DwarningAsError=true", "-R", str(subject.source)]
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
        timeout=180,
    )


def _topological_dependencies() -> tuple[str, ...]:
    graph: dict[str, tuple[str, ...]] = {}

    def visit(name: str) -> None:
        if name in graph:
            return
        path = PROJECT / "Proofs" / f"{name}.lean"
        imports = tuple(re.findall(r"^import Proofs\.([A-Za-z0-9_]+)", path.read_text(), re.MULTILINE))
        graph[name] = imports
        for imported in imports:
            visit(imported)

    visit(MODULE)
    order: list[str] = []
    visited: set[str] = set()

    def emit(name: str) -> None:
        if name in visited:
            return
        visited.add(name)
        for imported in graph[name]:
            emit(imported)
        order.append(name)

    emit(MODULE)
    assert tuple(order[:-1]) == DEPENDENCIES, (order, DEPENDENCIES)
    assert set(order) == set(DEPENDENCIES) | {MODULE}
    return tuple(order)


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    assert PROJECT.joinpath("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    located = subprocess.run(
        ["elan", "which", "lean"], cwd=PROJECT, capture_output=True, text=True,
        check=True, timeout=30,
    )
    executable = Path(located.stdout.strip())
    version = subprocess.run(
        [str(executable), "--version"], capture_output=True, text=True,
        check=True, timeout=30,
    )
    assert "version 4.27.0," in version.stdout
    assert MODULE_SOURCE.is_file(), MODULE_SOURCE
    assert hashlib.sha256(MODULE_SOURCE.read_bytes()).hexdigest() == FORMAL_SOURCE_PINS[MODULE]
    order = _topological_dependencies()
    directory = tmp_path_factory.mktemp("registered-supply-holdings")
    source, library = directory / "source", directory / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    for name in order:
        dependency = PROJECT / "Proofs" / f"{name}.lean"
        assert hashlib.sha256(dependency.read_bytes()).hexdigest() == FORMAL_SOURCE_PINS[name]
        captured = source / "Proofs" / f"{name}.lean"
        captured.write_bytes(dependency.read_bytes())
        result = _compile(subject, captured, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return subject


def _probe(lean: LeanSubject, name: str, body: str, opens: str = OPENS) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{opens}{body}")
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _decode_nested(output: str) -> object:
    lines = [line for line in output.splitlines() if line.strip()]
    assert len(lines) == 1, output
    return json.loads(json.loads(lines[0]))


def _structure_fields(source: str, name: str) -> tuple[str, ...]:
    block = re.search(
        rf"^structure {name}\b.*?(?=^\S)", source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert block is not None, name
    return tuple(re.findall(r"^  (\w+) :", block.group(0), flags=re.MULTILINE))


CLOSURE_NAMESPACE = "Proofs.AssetTransferGlobalStateClosureV1"
SUCCESSOR_NAMESPACE = "Proofs.AssetTransferGlobalSuccessorV1"

CONTINUATION_OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open Proofs.AssetTransferPolicySelectionV1
open {SUCCESSOR_NAMESPACE} (Admitted FeeEligible SingleEnabledLane pre fields result successor
  acceptedWitness successor_verified step_accepted step_rejected_exact successor_metadata
  insertReplay successorRoots)
open {CLOSURE_NAMESPACE} (continuedState continuedState_accepted continuedState_static_frame)
namespace H
export {NAMESPACE}
  (SupportRelation sourceRows continued_state_support_relation
   continued_state_support_relation_accepted continued_state_support_relation_rejected)
end H
namespace Z
export {CLOSURE_NAMESPACE} (continuedState)
end Z
namespace X
export {SUCCESSOR_NAMESPACE} (result successor)
end X
attribute [local instance] lexOrd
"""


def _holdings_requirements(tag: str, next_tag: str) -> str:
    """Spell every existing continuation premise for an independent consumer."""
    return f"""
theorem {tag}_requirements :
    {CLOSURE_NAMESPACE}.ContinuationRequirements
      ({CLOSURE_NAMESPACE}.continuedState {tag}Global) {next_tag}Global := by
  refine {{
    pre := ?_,
    context := ?_,
    height := ?_,
    heightFits := ?_,
    freshReplay := ?_,
    freshOccurrence := ?_,
    preLaneRoot := ?_,
    laneRootChanged := ?_,
    commandWellFormed := ?_,
    feeEligible := ?_ }}
  · rfl
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · rfl
  · unfold FitsU64
    decide
  · decide
  · intro replayId prior lookup
    change (if replayId = {tag}Occurrence.replayId then some {tag}Occurrence.occurrenceId
      else {tag}Replay replayId) = some prior at lookup
    split at lookup
    · cases lookup
      decide
    · simp only [{tag}Replay] at lookup
      split at lookup
      · cases lookup
        decide
      · cases lookup
  · rfl
  · decide
  · exact ⟨by decide, by decide⟩
  · exact {next_tag}_fee_eligible
"""

PRIMARY_WITNESS = r'''
namespace HoldingsPrimaryWitness

namespace K
export Proofs.AssetTransferPolicySelectionV1
  (State StateAdmitted PoliciesAdmitted SuppliesAdmitted policyKey supplyKey)
end K

namespace G
export Proofs.GlobalEconomicStateRefinementV2
  (GlobalState AmountRow SupplyRow OwnedMatchesSupply StateQuantitiesAdmitted
   amountForAsset supplyFor ownedFor)
end G

namespace S
export Proofs.AssetTransferSparseTablesV1
  (CanonicalBalances Unique PositiveAccounts accounts)
end S

namespace T
export Proofs.AssetTransferRefinementV1 (Policy IsU128)
end T

namespace H
export Proofs.RegisteredSupplyHoldingsV1
  (sourceRows SupportRelation support_relation_of_admitted_owned
   support_relation_physical support_relation_of_invariant)
end H

namespace R
export Proofs.RegisteredSupplySupportV1
  (V1SupplyRow SupportView encode decode)
end R

def policies : List T.Policy :=
  [⟨"EUR", "eur_treasury", (0 : Int), true⟩,
   ⟨"USD", "usd_treasury", (0 : Int), true⟩]

def primaryEconomic : G.GlobalState :=
  { Proofs.GlobalEconomicStateRefinementV2.staticGlobalState with
    balances := [⟨"alice", "USD", "accounts", (4 : Int)⟩]
    supplies := [⟨"EUR", (0 : Int)⟩, ⟨"USD", (10 : Int)⟩]
    custody := [⟨"vault", "USD", "vault", (6 : Int)⟩]
    reserves := [] }

def primaryState : K.State :=
  { moduleReleaseId := "release:primary"
    policies := policies
    economic := primaryEconomic }

theorem primary_canonical : S.CanonicalBalances primaryEconomic.balances := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · unfold S.Unique
    decide
  · intro row member
    simp [primaryEconomic] at member
    rcases member with rfl
    exact ⟨by decide, by unfold T.IsU128; decide, by decide⟩

theorem primary_policies_admitted : K.PoliciesAdmitted policies := by
  unfold K.PoliciesAdmitted K.policyKey
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro policy member
  simp [policies] at member
  rcases member with rfl | rfl <;> unfold T.IsU128 <;> decide

theorem primary_supplies_admitted : K.SuppliesAdmitted primaryEconomic.supplies := by
  unfold K.SuppliesAdmitted K.supplyKey
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro supply member
  simp [primaryEconomic] at member
  rcases member with rfl | rfl <;> unfold T.IsU128 <;> decide

theorem primary_state_admitted : K.StateAdmitted primaryState := by
  refine ⟨primary_canonical, ?_, ?_, by decide, ?_⟩
  · simpa only [primaryState] using primary_policies_admitted
  · simpa only [primaryState] using primary_supplies_admitted
  · intro asset
    by_cases eur : "EUR" = asset
    · subst asset
      decide
    · by_cases usd : "USD" = asset
      · subst asset
        decide
      · simp [primaryState, primaryEconomic, G.amountForAsset, G.supplyFor, eur, usd]

theorem primary_owned : G.OwnedMatchesSupply primaryEconomic := by
  intro asset
  by_cases eur : "EUR" = asset
  · subst asset
    decide
  · by_cases usd : "USD" = asset
    · subst asset
      decide
    · simp [primaryEconomic, G.ownedFor, G.amountForAsset, G.supplyFor, eur, usd]

theorem primary_relation : H.SupportRelation primaryState :=
  H.support_relation_of_admitted_owned primary_state_admitted primary_owned

theorem primary_physical : ∀ asset,
    G.supplyFor (R.encode (H.sourceRows primaryState)).numericSupplyRows asset =
      G.amountForAsset primaryEconomic.balances asset +
        G.amountForAsset primaryEconomic.custody asset :=
  H.support_relation_physical primary_state_admitted primary_owned (by rfl)

example : ¬ G.StateQuantitiesAdmitted primaryEconomic := by
  intro admitted
  have rows := admitted.2.2.2.1
  have zero := rows (⟨"EUR", (0 : Int)⟩) (by simp [primaryEconomic])
  exact zero.2 (by decide)

example : List.Pairwise (fun left right => compare left right = .lt)
    ((H.sourceRows primaryState).map
      Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset) :=
  Proofs.RegisteredSupplyHoldingsV1.SupportRelation.sourceKeysOrdered primary_relation

example : (R.encode (H.sourceRows primaryState)).registeredAssetKeys = ["EUR", "USD"] := by
  decide

example : (R.encode (H.sourceRows primaryState)).numericSupplyRows = [⟨"USD", (10 : Int)⟩] := by
  decide

example : R.decode (R.encode (H.sourceRows primaryState)) = H.sourceRows primaryState := by
  exact Proofs.RegisteredSupplyHoldingsV1.SupportRelation.rawRoundtrip primary_relation

example : G.supplyFor (R.encode (H.sourceRows primaryState)).numericSupplyRows "EUR" = 0 := by
  decide

example : G.supplyFor (R.encode (H.sourceRows primaryState)).numericSupplyRows "USD" = 10 := by
  decide

example : G.ownedFor primaryEconomic "EUR" = 0 := by decide
example : G.ownedFor primaryEconomic "USD" = 10 := by decide

/- Equal empty numeric support and numeric ordering do not establish complete
   registered-key ordering.  This reversed all-zero source is kept as an
   independent countermodel for the complete-key relation field. -/
def allZeroForward : List R.V1SupplyRow :=
  [⟨"EUR", (0 : Int)⟩, ⟨"USD", (0 : Int)⟩]

def allZeroReverse : List R.V1SupplyRow :=
  [⟨"USD", (0 : Int)⟩, ⟨"EUR", (0 : Int)⟩]

example : (R.encode allZeroForward).numericSupplyRows = [] := by decide
example : (R.encode allZeroReverse).numericSupplyRows = [] := by decide
example : (R.encode allZeroForward).numericSupplyRows =
    (R.encode allZeroReverse).numericSupplyRows := by decide
example : List.Pairwise (fun left right => compare left right = .lt)
    (allZeroForward.map Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset) := by decide
example : List.Pairwise (fun left right => compare left right = .lt)
    ((R.encode allZeroReverse).numericSupplyRows.map
      Proofs.GlobalEconomicStateRefinementV2.SupplyRow.asset) := by decide
example : ¬ List.Pairwise (fun left right => compare left right = .lt)
    (allZeroReverse.map Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset) := by decide

/- A full-ownership state may have one reserve atom; the physical corollary
   below is intentionally only applied to an explicitly empty reserve table. -/
def reserveEconomic : G.GlobalState :=
  { primaryEconomic with
    custody := [⟨"vault", "USD", "vault", (5 : Int)⟩]
    reserves := [⟨"reserve", "USD", "reserve", (1 : Int)⟩] }

def reserveState : K.State :=
  { primaryState with economic := reserveEconomic }

theorem reserve_admitted : K.StateAdmitted reserveState := by
  simpa only [reserveState, reserveEconomic] using primary_state_admitted

theorem reserve_owned : G.OwnedMatchesSupply reserveEconomic := by
  intro asset
  by_cases eur : "EUR" = asset
  · subst asset
    decide
  · by_cases usd : "USD" = asset
    · subst asset
      decide
    · simp [reserveEconomic, primaryEconomic, G.ownedFor, G.amountForAsset, G.supplyFor,
        eur, usd]

theorem reserve_relation : H.SupportRelation reserveState :=
  H.support_relation_of_admitted_owned reserve_admitted reserve_owned

example : G.ownedFor reserveEconomic "USD" = 10 := by decide

 def emptyReserveMismatch : G.GlobalState :=
  { reserveEconomic with reserves := [] }

example : ¬ G.OwnedMatchesSupply emptyReserveMismatch := by
  intro owned
  have mismatch := owned "USD"
  simp [emptyReserveMismatch, reserveEconomic, primaryEconomic, G.ownedFor,
    G.amountForAsset, G.supplyFor]
    at mismatch

#eval IO.println (reprStr (reprStr [
  ["POLICY_KEYS", reprStr (policies.map K.policyKey)],
  ["SUPPLY_ROWS", reprStr (primaryEconomic.supplies.map (fun row => [row.asset, toString row.amountAtoms]))],
  ["REGISTERED_KEYS", reprStr (R.encode (H.sourceRows primaryState)).registeredAssetKeys],
  ["NUMERIC_ROWS", reprStr ((R.encode (H.sourceRows primaryState)).numericSupplyRows.map fun row =>
    [row.asset, toString row.amountAtoms])],
  ["DECODED_ROWS", reprStr ((R.decode (R.encode (H.sourceRows primaryState))).map fun row =>
    [row.asset, toString row.amountAtoms])],
  ["EUR_LOOKUP", toString (G.supplyFor
    (R.encode (H.sourceRows primaryState)).numericSupplyRows "EUR")],
  ["USD_LOOKUP", toString (G.supplyFor
    (R.encode (H.sourceRows primaryState)).numericSupplyRows "USD")],
  ["EUR_OWNED", toString (G.ownedFor primaryEconomic "EUR")],
  ["USD_OWNED", toString (G.ownedFor primaryEconomic "USD")]
]))

end HoldingsPrimaryWitness
'''


def test_public_holdings_contract_has_independent_consumers_and_no_forbidden_axioms(
    lean: LeanSubject,
) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == tuple(THEOREM_TYPES)
    assert _structure_fields(code, "SupportRelation") == (
        "sourceKeysUnique",
        "sourceRowsU128",
        "rawRoundtrip",
        "registeredKeys",
        "sourceKeysOrdered",
        "numericSupportAdmitted",
        "numericKeysSublist",
        "numericKeysOrdered",
        "lookupOwned",
    )
    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    report = " ".join(_probe(lean, "IndependentHoldingsConsumers", consumers).split())
    for name in THEOREM_TYPES:
        found = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
            report,
        )
        assert found, (name, report)
        axioms = {item.strip() for item in (found.group(1) or "").split(",") if item.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)
    registry = (PROJECT / "Proofs.lean").read_text().splitlines()
    assert registry.count(f"import {NAMESPACE}") == 1
    for name, digest in FORMAL_SOURCE_PINS.items():
        path = PROJECT / "Proofs" / f"{name}.lean"
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, name


def test_zero_supply_identity_physical_lookup_and_reserve_countermodel(
    lean: LeanSubject,
) -> None:
    output = _probe(lean, "HoldingsPrimaryWitness", PRIMARY_WITNESS)
    observed = _decode_nested(output)
    assert observed == [
        ["POLICY_KEYS", '["EUR", "USD"]'],
        ["SUPPLY_ROWS", '[["EUR", "0"], ["USD", "10"]]'],
        ["REGISTERED_KEYS", '["EUR", "USD"]'],
        ["NUMERIC_ROWS", '[["USD", "10"]]'],
        ["DECODED_ROWS", '[["EUR", "0"], ["USD", "10"]]'],
        ["EUR_LOOKUP", "0"],
        ["USD_LOOKUP", "10"],
        ["EUR_OWNED", "0"],
        ["USD_OWNED", "10"],
    ]


SECOND_ACCEPTED_THEOREM = """
theorem first_accepted : (step firstTransfer).verdict = .accepted := by decide
theorem second_accepted : (step secondTransfer).verdict = .accepted := by
  have carriedBalances :
      (continuedState firstGlobal).economic.balances = secondEconomic.balances := by
    rw [continuedState_accepted first_accepted]
    change Proofs.CanonicalEpochEconomicRowsV1.sortOn
      Proofs.AssetTransferSparseTablesV1.balanceWire
        [⟨"bob", "USD", "accounts", (10 : Int)⟩,
         ⟨"alice", "USD", "accounts", (35 : Int)⟩,
         ⟨"alice", "EUR", "accounts", (9 : Int)⟩] = _
    simp +decide [Proofs.CanonicalEpochEconomicRowsV1.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop,
      secondEconomic]
  unfold step
  simp only [secondTransfer, (continuedState_static_frame firstGlobal).1,
    (continuedState_static_frame firstGlobal).2]
  change (Proofs.AssetTransferSparseTablesV1.step
    (selectedInput secondTransfer ⟨"USD", "bob", (1 : Int), true⟩)).verdict = .accepted
  unfold Proofs.AssetTransferSparseTablesV1.step
  simp only [Proofs.AssetTransferSparseTablesV1.leaf,
    Proofs.AssetTransferSparseTablesV1.localState,
    Proofs.AssetTransferSparseTablesV1.checkedBalances,
    selectedInput, secondTransfer, carriedBalances,
    (continuedState_static_frame firstGlobal).1]
  decide
"""


def _accepted_continuation_fixture():
    from tests.formal.test_lean_asset_transfer_global_state_closure_v1 import _accepted_pair

    pair = _accepted_pair()
    first, first_accepted, _, first_post, second, second_accepted, _, second_post = pair
    assert first.module_input.command.amount_atoms == 4
    assert second.module_input.command.amount_atoms == 2
    assert second.pre_global == first_post
    assert second_post.height == first_post.height + 1
    assert (
        second_accepted.private_port.post_state.supplies
        == first_accepted.private_port.post_state.supplies
    )
    return pair


def _accepted_continuation_source(pair) -> str:
    from tests.formal.test_lean_asset_transfer_global_state_closure_v1 import (
        _lean_fee_eligible_carried,
        _lean_mirror_carried,
    )
    from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
        _lean_admission,
        _lean_admitted_record,
        _lean_fee_eligible,
        _lean_mirror,
    )

    first, first_accepted, _, first_post, second, second_accepted, _, second_post = pair
    return (
        _lean_mirror(
            first,
            first_accepted.private_port.post_state.state_root,
            first_post.state_root,
            "first",
        )
        + _lean_mirror_carried(
            second,
            second_accepted.private_port.post_state.state_root,
            second_post.state_root,
            "second",
            f"{CLOSURE_NAMESPACE}.continuedState firstGlobal",
        )
        + _lean_admission("first")
        + _lean_fee_eligible("first")
        + _lean_admitted_record("first")
        + _lean_fee_eligible_carried("second")
    )


def _accepted_continuation_body(pair) -> str:
    return (
        _accepted_continuation_source(pair)
        + SECOND_ACCEPTED_THEOREM
        + _holdings_requirements("first", "second")
        + f"""
example : H.SupportRelation (Z.continuedState firstGlobal) ∧
    Z.continuedState firstGlobal =
      {{ (X.result firstGlobal).post with economic := X.successor firstGlobal }} :=
  H.continued_state_support_relation_accepted first_admitted first_accepted

def second_admitted : {SUCCESSOR_NAMESPACE}.Admitted secondGlobal :=
  {CLOSURE_NAMESPACE}.continuation_admitted first_admitted first_requirements

example : H.SupportRelation (Z.continuedState secondGlobal) :=
  H.continued_state_support_relation second_admitted

example : H.SupportRelation (Z.continuedState secondGlobal) ∧
    Z.continuedState secondGlobal =
      {{ (X.result secondGlobal).post with economic := X.successor secondGlobal }} :=
  H.continued_state_support_relation_accepted second_admitted second_accepted
"""
    )


def test_positive_global_continuation_consumes_holdings_relation(lean: LeanSubject) -> None:
    """Use the actual two-transfer witness and the accepted continuation corollary."""
    pair = _accepted_continuation_fixture()
    assert _probe(
        lean,
        "RegisteredHoldingsAcceptedContinuation",
        _accepted_continuation_body(pair),
        CONTINUATION_OPENS,
    ) == ""


def _rejected_continuation_fixture():
    from tests.formal.test_lean_asset_transfer_global_state_closure_v1 import (
        _accepted_pair,
        _next_witness,
    )

    first, first_accepted, _, first_post, *_ = _accepted_pair()
    rejected = _next_witness(
        first,
        first_accepted,
        first_post,
        amount=0,
        nonce=7,
        op_index=2,
    )
    assert rejected.module_input.command.amount_atoms == 0
    assert rejected.pre_global == first_post
    return first, first_accepted, first_post, rejected


def _rejected_continuation_body(fixture) -> str:
    from tests.formal.test_lean_asset_transfer_global_state_closure_v1 import (
        _lean_fee_eligible_carried,
        _lean_mirror_carried,
    )
    from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
        _lean_admission,
        _lean_admitted_record,
        _lean_fee_eligible,
        _lean_mirror,
    )
    first, first_accepted, first_post, rejected = fixture
    requirements = _holdings_requirements("first", "rejected")
    body = (
        _lean_mirror(
            first,
            first_accepted.private_port.post_state.state_root,
            first_post.state_root,
            "first",
        )
        + _lean_mirror_carried(
            rejected,
            "0x" + "cc" * 32,
            "0x" + "dd" * 32,
            "rejected",
            f"{CLOSURE_NAMESPACE}.continuedState firstGlobal",
        )
        + _lean_admission("first")
        + _lean_fee_eligible("first")
        + _lean_admitted_record("first")
        + _lean_fee_eligible_carried("rejected")
        + """
theorem first_accepted : (step firstTransfer).verdict = .accepted := by decide
theorem rejected_leaf :
    (step rejectedTransfer).verdict = .rejected .zeroAmount := by decide
"""
        + requirements
        + f"""
def rejected_admitted : {SUCCESSOR_NAMESPACE}.Admitted rejectedGlobal :=
  {CLOSURE_NAMESPACE}.continuation_admitted first_admitted first_requirements

example : H.SupportRelation (Z.continuedState rejectedGlobal) ∧
    Z.continuedState rejectedGlobal = rejectedGlobal.transfer.pre :=
  H.continued_state_support_relation_rejected rejected_admitted rejected_leaf
"""
    )
    return body


def test_rejected_global_continuation_consumes_holdings_relation_as_exact_noop(
    lean: LeanSubject,
) -> None:
    fixture = _rejected_continuation_fixture()
    assert _probe(
        lean,
        "RegisteredHoldingsRejectedContinuation",
        _rejected_continuation_body(fixture),
        CONTINUATION_OPENS,
    ) == ""


# ---------------------------------------------------------------------------------------
# Runtime observations: exact V1 rows, zero-supply identity, and lifecycle controls.


RUNTIME_ROOT_A = "0x" + "01" * 32
RUNTIME_ROOT_B = "0x" + "02" * 32


def _assert_runtime_source_pins() -> None:
    for relative, digest in RUNTIME_SOURCE_PINS.items():
        path = ROOT / relative
        assert path.is_file(), path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, relative


def _runtime_two_asset_state() -> AssetTransferStateV1:
    from src.core.asset_transfer_types_v1 import (
        AssetTransferPolicyV1,
        AssetTransferStateV1,
    )
    from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1

    return AssetTransferStateV1(
        module_release_id=RUNTIME_ROOT_A,
        policies=(
            AssetTransferPolicyV1("EUR", "eur_treasury", 0, True),
            AssetTransferPolicyV1("USD", "usd_treasury", 0, True),
        ),
        balances=(EconomicAmountV1("alice", "USD", "accounts", 4),),
        supplies=(AssetSupplyV1("EUR", 0), AssetSupplyV1("USD", 10)),
    )


def _runtime_project(
    state: AssetTransferStateV1,
    custody: tuple[EconomicAmountV1, ...],
) -> AssetLaneStateProjectionV1:
    from src.core.asset_lane_projection_v1 import project_asset_transfer_state_v1

    return project_asset_transfer_state_v1(
        state,
        asset_policy_registry_root=RUNTIME_ROOT_A,
        fee_policy_registry_root=RUNTIME_ROOT_B,
        custody=custody,
    )


def _runtime_reject(name: str, thunk: Callable[[], object]) -> tuple[str, str, str]:
    try:
        thunk()
    except Exception as exc:  # noqa: BLE001 - exact bounded observation helper.
        return name, type(exc).__name__, str(exc)
    raise AssertionError(f"{name} unexpectedly accepted")


def _runtime_duplicate_source():
    from src.core.asset_transfer_types_v1 import AssetTransferPolicyV1, AssetTransferStateV1
    from src.core.global_settlement_types_v1 import AssetSupplyV1

    return AssetTransferStateV1(
        module_release_id=RUNTIME_ROOT_A,
        policies=(AssetTransferPolicyV1("USD", "treasury", 0, True),),
        balances=(),
        supplies=(AssetSupplyV1("USD", 1), AssetSupplyV1("USD", 2)),
    )


def _runtime_omitted_zero_source():
    from src.core.asset_transfer_types_v1 import AssetTransferPolicyV1, AssetTransferStateV1
    from src.core.global_settlement_types_v1 import AssetSupplyV1

    return AssetTransferStateV1(
        module_release_id=RUNTIME_ROOT_A,
        policies=(
            AssetTransferPolicyV1("EUR", "eur_treasury", 0, True),
            AssetTransferPolicyV1("USD", "usd_treasury", 0, True),
        ),
        balances=(),
        supplies=(AssetSupplyV1("USD", 10),),
    )


RUNTIME_REJECTION_EXPECTED: Final[tuple[tuple[str, str, str], ...]] = (
    (
        "unknown_asset_holding",
        "ValueError",
        "asset lane holding references an unnamed supply",
    ),
    (
        "duplicate_supply_key",
        "ValueError",
        "asset transfer supplies must be canonically ordered and unique",
    ),
    (
        "omitted_zero_supply_key",
        "ValueError",
        "asset transfer policies and supplies must cover the same assets",
    ),
    ("holdings_mismatch", "ValueError", "owned and custodied total must equal supply"),
)


def _runtime_rejection_observations(state: AssetTransferStateV1):
    from src.core.global_settlement_types_v1 import EconomicAmountV1

    return (
        _runtime_reject(
            "unknown_asset_holding",
            lambda: _runtime_project(
                state,
                (EconomicAmountV1("vault", "GBP", "vault", 1),),
            ),
        ),
        _runtime_reject("duplicate_supply_key", _runtime_duplicate_source),
        _runtime_reject("omitted_zero_supply_key", _runtime_omitted_zero_source),
        _runtime_reject("holdings_mismatch", lambda: _runtime_project(state, ())),
    )


def test_runtime_registered_zero_and_positive_projection_matches_lean_view() -> None:
    from src.core.global_settlement_types_v1 import EconomicAmountV1

    _assert_runtime_source_pins()
    state = _runtime_two_asset_state()
    before = state.to_canonical()
    projected = _runtime_project(
        state,
        (EconomicAmountV1("vault", "USD", "vault", 6),),
    )

    # These are the exact finite values emitted by PRIMARY_WITNESS above.
    assert tuple(policy.asset for policy in state.policies) == ("EUR", "USD")
    assert tuple((row.asset, row.amount_atoms) for row in state.supplies) == (
        ("EUR", 0),
        ("USD", 10),
    )
    assert tuple((row.asset, row.amount_atoms) for row in projected.supplies) == (
        ("EUR", 0),
        ("USD", 10),
    )
    assert projected.owned_and_custodied_atoms("EUR") == 0
    assert projected.owned_and_custodied_atoms("USD") == 10
    assert projected.supply_atoms("EUR") == 0
    with pytest.raises(ValueError, match="unknown asset lane supply"):
        projected.supply_atoms("GBP")
    assert state.to_canonical() == before


def test_runtime_managed_issue_from_zero_and_full_burn_keep_zero_row_identity() -> None:
    from src.core.asset_lane_projection_v1 import project_managed_asset_lifecycle_state_v1
    from src.core.managed_asset_lifecycle_module_v1 import (
        transition_managed_asset_lifecycle_v1,
    )
    from src.core.managed_asset_lifecycle_types_v1 import ManagedAssetLifecycleAcceptedV1
    from tests.core.test_managed_asset_lifecycle_boundaries_v1 import (
        I128_MIN_MAGNITUDE,
        _command,
        _context,
        _state,
    )

    _assert_runtime_source_pins()

    def project(state: ManagedAssetLifecycleStateV1) -> AssetLaneStateProjectionV1:
        return project_managed_asset_lifecycle_state_v1(
            state,
            asset_policy_registry_root=RUNTIME_ROOT_A,
            fee_policy_registry_root=RUNTIME_ROOT_B,
        )

    issue_pre = _state(account_atoms=0, supply_atoms=0)
    issue_before = issue_pre.to_canonical()
    issue_result = transition_managed_asset_lifecycle_v1(
        _context(issue=True),
        issue_pre,
        _command(issue=True, amount_atoms=1),
    )
    assert type(issue_result) is ManagedAssetLifecycleAcceptedV1
    issue_pre_projection = project(issue_pre)
    issue_post_projection = project(issue_result.post_state)
    assert tuple(row.asset for row in issue_pre_projection.supplies) == ("USD",)
    assert tuple(row.asset for row in issue_post_projection.supplies) == ("USD",)
    assert issue_pre_projection.supplies[0].amount_atoms == 0
    assert issue_post_projection.supplies[0].amount_atoms == 1
    assert issue_pre_projection.owned_and_custodied_atoms("USD") == 0
    assert issue_post_projection.owned_and_custodied_atoms("USD") == 1
    assert issue_pre.to_canonical() == issue_before

    burn_pre = _state(
        account_atoms=I128_MIN_MAGNITUDE,
        supply_atoms=I128_MIN_MAGNITUDE,
    )
    burn_before = burn_pre.to_canonical()
    burn_result = transition_managed_asset_lifecycle_v1(
        _context(issue=False),
        burn_pre,
        _command(issue=False, amount_atoms=I128_MIN_MAGNITUDE),
    )
    assert type(burn_result) is ManagedAssetLifecycleAcceptedV1
    burn_projection = project(burn_result.post_state)
    assert tuple((row.asset, row.amount_atoms) for row in burn_projection.supplies) == (
        ("USD", 0),
    )
    assert burn_projection.owned_and_custodied_atoms("USD") == 0
    assert burn_pre.to_canonical() == burn_before


def test_runtime_complete_source_and_rejection_controls_preserve_inputs() -> None:
    from src.core.global_settlement_types_v1 import EconomicAmountV1

    _assert_runtime_source_pins()
    state = _runtime_two_asset_state()
    before = state.to_canonical()
    custody = (EconomicAmountV1("vault", "USD", "vault", 6),)
    projected = _runtime_project(state, custody)
    assert projected.to_canonical()["supplies"] == state.supplies
    assert state.to_canonical() == before

    observations = _runtime_rejection_observations(state)
    assert observations == RUNTIME_REJECTION_EXPECTED
    assert state.to_canonical() == before
