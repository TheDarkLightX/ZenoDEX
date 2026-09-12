"""Fresh Lean replay of custody completion over accepted finite V2 source plans.

The controls cover transfer, issue, and burn from a legal state with nonzero
custody. They bind supplied complete roots and exact six-field plan values.
They do not claim runtime hashing, codec, receipt, or publication refinement.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from src.core.asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_input_v2 import _decode_context
from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    AssetTransferAcceptedV2,
    AssetTransferRejectedV2,
)
from src.core.global_settlement_abi_v2_codec import (
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
from src.core.global_settlement_types_v2 import (
    LaneIdV2,
    LaneWriteV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleRejectedV2,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    effect_plan_lean as effect_plan_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import lean as lean
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    transfer_consumer_lean as transfer_consumer_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    transfer_effect_plan_lean as transfer_effect_plan_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

REPO = Path(__file__).resolve().parents[2]
PROOFS = REPO / "lean-mathlib/Proofs"
MODULE = "AssetLaneCustodyEffectPlanV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = PROOFS / f"{MODULE}.lean"
GOLDEN_FIXTURE = REPO / "tests/data/asset_lane_custody_v2_golden.json"
GOLDEN_FIXTURE_SHA256 = "6d128ed29521daea1211b2e7e2ba1b421b833723e5b21ab2a452e89ee103a4a1"
GOLDEN_CASES = json.loads(GOLDEN_FIXTURE.read_bytes())["cases"]
SOURCE_SHA256 = "23bb4463a43b8ce8a4e234937d4f3187354cdeffef35a7645305059a1f05457a"
DEPENDENCIES = (
    ("AssetLaneCustodyRefinementV2", "df3cf08fc7b108d08efc78ab7cecbc5f86e221a80c210e6c9b5ad229699a8de9"),
    ("AssetLaneCustodyTraceV2", "fda710c542059d5041afd36bfd96746e8f208f98b8c4a31c4b723c9e9c6b9940"),
    ("AssetLaneCustodyRecompositionV2", "0ffbeb9fdc38e1bc3b9995e1b17582dd921bbab8ee0ee846d88d59587d0d42e3"),
    (MODULE, SOURCE_SHA256),
)
THEOREM_NAMES = (
    "complete_plan_fields",
    "complete_conservation_admitted",
    "complete_plan_admission",
    "transfer_rejected_empty",
    "managed_rejected_empty",
    "transfer_accepted_policy",
    "transfer_completed_row_exact",
    "transfer_accepted_conservation",
    "transfer_accepted_fields",
    "managed_source_supply",
    "recomposed_selected_supply",
    "managed_source_post_supply",
    "managed_accepted_policy",
    "managed_completed_row_exact",
    "managed_accepted_conservation",
    "managed_accepted_fields",
    "transfer_accepted_plan_admitted",
    "managed_accepted_plan_admitted",
    "transfer_accepted_completion",
    "managed_accepted_completion",
)
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
PREAMBLE = f"""import {NAMESPACE}
open Proofs
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1
open Proofs.AssetLaneCustodyRefinementV2
open {NAMESPACE}
attribute [local instance] lexOrd
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
"""


@pytest.fixture(scope="module")
def custody_effect_plan_lean(transfer_effect_plan_lean: LeanSubject) -> LeanSubject:
    """Compile every added custody layer from source after the fresh leaf closure."""

    for name, expected in DEPENDENCIES:
        source = (PROOFS / f"{name}.lean").read_bytes()
        assert hashlib.sha256(source).hexdigest() == expected
        path = transfer_effect_plan_lean.source / "Proofs" / f"{name}.lean"
        path.write_bytes(source)
        result = _compile(
            transfer_effect_plan_lean,
            path,
            transfer_effect_plan_lean.library / "Proofs" / f"{name}.olean",
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return transfer_effect_plan_lean


def _consumer(subject: LeanSubject, name: str, body: str):
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


CONTRACTS = r"""
example : ∀ {pre post : C.State} {row : AssetConservationRow},
    AssetConservationAdmitted row → C.PhysicalBalanced pre → C.PhysicalBalanced post →
    C.supplyAt pre row.asset = row.supplyPreAtoms →
    C.supplyAt post row.asset = row.supplyPostAtoms →
    AssetConservationAdmitted (completeConservationRow pre post row) :=
  @complete_conservation_admitted

example : ∀ {pre post : C.State} {completePreRoot completePostRoot : RootId}
    {source : EffectPlan}, EffectPlanAdmitted source →
    (∀ row ∈ source.assetConservation,
      AssetConservationAdmitted (completeConservationRow pre post row)) →
    source.laneWrites.length = 1 →
    EffectPlanAdmitted (completePlan pre post completePreRoot completePostRoot source) :=
  @complete_plan_admission

example : ∀ {digest : B.Bytes → String} {ctx : T.Context} {pre : C.State}
    {command : T.Command} {completePreRoot completePostRoot : RootId}
    {code : AssetTransferFiniteOutcomeV2.RejectCode},
    (FT.transition digest ctx (transferSource pre) command).verdict = .rejected code →
    transferEffectPlan digest ctx pre command completePreRoot completePostRoot = EffectPlan.empty :=
  @transfer_rejected_empty

example : ∀ {digest : B.Bytes → String} {ctx : M.Context} {pre : C.State}
    {command : M.Command} {completePreRoot completePostRoot : RootId}
    {code : ManagedAssetFiniteOutcomeV2.RejectCode},
    (FM.transition digest ctx (managedSource pre) command).verdict = .rejected code →
    managedEffectPlan digest ctx pre command completePreRoot completePostRoot = EffectPlan.empty :=
  @managed_rejected_empty

example {digest : B.Bytes → String} {ctx : T.Context} {pre : C.State}
    {command : T.Command} {completePreRoot completePostRoot : RootId}
    (roots : T.RootModel) (admitted : C.RowsRepresentable pre)
    (structural : FT.Structural (transferSource pre))
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    ∃ policy, FT.policyFor (transferSource pre) command.asset = some policy ∧
      policy ∈ pre.transferState.policies ∧
      (AssetTransferRefinementV2.transition roots ctx (C.transferView pre policy) command).verdict =
        .accepted ∧
      let post := C.transferPost pre policy command
      let completed := transferEffectPlan digest ctx pre command completePreRoot completePostRoot
      let source := TP.transferPlan digest ctx (transferSource pre) command
      completed.assetConservation = [transferCompletedConservation pre post command] ∧
        AssetConservationAdmitted (transferCompletedConservation pre post command) ∧
        EffectPlanAdmitted completed ∧
        completed.rows = source.rows ∧ completed.feeConservation = source.feeConservation ∧
        completed.laneWrites = [⟨.assetTransfer, completePreRoot, completePostRoot⟩] ∧
        completed.occurrenceConsumptions = source.occurrenceConsumptions ∧
        completed.externalOutboxEnqueue = source.externalOutboxEnqueue :=
  transfer_accepted_completion roots admitted structural accepted

example {digest : B.Bytes → String} {ctx : M.Context} {pre : C.State}
    {command : M.Command} {completePreRoot completePostRoot : RootId}
    (roots : M.RootModel) (admitted : C.RowsRepresentable pre)
    (structural : FM.Structural (managedSource pre))
    (commandAdmitted : M.CommandWellFormed command) (owner : B.ValidToken command.accountOwner)
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    ∃ policy, FM.policyFor (managedSource pre) command.asset = some policy ∧
      policy ∈ pre.managedPolicies ∧
      (ManagedAssetLifecycleRefinementV2.transition roots ctx (C.managedView pre policy) command).verdict =
        .accepted ∧
      let post := R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command)
      let completed := managedEffectPlan digest ctx pre command completePreRoot completePostRoot
      let source := MP.managedPlan digest ctx (managedSource pre) command
      completed.assetConservation = [managedCompletedConservation pre post command] ∧
        AssetConservationAdmitted (managedCompletedConservation pre post command) ∧
        EffectPlanAdmitted completed ∧
        completed.rows = source.rows ∧ completed.feeConservation = source.feeConservation ∧
        completed.laneWrites = [⟨.assetTransfer, completePreRoot, completePostRoot⟩] ∧
        completed.occurrenceConsumptions = source.occurrenceConsumptions ∧
        completed.externalOutboxEnqueue = source.externalOutboxEnqueue :=
  managed_accepted_completion roots admitted structural commandAdmitted owner accepted
"""


def test_contract_surface_signatures_axioms_and_placeholders(
    custody_effect_plan_lean: LeanSubject,
) -> None:
    source = SOURCE.read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == SOURCE_SHA256
    assert tuple(re.findall(r"^theorem\s+(\w+)", source, flags=re.MULTILINE)) == THEOREM_NAMES
    executable = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", executable) is None

    contracts = CONTRACTS + "\n" + "\n".join(
        f"#print axioms {NAMESPACE}.{name}" for name in THEOREM_NAMES
    )
    checked = _consumer(custody_effect_plan_lean, "CustodyEffectPlanContracts", contracts)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    assert _axiom_names(checked.stdout) <= STANDARD_AXIOMS
    count = len(re.findall(r"depends on axioms:|does not depend on any axioms", checked.stdout))
    assert count == len(THEOREM_NAMES)


CONTROLS = r"""
namespace EffectControls

local instance token_decidable (value : String) : Decidable (B.ValidToken value) := by
  unfold B.ValidToken
  infer_instance
local instance unique_decidable (rows : List AmountRow) :
    Decidable (AssetTransferSparseTablesV1.Unique rows) := by
  unfold AssetTransferSparseTablesV1.Unique
  infer_instance
local instance supply_unique_decidable (rows : List V1SupplyRow) :
    Decidable (SourceAssetKeysUnique rows) := by
  unfold SourceAssetKeysUnique
  infer_instance
local instance width_decidable (value : Int) : Decidable (FitsU128 value) := by
  unfold FitsU128
  infer_instance

def transferPolicy : T.Policy :=
  ⟨"A", "collector", 0, true, .registeredOrdinaryToken, some "origin", 8⟩
def managedPolicy : M.Policy :=
  ⟨"A", .registeredOrdinaryToken, some "origin", 8,
    some ⟨"issuer", "issue-grant"⟩, some "burn-grant", true⟩
def balances : List AmountRow := [⟨"sender", "A", "accounts", 5⟩]
def supplies : List V1SupplyRow := [⟨"A", 10⟩]
def custody : List AmountRow := [⟨"vault", "A", "escrow", 5⟩]
def pre : C.State :=
  { transferState := ⟨"release", [transferPolicy], balances, supplies⟩
    originRegistry := ["A"]
    managedPolicies := [managedPolicy]
    custody := custody }

def transfer : T.Command :=
  ⟨"asset_transfer", "body", "A", "sender", "recipient", 5, 0, some "origin"⟩
def transferContext : T.Context :=
  ⟨"release", "global", some ⟨"global", [], "asset_transfer", "body",
    "sender", "grant", "occurrence"⟩⟩
def issue : M.Command :=
  ⟨"managed_asset_issue", "issue-body", "A", .registeredOrdinaryToken,
    some "origin", 8, some "issue-grant", "sender", 1⟩
def issueContext : M.Context :=
  ⟨"release", "global", some ⟨"global", [], "managed_asset_issue", "issue-body",
    "issuer", "issue-grant", "issue-occ"⟩⟩
def burn : M.Command :=
  ⟨"managed_asset_burn", "burn-body", "A", .registeredOrdinaryToken,
    some "origin", 8, some "burn-grant", "sender", 1⟩
def burnContext : M.Context :=
  ⟨"release", "global", some ⟨"global", [], "managed_asset_burn", "burn-body",
    "sender", "burn-grant", "burn-occ"⟩⟩
def digest (_ : B.Bytes) : String := "abstract-leaf-root"
def transferRoots : T.RootModel := ⟨fun _ => "abstract-scalar-root"⟩

theorem rowsRepresentable : C.RowsRepresentable pre := by
  constructor
  · unfold SourceAssetKeysUnique; decide
  · unfold SourceAssetKeysOrdered; decide
  · intro row member
    have same : row = ⟨"A", 10⟩ := by simpa [pre, supplies] using member
    subst row
    decide
  · rfl
  · rfl
  · intro policy member
    have same : policy = managedPolicy := by simpa [pre] using member
    subst policy
    decide
  · unfold AssetTransferSparseTablesV1.Unique; decide
  · simp [AssetTransferSparseTablesV1.PositiveAccounts, pre, balances,
      AssetTransferSparseTablesV1.accounts, AssetTransferRefinementV1.IsU128,
      AssetTransferRefinementV1.u128Max]
  · unfold AssetTransferSparseTablesV1.Unique; decide
  · simp [pre, custody, AssetTransferSparseTablesV1.accounts, FitsU128, maxU128]
  · intro row member
    simp [pre, balances, custody] at member
    rcases member with rfl | rfl <;> decide
  · intro asset
    by_cases same : asset = "A"
    · subst asset; decide
    · have different : "A" ≠ asset := Ne.symm same
      simp [C.physicalFor, C.supplyAt, pre, balances, supplies, custody,
        amountForAsset, numericRows, nonzeroRow, toNumericRow, supplyFor, different]

def transferLeaf : FT.State :=
  ⟨"release", [transferPolicy], [⟨"sender", "A", "accounts", 5⟩], [⟨"A", 10⟩]⟩
def managedLeaf : FM.State :=
  ⟨"release", [managedPolicy], [⟨"sender", "A", "accounts", 5⟩], [⟨"A", 10⟩]⟩

theorem transferSourceEq : transferSource pre = transferLeaf := rfl
theorem managedSourceEq : managedSource pre = managedLeaf := by decide +kernel

theorem transferStructural : FT.Structural (transferSource pre) := by
  rw [transferSourceEq]
  constructor
  · decide
  · simp [transferLeaf]
  · intro policy member
    have same : policy = transferPolicy := by simpa [transferLeaf] using member
    subst policy
    decide
  · intro policy member
    have same : policy = transferPolicy := by simpa [transferLeaf] using member
    subst policy
    rfl
  · intro policy member
    have same : policy = transferPolicy := by simpa [transferLeaf] using member
    subst policy
    unfold B.ValidToken
    decide
  · exact rowsRepresentable.balanceUnique
  · exact rowsRepresentable.balancePositive
  · decide
  · intro row member
    have same : row = ⟨"sender", "A", "accounts", 5⟩ := by
      simpa [transferLeaf, balances] using member
    subst row
    decide
  · exact rowsRepresentable.supplyUnique
  · exact rowsRepresentable.supplyOrdered
  · exact rowsRepresentable.supplyBounded
  · rfl
  · intro asset
    simpa [transferLeaf, C.supplyAt] using
      (AssetLaneCustodyTraceV2.account_bounds rowsRepresentable asset).2.1
  · intro row member
    have same : row = ⟨"sender", "A", "accounts", 5⟩ := by
      simpa [transferLeaf, balances] using member
    subst row
    exact ⟨by decide, by decide, by decide⟩
  · intro row member
    have same : row = ⟨"A", 10⟩ := by simpa [transferLeaf, supplies] using member
    subst row
    decide

theorem managedStructural : FM.Structural (managedSource pre) := by
  rw [managedSourceEq]
  constructor
  · decide
  · simp [managedLeaf]
  · intro policy member
    have same : policy = managedPolicy := by simpa [managedLeaf] using member
    subst policy
    exact ⟨rfl, by intro excluded; exact False.elim (excluded rfl)⟩
  · exact rowsRepresentable.balanceUnique
  · exact rowsRepresentable.balancePositive
  · decide
  · intro row member
    have same : row = ⟨"sender", "A", "accounts", 5⟩ := by
      simpa [managedLeaf, balances] using member
    subst row
    decide
  · exact rowsRepresentable.supplyUnique
  · exact rowsRepresentable.supplyOrdered
  · exact rowsRepresentable.supplyBounded
  · rfl
  · intro asset
    simpa [managedLeaf, C.supplyAt] using
      (AssetLaneCustodyTraceV2.account_bounds rowsRepresentable asset).2.1
  · intro row member
    have same : row = ⟨"sender", "A", "accounts", 5⟩ := by
      simpa [managedLeaf, balances] using member
    subst row
    exact ⟨by decide, by decide, by decide⟩
  · intro row member
    have same : row = ⟨"A", 10⟩ := by simpa [managedLeaf, supplies] using member
    subst row
    decide

theorem issueCommand : M.CommandWellFormed issue := ⟨by decide, rfl⟩
theorem burnCommand : M.CommandWellFormed burn := ⟨by decide, rfl⟩
theorem issueOwner : B.ValidToken issue.accountOwner := by unfold B.ValidToken; decide
theorem burnOwner : B.ValidToken burn.accountOwner := by unfold B.ValidToken; decide

theorem transferSelected : FT.policyFor (transferSource pre) transfer.asset = some transferPolicy := by
  rw [transferSourceEq]
  decide
theorem issueSelected : FM.policyFor (managedSource pre) issue.asset = some managedPolicy := by
  rw [managedSourceEq]
  decide
theorem burnSelected : FM.policyFor (managedSource pre) burn.asset = some managedPolicy := by
  rw [managedSourceEq]
  decide

theorem transferAccepted :
    (FT.transition digest transferContext
      (transferSource pre) transfer).verdict = .accepted := by
  unfold digest
  rw [transferSourceEq]
  decide +kernel
theorem issueAccepted :
    (FM.transition digest issueContext
      (managedSource pre) issue).verdict = .accepted := by
  unfold digest
  rw [managedSourceEq]
  decide +kernel
theorem burnAccepted :
    (FM.transition digest burnContext (managedSource pre) burn).verdict = .accepted := by
  unfold digest
  rw [managedSourceEq]
  decide +kernel

example :
    (transferEffectPlan digest transferContext pre transfer
      "complete-pre" "complete-transfer-post").assetConservation =
        [⟨"A", 10, 10, 10, 10, 0, 0⟩] := by
  unfold digest
  decide +kernel

example :
    (managedEffectPlan digest issueContext pre issue
      "complete-pre" "complete-issue-post").assetConservation =
        [⟨"A", 10, 11, 10, 11, 1, 0⟩] := by
  unfold digest
  decide +kernel

example :
    (managedEffectPlan digest burnContext pre burn "complete-pre"
      "complete-burn-post").assetConservation =
        [⟨"A", 10, 9, 10, 9, 0, 1⟩] := by
  unfold digest
  decide +kernel

example :
    (transferEffectPlan digest transferContext pre transfer
      "complete-pre" "complete-transfer-post").laneWrites =
        [⟨.assetTransfer, "complete-pre", "complete-transfer-post"⟩] := by
  unfold digest
  decide +kernel

example : EffectPlanAdmitted
    (transferEffectPlan digest transferContext pre transfer
      "complete-pre" "complete-transfer-post") :=
  transfer_accepted_plan_admitted transferRoots rowsRepresentable transferStructural
    transferSelected transferAccepted

example : EffectPlanAdmitted
    (managedEffectPlan digest issueContext pre issue
      "complete-pre" "complete-issue-post") :=
  managed_accepted_plan_admitted rowsRepresentable managedStructural issueCommand issueOwner
    issueSelected issueAccepted

example : EffectPlanAdmitted
    (managedEffectPlan digest burnContext pre burn "complete-pre" "complete-burn-post") :=
  managed_accepted_plan_admitted rowsRepresentable managedStructural burnCommand burnOwner
    burnSelected burnAccepted

end EffectControls
"""


def test_accepted_transfer_issue_and_burn_with_nonzero_custody(
    custody_effect_plan_lean: LeanSubject,
) -> None:
    checked = _consumer(custody_effect_plan_lean, "CustodyEffectPlanControls", CONTROLS)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""


def _raw_physical_atoms(state: dict[str, object], asset: str) -> int:
    transfer = state["transfer_state"]
    assert isinstance(transfer, dict)
    balances = transfer["balances"]
    custody = state["custody"]
    assert isinstance(balances, list)
    assert isinstance(custody, list)
    total = 0
    for row in (*balances, *custody):
        if isinstance(row, dict) and row.get("asset") == asset:
            amount = row["amount_atoms"]
            assert type(amount) is int
            total += amount
    return total


@pytest.mark.parametrize("case", GOLDEN_CASES, ids=lambda case: case["name"])
def test_ten_golden_outcomes_refine_actual_leaf_effects_by_exact_completion(case) -> None:
    """Check a finite leaf-to-custody relation, independently of the renderer."""

    assert hashlib.sha256(GOLDEN_FIXTURE.read_bytes()).hexdigest() == GOLDEN_FIXTURE_SHA256
    assert len(GOLDEN_CASES) == 10
    context = _decode_context(canonical_global_bytes_v2(case["context"]))
    pre = decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(case["pre_state"]))
    command_raw = canonical_global_bytes_v2(case["command"])
    command: AssetLaneCommandV2
    leaf: (
        AssetTransferAcceptedV2 | AssetTransferRejectedV2
        | ManagedAssetLifecycleAcceptedV2 | ManagedAssetLifecycleRejectedV2
    )
    if case["command_type"] == "TRANSFER":
        command = decode_asset_transfer_command_v2(command_raw)
        leaf = transition_asset_transfer_v2(context.transfer_context(), pre.transfer_state, command)
    else:
        command = decode_managed_asset_lifecycle_command_v2(command_raw)
        leaf = transition_managed_asset_lifecycle_v2(
            context.managed_context(), pre.managed_leaf_state(), command
        )
    completed = transition_asset_lane_custody_v2(context, pre, command)

    if case["output"]["status"] == "REJECTED":
        assert isinstance(leaf, (AssetTransferRejectedV2, ManagedAssetLifecycleRejectedV2))
        assert isinstance(completed, AssetLaneRejectedV2)
        assert completed.code is leaf.code
        assert completed.effects.is_empty
        assert completed.pre_state_root == completed.post_state_root == pre.state_root
        return

    assert isinstance(leaf, (AssetTransferAcceptedV2, ManagedAssetLifecycleAcceptedV2))
    assert isinstance(completed, AssetLaneCustodyAcceptedV2)
    raw_pre = case["pre_state"]
    raw_post = case["output"]["post_state"]
    expected_post = decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(raw_post))
    expected_effects = replace(
        leaf.effects,
        asset_conservation=tuple(
            replace(
                row,
                owned_and_custodied_pre_atoms=_raw_physical_atoms(raw_pre, row.asset),
                owned_and_custodied_post_atoms=_raw_physical_atoms(raw_post, row.asset),
            )
            for row in leaf.effects.asset_conservation
        ),
        lane_writes=(
            LaneWriteV2(LaneIdV2.ASSET_TRANSFER, pre.state_root, expected_post.state_root),
        ),
    )
    assert completed.post_state == expected_post
    assert completed.effects == expected_effects
    assert completed.effects.rows == leaf.effects.rows
    assert completed.effects.fee_conservation == leaf.effects.fee_conservation
    assert completed.effects.occurrence_consumptions == leaf.effects.occurrence_consumptions
    assert completed.effects.external_outbox_enqueue == leaf.effects.external_outbox_enqueue


def test_accounts_only_completion_mutant_is_refused(custody_effect_plan_lean: LeanSubject) -> None:
    source = SOURCE.read_text()
    replacements = {
        "ownedAndCustodiedPreAtoms := C.physicalFor pre row.asset":
            "ownedAndCustodiedPreAtoms := amountForAsset pre.transferState.balances row.asset",
        "ownedAndCustodiedPostAtoms := C.physicalFor post row.asset":
            "ownedAndCustodiedPostAtoms := amountForAsset post.transferState.balances row.asset",
    }
    for before, after in replacements.items():
        assert source.count(before) == 1
        source = source.replace(before, after)
    path = custody_effect_plan_lean.source / "AccountsOnlyCustodyEffectPlanMutant.lean"
    path.write_text(source)
    checked = _compile(custody_effect_plan_lean, path)
    assert checked.returncode == 1, checked.stdout + checked.stderr
    assert "error:" in checked.stdout
    assert "amountForAsset" in checked.stdout
    assert "unexpected token" not in checked.stdout
    assert "unknown identifier" not in checked.stdout.lower()


@pytest.mark.parametrize(
    ("name", "lane_writes"),
    (
        ("Passthrough", "source.laneWrites"),
        (
            "Duplicate",
            "[⟨.assetTransfer, completePreRoot, completePostRoot⟩, "
            "⟨.assetTransfer, completePreRoot, completePostRoot⟩]",
        ),
    ),
)
def test_lane_write_completion_mutants_are_refused(
    custody_effect_plan_lean: LeanSubject,
    name: str,
    lane_writes: str,
) -> None:
    source = SOURCE.read_text()
    original = "laneWrites := [⟨.assetTransfer, completePreRoot, completePostRoot⟩]"
    assert source.count(original) == 1
    path = custody_effect_plan_lean.source / f"{name}LaneWriteCustodyEffectPlanMutant.lean"
    path.write_text(source.replace(original, f"laneWrites := {lane_writes}"))
    checked = _compile(custody_effect_plan_lean, path)
    assert checked.returncode == 1, checked.stdout + checked.stderr
    assert "error:" in checked.stdout
    assert "unexpected token" not in checked.stdout
    assert "unknown identifier" not in checked.stdout.lower()
