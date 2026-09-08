"""Retained checks for the scoped finite managed-effect-plan construction.

The frozen Lean source is pinned and compiled on the existing finite-outcome
closure.  An independent concrete consumer evaluates an issue from zero supply
and its full burn, then compares the six observable plan fields with current
typed Python constructors.  This is bounded construction evidence.  It does
not establish root syntax, digest, codec, journal, authority, universal runtime
refinement, or production claims.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.asset_transfer_types_v2 import AssetClassV2
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import AssetSupplyV2, LaneIdV2, LaneWriteV2
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_result_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleRejectedV2,
)
from src.core.managed_asset_lifecycle_state_v2 import (
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleStateV2,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import lean as lean
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import outcome_lean as outcome_lean
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import shared_lean as shared_lean
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "AssetLaneFiniteEffectPlanV2"
NAMESPACE = f"Proofs.{MODULE}"
REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE = REPO_ROOT / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "24ac1efe7c06732d3c4d7dd37269d2b6afb64bb8d18a7b4893f9460b47b82fc3"

ROOT = "0x" + "1" * 64
ORIGIN = "0x" + "2" * 64
AUTHORITY = "0x" + "3" * 64
GLOBAL = "0x" + "4" * 64

OPEN_PREAMBLE = f"""open Proofs
open Proofs.ManagedAssetFiniteOutcomeV2
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1
open {NAMESPACE}
attribute [local instance] lexOrd
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
"""
PREAMBLE = f"import {NAMESPACE}\n{OPEN_PREAMBLE}"

THEOREM_NAMES = (
    "effect_key_of_wire_unique",
    "sorted_wire_unique",
    "sorted_rows_strict",
    "covered_quantities_u128",
    "managed_raw_unique",
    "managed_rejected_empty",
    "managed_amount_positive",
    "managed_rows_admitted",
    "managed_conservation_admitted",
    "managed_projection",
    "managed_fee_projection",
    "managed_keys_ordered",
    "managed_items",
    "managed_plan_admitted",
    "managed_asset_token",
    "managed_plan_tokens",
    "managed_accepted_fields",
)

# These are the theorem contracts that describe the resulting plan.  The
# declaration inventory and axiom probe below still cover the full source
# surface without turning every internal helper into a retained contract.
MEANINGFUL_TYPES = {
    "managed_rejected_empty": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
      {command : M.Command} {code : ManagedAssetFiniteOutcomeV2.RejectCode},
      (FM.transition digest ctx pre command).verdict = .rejected code →
        managedPlan digest ctx pre command = EffectPlan.empty""",
    "managed_plan_admitted": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
      {command : M.Command}, FM.Structural pre → M.CommandWellFormed command →
        B.ValidToken command.accountOwner →
        (FM.transition digest ctx pre command).verdict = .accepted →
          EffectPlanAdmitted (managedPlan digest ctx pre command)""",
    "managed_keys_ordered": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
      {command : M.Command}, (FM.transition digest ctx pre command).verdict = .accepted →
        PlanKeysUnique (managedPlan digest ctx pre command) ∧
          PlanOrdered (managedPlan digest ctx pre command)""",
    "managed_items": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
      {command : M.Command}, (FM.transition digest ctx pre command).verdict = .accepted →
        (managedPlan digest ctx pre command).rows.length = 2 ∧
          PlanWithinItemBounds (managedPlan digest ctx pre command)""",
    "managed_plan_tokens": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
      {command : M.Command}, FM.Structural pre → B.ValidToken command.accountOwner →
        (FM.transition digest ctx pre command).verdict = .accepted →
          PlanTokens (managedPlan digest ctx pre command)""",
    "managed_accepted_fields": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
      {command : M.Command}, FM.Structural pre →
        (FM.transition digest ctx pre command).verdict = .accepted →
          ∃ occurrence, ctx.occurrence = some occurrence ∧
            managedPlan digest ctx pre command =
              ⟨C.sortOn effectWire (managedRawRows command),
                [managedConservation pre (FM.transition digest ctx pre command).post command], [],
                [⟨.assetTransfer, FM.stateRoot digest pre,
                  FM.stateRoot digest (FM.transition digest ctx pre command).post⟩],
                [occurrence.occurrenceId], []⟩""",
}


@pytest.fixture(scope="module")
def effect_plan_lean(request: pytest.FixtureRequest) -> LeanSubject:
    """Compile the frozen plan source as the next module in the finite closure."""

    subject: LeanSubject = request.getfixturevalue("outcome_lean")
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
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


def _raw_consumer(subject: LeanSubject, name: str, source: str) -> subprocess.CompletedProcess[str]:
    path = subject.source / f"{name}.lean"
    path.write_text(source)
    return _compile(subject, path)


def _axiom_names(output: str) -> set[str]:
    return {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }


def test_frozen_effect_plan_surface_and_standard_axioms(effect_plan_lean: LeanSubject) -> None:
    source_code = SOURCE.read_text()
    assert hashlib.sha256(source_code.encode()).hexdigest() == SOURCE_SHA256
    declared = tuple(re.findall(r"^theorem\s+(\w+)", source_code, flags=re.MULTILINE))
    assert declared == THEOREM_NAMES
    assert len(declared) == len(set(declared)) == 17
    executable = re.sub(r"/-.*?-/", "", source_code, flags=re.DOTALL)
    assert (
        re.search(
            r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b",
            executable,
        )
        is None
    )
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in MEANINGFUL_TYPES.items()
    )
    body += "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in THEOREM_NAMES)
    result = _consumer(effect_plan_lean, "AssetLaneFiniteEffectPlanContracts", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    reports = result.stdout.count("depends on axioms") + result.stdout.count(
        "does not depend on any axioms"
    )
    assert reports == len(MEANINGFUL_TYPES) + len(THEOREM_NAMES)
    assert _axiom_names(result.stdout) <= {"propext", "Quot.sound", "Classical.choice"}


EFFECT_PLAN_CONSUMER = r"""
import Proofs.AssetLaneFiniteEffectPlanV2

set_option warningAsError true
set_option maxRecDepth 100000

open Proofs.ManagedAssetFiniteOutcomeV2

namespace IndependentEffectPlanConsumer

local instance token_decidable (s : String) : Decidable (B.ValidToken s) := by
  unfold B.ValidToken
  infer_instance
local instance unique_decidable (rows : List Proofs.GlobalEconomicStateRefinementV2.AmountRow) :
    Decidable (S.Unique rows) := by
  unfold S.Unique
  infer_instance
local instance supply_unique_decidable (rows : List Proofs.RegisteredSupplySupportV1.V1SupplyRow) :
    Decidable (Proofs.RegisteredSupplySupportV1.SourceAssetKeysUnique rows) := by
  unfold Proofs.RegisteredSupplySupportV1.SourceAssetKeysUnique
  infer_instance
local instance width_decidable (n : Int) : Decidable (Proofs.GlobalSettlementCoreV2.FitsU128 n) := by
  unfold Proofs.GlobalSettlementCoreV2.FitsU128
  infer_instance

def p : M.Policy := ⟨"A", .registeredOrdinaryToken, some "origin", 8,
  some ⟨"issuer", "auth"⟩, some "auth", true⟩
def base : State := ⟨"release", [p], [], [⟨"A", 0⟩]⟩
def issue : M.Command := ⟨"managed_asset_issue", "body", "A", .registeredOrdinaryToken,
  some "origin", 8, some "auth", "alice", 1⟩
def ctx : M.Context := ⟨"release", "global", some ⟨"global", [], "managed_asset_issue",
  "body", "issuer", "auth", "occurrence"⟩⟩
def missing : M.Context := { ctx with occurrence := none }
def constantDigest (_ : B.Bytes) : M.Root := "constant"

theorem base_structural : Structural base := by
  constructor
  · decide
  · simp [base]
  · intro policy member
    have same : policy = p := by simpa only [base, List.mem_singleton] using member
    subst policy
    exact ⟨rfl, by intro absent; exact False.elim (absent rfl)⟩
  · decide
  · intro row member; simp [base] at member
  · simp [base]
  · intro row member; simp [base] at member
  · decide
  · simp [base, Proofs.RegisteredSupplyUpdateV1.SourceAssetKeysOrdered]
  · intro row member
    have same : row = ⟨"A", 0⟩ := by simpa only [base, List.mem_singleton] using member
    subst row
    decide
  · rfl
  · intro asset
    simp [base, Proofs.GlobalEconomicStateRefinementV2.amountForAsset,
      Proofs.RegisteredSupplySupportV1.numericRows, Proofs.RegisteredSupplySupportV1.nonzeroRow,
      Proofs.GlobalEconomicStateRefinementV2.supplyFor]
  · intro row member; simp [base] at member
  · intro row member
    have same : row = ⟨"A", 0⟩ := by simpa only [base, List.mem_singleton] using member
    subst row
    decide

namespace P
export Proofs.AssetLaneFiniteEffectPlanV2 (managedPlan managedRawRows managed_plan_admitted
  managed_plan_tokens managed_keys_ordered managed_rejected_empty managed_items)
end P

theorem issue_command_admitted : M.CommandWellFormed issue := ⟨by decide, rfl⟩
theorem issue_accepts : (transition constantDigest ctx base issue).verdict = .accepted := by decide +kernel

def issuePlan := P.managedPlan constantDigest ctx base issue

theorem issue_numeric_plan_admitted : Proofs.GlobalSettlementCoreV2.EffectPlanAdmitted issuePlan :=
  P.managed_plan_admitted base_structural issue_command_admitted (by decide) issue_accepts

theorem issue_tokens_and_order : Proofs.AssetLaneFiniteEffectPlanV2.PlanTokens issuePlan ∧
    Proofs.AssetLaneFiniteEffectPlanV2.PlanOrdered issuePlan :=
  ⟨P.managed_plan_tokens base_structural (by decide) issue_accepts,
   (P.managed_keys_ordered issue_accepts).2⟩

def issued : State := (transition constantDigest ctx base issue).post

theorem issued_structural : Structural issued := by
  change Structural (transition constantDigest ctx base issue).post
  rw [(accepted_post_effects issue_accepts).1]
  exact economic_candidate_structural base_structural issue_command_admitted (by decide)
    ((accepted_iff constantDigest ctx base issue).mp issue_accepts).1

def burn : M.Command := {issue with commandKind := "managed_asset_burn"}
def burnCtx : M.Context := ⟨"release", "global", some ⟨"global", [], "managed_asset_burn",
  "body", "alice", "auth", "burn-occurrence"⟩⟩
theorem burn_command_admitted : M.CommandWellFormed burn := ⟨by decide, rfl⟩
theorem burn_accepts : (transition constantDigest burnCtx issued burn).verdict = .accepted := by decide +kernel

def burnPlan := P.managedPlan constantDigest burnCtx issued burn

theorem burn_numeric_plan_admitted : Proofs.GlobalSettlementCoreV2.EffectPlanAdmitted burnPlan :=
  P.managed_plan_admitted issued_structural burn_command_admitted (by decide) burn_accepts

theorem burn_tokens_and_order : Proofs.AssetLaneFiniteEffectPlanV2.PlanTokens burnPlan ∧
    Proofs.AssetLaneFiniteEffectPlanV2.PlanOrdered burnPlan :=
  ⟨P.managed_plan_tokens issued_structural (by decide) burn_accepts,
   (P.managed_keys_ordered burn_accepts).2⟩

theorem rejected_plan_has_six_empty_fields : P.managedPlan constantDigest missing base issue =
    Proofs.GlobalSettlementCoreV2.EffectPlan.empty :=
  P.managed_rejected_empty (code := .economic .missingOccurrence) (by decide)

theorem issue_and_burn_have_two_effect_rows : issuePlan.rows.length = 2 ∧ burnPlan.rows.length = 2 :=
  ⟨(P.managed_items issue_accepts).1, (P.managed_items burn_accepts).1⟩

end IndependentEffectPlanConsumer
"""


@pytest.fixture(scope="module")
def effect_plan_consumer_lean(effect_plan_lean: LeanSubject) -> LeanSubject:
    path = effect_plan_lean.source / "AssetLaneFiniteEffectPlanConsumerV2.lean"
    path.write_text(EFFECT_PLAN_CONSUMER)
    result = _compile(
        effect_plan_lean,
        path,
        effect_plan_lean.library / "AssetLaneFiniteEffectPlanConsumerV2.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return effect_plan_lean


def test_independent_issue_full_burn_admission_order_tokens_and_empty_rejection(
    effect_plan_consumer_lean: LeanSubject,
) -> None:
    assert (
        effect_plan_consumer_lean.library / "AssetLaneFiniteEffectPlanConsumerV2.olean"
    ).is_file()


OBSERVATIONS = r"""
import AssetLaneFiniteEffectPlanConsumerV2
import Lean.Data.Json

open IndependentEffectPlanConsumer Proofs.GlobalSettlementCoreV2

namespace EffectPlanObservations

def observation (name : String) (plan : EffectPlan) (occurrence : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", Lean.toJson name),
    ("rows", Lean.Json.arr ((plan.rows.map (fun row => Lean.Json.arr #[
      Lean.toJson row.kind.code, Lean.toJson row.principal, Lean.toJson row.asset,
      Lean.toJson row.custodyDomain, Lean.toJson row.deltaAtoms])).toArray)),
    ("conservation", Lean.Json.arr ((plan.assetConservation.map (fun row => Lean.Json.arr #[
      Lean.toJson row.asset, Lean.toJson row.ownedAndCustodiedPreAtoms,
      Lean.toJson row.ownedAndCustodiedPostAtoms, Lean.toJson row.supplyPreAtoms,
      Lean.toJson row.supplyPostAtoms, Lean.toJson row.authorizedIssueAtoms,
      Lean.toJson row.authorizedBurnAtoms])).toArray)),
    ("counts", Lean.toJson [plan.rows.length, plan.assetConservation.length,
      plan.feeConservation.length, plan.laneWrites.length, plan.occurrenceConsumptions.length,
      plan.externalOutboxEnqueue.length]),
    ("lane_ids", Lean.toJson (plan.laneWrites.map (fun write => write.laneId.code))),
    ("roots_bound", Lean.toJson (plan.laneWrites.all (fun write =>
      write.preRoot == "constant" && write.postRoot == "constant"))),
    ("occurrence_bound", Lean.toJson (plan.occurrenceConsumptions == [occurrence]))]

#eval IO.println ((observation "issue" issuePlan "occurrence").compress)
#eval IO.println ((observation "burn" burnPlan "burn-occurrence").compress)

end EffectPlanObservations
"""


def _managed_context(command: ManagedAssetLifecycleCommandV2) -> ManagedAssetLifecycleContextV2:
    subject = "issuer" if command.command_kind == "managed_asset_issue" else command.account_owner
    occurrence = EconomicCommandOccurrenceV2(
        "review",
        ROOT,
        1,
        0,
        0,
        command.command_kind,
        command.command_body_hash,
        ROOT,
        subject,
        AUTHORITY,
        1,
        ROOT,
        GLOBAL,
        (),
    )
    return ManagedAssetLifecycleContextV2(1, ROOT, GLOBAL, occurrence)


def _runtime_observation(
    name: str,
    context: ManagedAssetLifecycleContextV2,
    pre_state: ManagedAssetLifecycleStateV2,
    command: ManagedAssetLifecycleCommandV2,
) -> tuple[ManagedAssetLifecycleStateV2, dict[str, object]]:
    result = transition_managed_asset_lifecycle_v2(context, pre_state, command)
    assert isinstance(result, ManagedAssetLifecycleAcceptedV2), name
    plan = result.effects
    plan.validate()
    occurrence = context.occurrence
    assert occurrence is not None
    return result.post_state, {
        "name": name,
        "rows": [
            [row.kind.value, row.principal, row.asset, row.custody_domain, row.delta_atoms]
            for row in plan.rows
        ],
        "conservation": [
            [
                row.asset,
                row.owned_and_custodied_pre_atoms,
                row.owned_and_custodied_post_atoms,
                row.supply_pre_atoms,
                row.supply_post_atoms,
                row.authorized_issue_atoms,
                row.authorized_burn_atoms,
            ]
            for row in plan.asset_conservation
        ],
        "counts": [
            len(plan.rows),
            len(plan.asset_conservation),
            len(plan.fee_conservation),
            len(plan.lane_writes),
            len(plan.occurrence_consumptions),
            len(plan.external_outbox_enqueue),
        ],
        "lane_ids": [write.lane_id.value for write in plan.lane_writes],
        "roots_bound": all(
            write.pre_root == pre_state.state_root
            and write.post_root == result.post_state.state_root
            for write in plan.lane_writes
        ),
        "occurrence_bound": plan.occurrence_consumptions == (occurrence.occurrence_id,),
    }


def _runtime_effect_plan_observations() -> list[dict[str, object]]:
    policy = ManagedAssetLifecyclePolicyV2(
        "A",
        AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        ORIGIN,
        8,
        "issuer",
        AUTHORITY,
        AUTHORITY,
        True,
    )
    pre_state = ManagedAssetLifecycleStateV2(ROOT, (policy,), (), (AssetSupplyV2("A", 0),))
    issue = ManagedAssetLifecycleCommandV2(
        "managed_asset_issue",
        "A",
        AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        ORIGIN,
        8,
        AUTHORITY,
        "alice",
        1,
    )
    issued_state, issued = _runtime_observation("issue", _managed_context(issue), pre_state, issue)
    burn = replace(issue, command_kind="managed_asset_burn")
    _, burned = _runtime_observation("burn", _managed_context(burn), issued_state, burn)

    rejected = transition_managed_asset_lifecycle_v2(
        ManagedAssetLifecycleContextV2(1, ROOT, GLOBAL, None), pre_state, issue
    )
    assert isinstance(rejected, ManagedAssetLifecycleRejectedV2)
    assert rejected.pre_state_root == rejected.post_state_root == pre_state.state_root
    assert rejected.effects.is_empty
    return [issued, burned]


def test_python_constructor_matches_bounded_lean_six_field_observations_and_root_nonclaim(
    effect_plan_consumer_lean: LeanSubject,
) -> None:
    expected = _runtime_effect_plan_observations()
    result = _raw_consumer(
        effect_plan_consumer_lean, "AssetLaneFiniteEffectPlanObservationsV2", OBSERVATIONS
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    observed = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
    assert observed == expected
    assert all(record["roots_bound"] and record["occurrence_bound"] for record in observed)

    # The Lean consumer deliberately uses a constant digest.  Its numeric plan
    # proof does not validate canonical root strings; the runtime constructor does.
    with pytest.raises(ValueError):
        LaneWriteV2(LaneIdV2.ASSET_TRANSFER, "constant", "constant")


def _semantic_false_control(subject: LeanSubject, name: str, body: str, fragment: str) -> None:
    result = _raw_consumer(
        subject,
        name,
        "import AssetLaneFiniteEffectPlanConsumerV2\n"
        "open IndependentEffectPlanConsumer\n"
        "set_option warningAsError true\n" + body,
    )
    output = result.stdout + result.stderr
    assert result.returncode == 1, output
    assert result.stderr == ""
    assert result.stdout.count("error:") == 1, output
    assert fragment in output, output
    assert "Tactic `decide` proved that the proposition" in output
    assert "is false" in output
    assert "unknown module" not in output
    assert "unknown identifier" not in output
    assert "failed to synthesize" not in output


def test_reversed_burn_and_missing_supply_row_are_semantic_false_controls(
    effect_plan_consumer_lean: LeanSubject,
) -> None:
    _semantic_false_control(
        effect_plan_consumer_lean,
        "AssetLaneFiniteEffectPlanFalseBurnSign",
        "example : (P.managedRawRows burn).map (fun row => row.deltaAtoms) = [1, 1] := by decide\n",
        "managedRawRows burn",
    )
    _semantic_false_control(
        effect_plan_consumer_lean,
        "AssetLaneFiniteEffectPlanFalseMissingSupplyRow",
        "example : issuePlan.rows.length = 1 := by\n"
        "  rw [issue_and_burn_have_two_effect_rows.1]\n"
        "  decide\n",
        "2 = 1",
    )
