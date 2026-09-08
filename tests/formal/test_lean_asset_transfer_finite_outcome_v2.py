"""Retained finite consumers for the frozen V2 transfer-outcome proof.

The source hash, theorem inventory, bounded Lean consumers, and typed runtime
vectors are deliberately kept separate.  They establish the scoped finite
model and its agreement with these constructed observations.  They do not
establish runtime constructor, digest, serializer, global replay, or production
authority claims.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import dataclass, replace
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
    AssetTransferRejectedV2,
    AssetTransferStateV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
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

MODULE = "AssetTransferFiniteOutcomeV2"
NAMESPACE = f"Proofs.{MODULE}"
REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE = REPO_ROOT / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "97eaaa3f7e7ec8859d6a28b7fc6de49586f8d7ce983f70908144dd92beb1f09c"

ROOT = "0x" + "1" * 64
ORIGIN = "0x" + "2" * 64
AUTHORITY = "0x" + "3" * 64
GLOBAL = "0x" + "4" * 64
OTHER = "0x" + "5" * 64
U128 = 2**128 - 1
I128 = 2**127 - 1
STATE_BYTE_CAP = 1_048_576

OPEN_PREAMBLE = f"""open Proofs
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
    "all_reject_codes_length",
    "all_reject_codes_complete",
    "all_reject_codes_wire_order",
    "all_reject_codes_wire_unique",
    "accepted_iff",
    "resource_reject_iff",
    "economic_reject_precedes_resource",
    "rejected_noop",
    "accepted_post_effects",
    "context_is_scalar_first_five",
    "firstFailing_append",
    "scalar_preserves_context_failure",
    "economic_matches_selected",
    "economic_none_iff_selected",
    "context_precedes_policy_absence",
    "absent_policy_after_context",
    "policyFor_spec",
    "structural_registered",
    "project_well_formed",
    "update_roles_supported",
    "update_roles_tokens",
    "update_roles_ordered",
    "ordered_roles_tokens",
    "economic_candidate_structural",
    "candidate_immutable",
    "accepted_preserves_admission",
    "accepted_selected_leaf",
    "accepted_accounting",
    "accepted_lookup",
    "selected_scan_precedes_resources",
    "accepted_iff_full_guards_resources",
    "resource_reject_iff_full_guards_resources",
    "insertPrincipal_length",
    "sortPrincipals_length",
    "ordered_roles_length_le_three",
    "movementRows_length_le",
    "movementRows_width",
    "accepted_payload_bounds",
    "accepted_effects_bind",
    "transition_preserves_admission",
    "trace_preserves_admission",
    "trace_prefixes_admitted",
)

# These type ascriptions pin the public contracts that decide finite outcome,
# reject precedence, admission, accounting, capacity, payload bounds, and trace
# preservation.  The inventory below independently watches every theorem.
MEANINGFUL_TYPES = {
    "all_reject_codes_length": "allRejectCodes.length = 18",
    "accepted_iff": """∀ (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State)
      (command : T.Command),
      (transition digest ctx pre command).verdict = .accepted ↔
        economicRejectCode ctx pre command = none ∧ Resources (candidate pre command)""",
    "resource_reject_iff": """∀ (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State)
      (command : T.Command),
      (transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
        economicRejectCode ctx pre command = none ∧ ¬ Resources (candidate pre command)""",
    "economic_reject_precedes_resource": """∀ (digest : B.Bytes → T.Root) (ctx : T.Context)
      (pre : State) (command : T.Command) (code : T.RejectCode),
      economicRejectCode ctx pre command = some code →
        transition digest ctx pre command = reject (.economic code) pre""",
    "rejected_noop": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State}
      {command : T.Command} {code : Proofs.AssetTransferFiniteOutcomeV2.RejectCode},
      (transition digest ctx pre command).verdict = .rejected code →
        (transition digest ctx pre command).post = pre ∧
        stateRoot digest (transition digest ctx pre command).post = stateRoot digest pre ∧
        (transition digest ctx pre command).effects =
          Proofs.AssetTransferRefinementV2.EffectEnvelope.empty""",
    "accepted_post_effects": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State}
      {command : T.Command},
      (transition digest ctx pre command).verdict = .accepted →
        (transition digest ctx pre command).post = candidate pre command ∧
        (transition digest ctx pre command).effects = acceptedEffects digest ctx pre command""",
    "economic_none_iff_selected": """∀ (ctx : T.Context) (pre : State) (command : T.Command),
      economicRejectCode ctx pre command = none ↔
        ∃ policy, policyFor pre command.asset = some policy ∧
          T.rejectCode ctx (project pre policy) command = none""",
    "project_well_formed": """∀ {pre : State} {policy : T.Policy}, Structural pre →
      policy ∈ pre.policies → T.StateWellFormed (project pre policy)""",
    "accepted_preserves_admission": """∀ {rootSyntax : String → Prop}
      {namespaceSyntax : String → T.AssetClass → Prop} {digest : B.Bytes → T.Root}
      {ctx : T.Context} {pre : State} {command : T.Command},
      Admitted rootSyntax namespaceSyntax pre → CommandAdmission command →
      (transition digest ctx pre command).verdict = .accepted →
        Admitted rootSyntax namespaceSyntax (transition digest ctx pre command).post""",
    "accepted_accounting": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State}
      {command : T.Command}, S.Unique pre.balances →
      (transition digest ctx pre command).verdict = .accepted → (asset : Asset) →
        amountForAsset (transition digest ctx pre command).post.balances asset =
          amountForAsset pre.balances asset ∧
        (transition digest ctx pre command).post.supplies = pre.supplies""",
    "accepted_iff_full_guards_resources": """∀ (digest : B.Bytes → T.Root) (ctx : T.Context)
      (pre : State) (command : T.Command),
      (transition digest ctx pre command).verdict = .accepted ↔
        ∃ policy, policyFor pre command.asset = some policy ∧
          (∀ reason ∈ T.preBalanceRejectCodes,
            T.guardPasses ctx (project pre policy) command reason) ∧
          T.balanceCodeOn (project pre policy) command
            (T.orderedRoles (project pre policy) command) = none ∧
          Resources (candidateFor pre policy command)""",
    "resource_reject_iff_full_guards_resources": """∀ (digest : B.Bytes → T.Root)
      (ctx : T.Context) (pre : State) (command : T.Command),
      (transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
        ∃ policy, policyFor pre command.asset = some policy ∧
          (∀ reason ∈ T.preBalanceRejectCodes,
            T.guardPasses ctx (project pre policy) command reason) ∧
          T.balanceCodeOn (project pre policy) command
            (T.orderedRoles (project pre policy) command) = none ∧
          ¬ Resources (candidateFor pre policy command)""",
    "accepted_payload_bounds": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context}
      {pre : State} {command : T.Command} {policy : T.Policy},
      policyFor pre command.asset = some policy →
      (transition digest ctx pre command).verdict = .accepted →
        (payloadFor pre policy command).movements.length ≤ 3 ∧
        (payloadFor pre policy command).feeAllocations.length ≤ 1 ∧
        (∀ row ∈ (payloadFor pre policy command).movements,
          T.IsI128 row.deltaAtoms ∧ row.deltaAtoms ≠ 0) ∧
        T.IsI128 policy.transferFeeAtoms""",
    "accepted_effects_bind": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context}
      {pre : State} {command : T.Command},
      (transition digest ctx pre command).verdict = .accepted →
        ∃ policy occurrence, policyFor pre command.asset = some policy ∧
          ctx.occurrence = some occurrence ∧
          (transition digest ctx pre command).effects.payload =
            some (payloadFor pre policy command) ∧
          (transition digest ctx pre command).effects.laneWrites =
            [⟨stateRoot digest pre,
              stateRoot digest (transition digest ctx pre command).post⟩] ∧
          (transition digest ctx pre command).effects.occurrenceConsumptions =
            [occurrence.occurrenceId] ∧
          (transition digest ctx pre command).effects.externalOutbox = [] ∧
          (transition digest ctx pre command).effects.externalRoots =
            AssetTransferRefinementV2.ExternalRoots.zero""",
    "trace_prefixes_admitted": """∀ {rootSyntax : String → Prop}
      {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → T.Root)
      (pre : State) (trace : List (T.Context × T.Command)),
      Admitted rootSyntax namespaceSyntax pre →
      (∀ input ∈ trace, CommandAdmission input.2) → (length : Nat) →
        Admitted rootSyntax namespaceSyntax (executeTrace digest pre (trace.take length))""",
}

EXPECTED_REJECT_CODES = [
    "MISSING_OCCURRENCE",
    "OCCURRENCE_BINDING_MISMATCH",
    "RELEASE_MISMATCH",
    "UNKNOWN_COMMAND",
    "OCCURRENCE_COMMAND_MISMATCH",
    "UNKNOWN_ASSET",
    "DISABLED_ASSET",
    "UNREGISTERED_ASSET",
    "ASSET_ORIGIN_MISMATCH",
    "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
    "UNAUTHORIZED_SUBJECT",
    "SELF_TRANSFER",
    "ZERO_AMOUNT",
    "FEE_LIMIT_EXCEEDED",
    "EFFECT_DELTA_OVERFLOW",
    "INSUFFICIENT_BALANCE",
    "BALANCE_OVERFLOW",
    "STATE_RESOURCE_LIMIT",
]


@pytest.fixture(scope="module")
def transfer_outcome_lean(request: pytest.FixtureRequest) -> LeanSubject:
    """Compile the frozen transfer proof as dependency 26 of the Std-only closure."""

    outcome_subject: LeanSubject = request.getfixturevalue("outcome_lean")
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    captured = outcome_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes(source)
    result = _compile(
        outcome_subject,
        captured,
        outcome_subject.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return outcome_subject


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


def test_frozen_theorem_surface_and_standard_axioms(
    transfer_outcome_lean: LeanSubject,
) -> None:
    source_code = SOURCE.read_text()
    assert hashlib.sha256(source_code.encode()).hexdigest() == SOURCE_SHA256
    declared = tuple(re.findall(r"^theorem\s+(\w+)", source_code, flags=re.MULTILINE))
    assert declared == THEOREM_NAMES
    assert len(declared) == len(set(declared)) == 42
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
    result = _consumer(transfer_outcome_lean, "TransferFiniteOutcomeContracts", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    axiom_reports = result.stdout.count("depends on axioms") + result.stdout.count(
        "does not depend on any axioms"
    )
    assert axiom_reports == len(MEANINGFUL_TYPES) + len(THEOREM_NAMES)
    assert _axiom_names(result.stdout) <= {"propext", "Quot.sound", "Classical.choice"}


FINITE_CONSUMER = r"""
import Proofs.AssetTransferFiniteOutcomeV2

set_option warningAsError true
set_option maxRecDepth 100000

open Proofs.AssetTransferFiniteOutcomeV2
open Proofs.GlobalEconomicStateRefinementV2 Proofs.RegisteredSupplySupportV1

namespace IndependentTransferConsumer

local instance token_decidable (s : String) : Decidable (B.ValidToken s) := by
  unfold B.ValidToken
  infer_instance
local instance unique_decidable (rows : List AmountRow) : Decidable (S.Unique rows) := by
  unfold S.Unique
  infer_instance
local instance supply_unique_decidable (rows : List V1SupplyRow) :
    Decidable (SourceAssetKeysUnique rows) := by
  unfold SourceAssetKeysUnique
  infer_instance
local instance width_decidable (n : Int) : Decidable (Proofs.GlobalSettlementCoreV2.FitsU128 n) := by
  unfold Proofs.GlobalSettlementCoreV2.FitsU128
  infer_instance

def p : T.Policy := ⟨"A", "collector", 0, true, .registeredOrdinaryToken, some "origin", 8⟩
def base : State := ⟨"release", [p], [⟨"sender", "A", "accounts", 5⟩], [⟨"A", 10⟩]⟩
def move : T.Command := ⟨"asset_transfer", "body", "A", "sender", "recipient", 5, 0, some "origin"⟩
def ctx : T.Context := ⟨"release", "global", some ⟨"global", [], "asset_transfer",
  "body", "sender", "grant", "occurrence"⟩⟩
def missing : T.Context := { ctx with occurrence := none }
def constantDigest (_ : B.Bytes) : T.Root := "constant"

theorem base_structural : Structural base := by
  constructor
  · decide
  · simp [base]
  · intro policy member
    have same : policy = p := by simpa only [base, List.mem_singleton] using member
    subst policy
    decide
  · intro policy member
    have same : policy = p := by simpa only [base, List.mem_singleton] using member
    subst policy
    rfl
  · intro policy member
    have same : policy = p := by simpa only [base, List.mem_singleton] using member
    subst policy
    decide
  · decide
  · intro row member
    have same : row = ⟨"sender", "A", "accounts", 5⟩ := by simpa only [base, List.mem_singleton] using member
    subst row
    exact ⟨rfl, by decide, by decide⟩
  · simp [base]
  · intro row member
    have same : row = ⟨"sender", "A", "accounts", 5⟩ := by simpa only [base, List.mem_singleton] using member
    subst row
    decide
  · decide
  · simp [base, Proofs.RegisteredSupplyUpdateV1.SourceAssetKeysOrdered]
  · intro row member
    have same : row = ⟨"A", 10⟩ := by simpa only [base, List.mem_singleton] using member
    subst row
    decide
  · rfl
  · intro asset
    by_cases selected : "A" = asset
    · subst asset
      decide
    · simp [base, amountForAsset, supplyFor, numericRows, nonzeroRow, toNumericRow, selected]
  · intro row member
    have same : row = ⟨"sender", "A", "accounts", 5⟩ := by simpa only [base, List.mem_singleton] using member
    subst row
    exact ⟨by decide, by decide⟩
  · intro row member
    have same : row = ⟨"A", 10⟩ := by simpa only [base, List.mem_singleton] using member
    subst row
    decide

theorem initial_admitted : Admitted (fun _ => True) (fun _ _ => True) base := by
  refine ⟨base_structural, ?_, ?_⟩
  · refine ⟨by decide, True.intro, ?_⟩
    intro policy member
    have same : policy = p := by simpa only [base, List.mem_singleton] using member
    subst policy
    refine ⟨by decide, True.intro, ?_⟩
    intro value selected
    have same : value = "origin" := by simpa only [p, Option.some.injEq] using selected.symm
    subst value
    exact ⟨by decide, True.intro⟩
  · decide

theorem cover_is_strict : amountForAsset base.balances "A" < supplyFor (numericRows base.supplies) "A" := by
  decide

theorem command_admitted : CommandAdmission move := ⟨⟨by decide, by decide⟩, by decide, by decide⟩

theorem accepted_nonvacuous : (transition constantDigest ctx base move).verdict = .accepted := by decide +kernel

theorem rejected_nonvacuous : (transition constantDigest missing base move).verdict =
    .rejected (.economic .missingOccurrence) := by decide

theorem rejection_is_exact_noop : (transition constantDigest missing base move).post = base ∧
    (transition constantDigest missing base move).effects = Proofs.AssetTransferRefinementV2.EffectEnvelope.empty :=
  ⟨(rejected_noop rejected_nonvacuous).1, (rejected_noop rejected_nonvacuous).2.2⟩

theorem derived_post_admission : Admitted (fun _ => True) (fun _ _ => True)
    (transition constantDigest ctx base move).post :=
  accepted_preserves_admission initial_admitted command_admitted accepted_nonvacuous

theorem all_asset_accounting (asset : String) :
    amountForAsset (transition constantDigest ctx base move).post.balances asset = amountForAsset base.balances asset ∧
    (transition constantDigest ctx base move).post.supplies = base.supplies :=
  accepted_accounting base_structural.balanceUnique accepted_nonvacuous asset

theorem changed_state_can_share_digest : (transition constantDigest ctx base move).post ≠ base ∧
    stateRoot constantDigest (transition constantDigest ctx base move).post = stateRoot constantDigest base :=
  ⟨by decide +kernel, rfl⟩

theorem missing_supply_is_not_recreated :
    (candidate { base with supplies := [] } move).supplies = [] := (candidate_immutable _ _).2.2

def mixed : List (T.Context × T.Command) := [(ctx, move), (missing, move), (ctx, move)]

theorem mixed_admission : Admitted (fun _ => True) (fun _ _ => True)
    (executeTrace constantDigest base mixed) := by
  apply trace_preserves_admission constantDigest base mixed initial_admitted
  intro input member
  have same : input.2 = move := by
    simp only [mixed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same <;> subst input <;> rfl
  rw [same]
  exact command_admitted

theorem mixed_full_move_then_noop_supply_identity :
    (executeTrace constantDigest base mixed).balances =
      [⟨"recipient", "A", "accounts", 5⟩] ∧
    (executeTrace constantDigest base mixed).supplies = [⟨"A", 10⟩] := by decide +kernel

theorem repeated_move_observes_computed_balance :
    (transition constantDigest ctx (transition constantDigest ctx base move).post move).verdict =
      .rejected (.economic .insufficientBalance) := by decide +kernel

theorem every_mixed_prefix_admitted (length : Nat) : Admitted (fun _ => True) (fun _ _ => True)
    (executeTrace constantDigest base (mixed.take length)) := by
  apply trace_prefixes_admitted constantDigest base mixed initial_admitted
  intro input member
  have same : input.2 = move := by
    simp only [mixed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same <;> subst input <;> rfl
  rw [same]
  exact command_admitted

example (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State) (command : T.Command) :
    (transition digest ctx pre command).verdict = .accepted ↔
      ∃ policy, policyFor pre command.asset = some policy ∧
        (∀ reason ∈ T.preBalanceRejectCodes, T.guardPasses ctx (project pre policy) command reason) ∧
        T.balanceCodeOn (project pre policy) command (T.orderedRoles (project pre policy) command) = none ∧
        Resources (candidateFor pre policy command) :=
  accepted_iff_full_guards_resources digest ctx pre command

end IndependentTransferConsumer
"""


@pytest.fixture(scope="module")
def transfer_consumer_lean(transfer_outcome_lean: LeanSubject) -> LeanSubject:
    path = transfer_outcome_lean.source / "TransferFiniteOutcomeConsumer.lean"
    path.write_text(FINITE_CONSUMER)
    result = _compile(
        transfer_outcome_lean,
        path,
        transfer_outcome_lean.library / "TransferFiniteOutcomeConsumer.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return transfer_outcome_lean


def test_independent_strict_cover_admission_trace_and_noop(
    transfer_consumer_lean: LeanSubject,
) -> None:
    assert (transfer_consumer_lean.library / "TransferFiniteOutcomeConsumer.olean").is_file()


def _semantic_false_control(subject: LeanSubject, name: str, proposition: str) -> None:
    path = subject.source / f"{name}.lean"
    path.write_text(
        "import TransferFiniteOutcomeConsumer\n"
        + OPEN_PREAMBLE
        + "open IndependentTransferConsumer\n"
        + f"example : {proposition} := by decide\n"
    )
    result = _compile(subject, path)
    output = result.stdout + result.stderr
    assert result.returncode != 0
    assert result.stderr == ""
    assert result.stdout.count("error:") == 1, output
    assert "Tactic `decide` proved that the proposition" in output
    assert "is false" in output
    assert "unknown module" not in output
    assert "unexpected token" not in output
    assert "unexpected identifier" not in output
    assert "failed to synthesize" not in output


def test_false_finite_outcome_laws_fail_for_the_intended_proposition(
    transfer_consumer_lean: LeanSubject,
) -> None:
    controls = (
        ("TransferFalseOmittedEighteenthCode", "allRejectCodes.length = 17"),
        (
            "TransferFalsePolicyBeforeContext",
            '(transition constantDigest missing base { move with asset := "absent" }).verdict = '
            ".rejected (.economic .unknownAsset)",
        ),
        (
            "TransferFalseDigestInjectivity",
            '((fun (_ : B.Bytes) => "same") (stateBytes base) = '
            '(fun (_ : B.Bytes) => "same") (stateBytes { base with moduleReleaseId := "other" })) → '
            'base = { base with moduleReleaseId := "other" }',
        ),
        (
            "TransferFalseMissingSupplyRecreated",
            '(candidate { base with supplies := [] } move).supplies = [⟨"A", 10⟩]',
        ),
        (
            "TransferFalseRejectedConsumesOccurrence",
            '(transition constantDigest missing base move).effects.occurrenceConsumptions = ["occurrence"]',
        ),
    )
    for name, proposition in controls:
        _semantic_false_control(transfer_consumer_lean, name, proposition)


def _policy(
    asset: str = "A",
    collector: str = "collector",
    fee: int = 0,
    **changes: object,
) -> AssetTransferPolicyV2:
    fields: dict[str, object] = {
        "asset": asset,
        "fee_owner": collector,
        "transfer_fee_atoms": fee,
        "enabled": True,
        "asset_class": AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        "asset_origin_root": ORIGIN,
        "atom_decimals": 8,
    }
    fields.update(changes)
    return AssetTransferPolicyV2(**fields)  # type: ignore[arg-type]


def _state(
    balance: int = 5,
    owner: str = "sender",
    fee: int = 0,
    collector: str = "collector",
    supply: int | None = None,
    policies: tuple[AssetTransferPolicyV2, ...] | None = None,
    others: tuple[EconomicAmountV2, ...] = (),
) -> AssetTransferStateV2:
    selected_policies = policies or (_policy(fee=fee, collector=collector), _policy("B"))
    rows = tuple(
        sorted(
            (
                (EconomicAmountV2(owner, selected_policies[0].asset, "accounts", balance),)
                if balance
                else ()
            )
            + others,
            key=lambda row: (row.asset, row.owner, row.custody_domain),
        )
    )
    supplies = tuple(
        AssetSupplyV2(
            policy.asset,
            sum(row.amount_atoms for row in rows if row.asset == policy.asset)
            if supply is None or index
            else supply,
        )
        for index, policy in enumerate(selected_policies)
    )
    return AssetTransferStateV2(ROOT, selected_policies, rows, supplies)


def _command(
    amount: int = 1,
    max_fee: int = U128,
    **changes: object,
) -> AssetTransferCommandV2:
    command = AssetTransferCommandV2(
        "asset_transfer", "A", "sender", "recipient", amount, max_fee, ORIGIN
    )
    return replace(command, **changes)


def _context(command: AssetTransferCommandV2, **changes: object) -> AssetTransferContextV2:
    occurrence = EconomicCommandOccurrenceV2(
        "review",
        ROOT,
        1,
        0,
        0,
        command.command_kind,
        command.command_body_hash,
        ROOT,
        command.sender,
        AUTHORITY,
        1,
        ROOT,
        GLOBAL,
        (),
    )
    return replace(AssetTransferContextV2(1, ROOT, GLOBAL, occurrence), **changes)


def _wire(value: object) -> dict[str, object]:
    return json.loads(canonical_global_bytes_v2(value))


def _canonical(value: object) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"))


def _lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def _lean_option(value: str | None) -> str:
    return "none" if value is None else f"some {_lean_string(value)}"


_LEAN_CLASSES = {
    "registered_ordinary_token": "registeredOrdinaryToken",
    "tau_native_coin": "tauNativeCoin",
    "canonical_zusd": "canonicalZusd",
    "lp_share": "lpShare",
    "zdex_protocol_token": "zdexProtocolToken",
    "sealed_bid_payment_or_inventory": "sealedBidPaymentOrInventory",
}


def _lean_policy(policy: dict[str, object]) -> str:
    return (
        "⟨"
        + ", ".join(
            (
                _lean_string(str(policy["asset"])),
                _lean_string(str(policy["fee_owner"])),
                str(policy["transfer_fee_atoms"]),
                str(policy["enabled"]).lower(),
                "." + _LEAN_CLASSES[str(policy["asset_class"])],
                _lean_option(
                    policy["asset_origin_root"]
                    if isinstance(policy["asset_origin_root"], str)
                    else None
                ),
                str(policy["atom_decimals"]),
            )
        )
        + "⟩"
    )


def _lean_state(state: dict[str, object]) -> str:
    balances = state["balances"]
    supplies = state["supplies"]
    policies = state["policies"]
    assert isinstance(balances, list)
    assert isinstance(supplies, list)
    assert isinstance(policies, list)
    balance_rows = [
        "⟨"
        + ", ".join(
            (
                _lean_string(str(row["owner"])),
                _lean_string(str(row["asset"])),
                _lean_string(str(row["custody_domain"])),
                str(row["amount_atoms"]),
            )
        )
        + "⟩"
        for row in balances
        if isinstance(row, dict)
    ]
    supply_rows = [
        f"⟨{_lean_string(str(row['asset']))}, {row['amount_atoms']}⟩"
        for row in supplies
        if isinstance(row, dict)
    ]
    policy_rows = [_lean_policy(row) for row in policies if isinstance(row, dict)]
    assert len(balance_rows) == len(balances)
    assert len(supply_rows) == len(supplies)
    assert len(policy_rows) == len(policies)
    balance_expr = "[" + ", ".join(balance_rows) + "]"
    if len(balances) == 4096:
        assert all(
            row
            == {
                "owner": f"o{index:04d}",
                "asset": "A",
                "custody_domain": "accounts",
                "amount_atoms": 9,
            }
            for index, row in enumerate(balances)
        )
        balance_expr = (
            '((List.range 4096).map (fun i => ⟨"o" ++ paddedIndex i, "A", "accounts", 9⟩))'
        )
    elif len(balances) == 4095:
        tail = balances[2:]
        assert all(isinstance(row, dict) for row in tail)
        quote_total = sum(str(row["owner"]).count('"') for row in tail)
        headroom = 160 - len(str(tail[-1]["owner"]))
        assert headroom in (0, 1)
        for index, row in enumerate(tail):
            assert isinstance(row, dict)
            extra = min(155, max(0, quote_total - index * 155))
            plain = 155 - extra - (headroom if index == 4092 else 0)
            assert row == {
                "owner": f"p{index:04d}" + '"' * extra + "a" * plain,
                "asset": "A",
                "custody_domain": "accounts",
                "amount_atoms": 9,
            }
        balance_expr = (
            "(["
            + ", ".join(balance_rows[:2])
            + "] ++ ((List.range 4093).map (fun i => "
            + f"let extra := min 155 ({quote_total} - i * 155); "
            + f"let plain := 155 - extra - (if i = 4092 then {headroom} else 0); "
            + '⟨"p" ++ paddedIndex i ++ String.ofList (List.replicate extra \'"\') ++ '
            + 'String.ofList (List.replicate plain \'a\'), "A", "accounts", 9⟩)))'
        )
    return (
        "⟨"
        + ", ".join(
            (
                _lean_string(str(state["module_release_id"])),
                "[" + ", ".join(policy_rows) + "]",
                balance_expr,
                "[" + ", ".join(supply_rows) + "]",
            )
        )
        + "⟩"
    )


def _lean_command(command: AssetTransferCommandV2) -> str:
    return (
        "⟨"
        + ", ".join(
            (
                _lean_string(command.command_kind),
                _lean_string(command.command_body_hash),
                _lean_string(command.asset),
                _lean_string(command.sender),
                _lean_string(command.recipient),
                str(command.amount_atoms),
                str(command.max_fee_atoms),
                _lean_option(command.asset_origin_root),
            )
        )
        + "⟩"
    )


def _lean_context(context: AssetTransferContextV2) -> str:
    occurrence = context.occurrence
    if occurrence is None:
        occurrence_expr = "none"
    else:
        occurrence_expr = (
            "some ⟨"
            + ", ".join(
                (
                    _lean_string(occurrence.pre_state_root),
                    "["
                    + ", ".join(_lean_string(value) for value in occurrence.consumed_object_ids)
                    + "]",
                    _lean_string(occurrence.command_kind),
                    _lean_string(occurrence.command_body_hash),
                    _lean_string(occurrence.subject_id),
                    _lean_string(occurrence.grant_root),
                    _lean_string(occurrence.occurrence_id),
                )
            )
            + "⟩"
        )
    return (
        "⟨"
        + ", ".join(
            (
                _lean_string(context.module_release_id),
                _lean_string(context.global_pre_state_root),
                occurrence_expr,
            )
        )
        + "⟩"
    )


def _candidate_wire(
    pre: AssetTransferStateV2, command: AssetTransferCommandV2
) -> dict[str, object]:
    candidate = _wire(pre)
    policies = candidate["policies"]
    rows = candidate["balances"]
    assert isinstance(policies, list)
    assert isinstance(rows, list)
    policy = next(policy for policy in policies if policy["asset"] == command.asset)
    assert isinstance(policy, dict)
    deltas = {
        command.sender: -command.amount_atoms - int(policy["transfer_fee_atoms"]),
        command.recipient: command.amount_atoms,
    }
    deltas[str(policy["fee_owner"])] = deltas.get(str(policy["fee_owner"]), 0) + int(
        policy["transfer_fee_atoms"]
    )
    by_key = {(str(row["asset"]), str(row["owner"])): row for row in rows if isinstance(row, dict)}
    assert len(by_key) == len(rows)
    for owner, delta in sorted(deltas.items()):
        key = (command.asset, owner)
        previous = by_key.get(key, {})
        amount = int(previous.get("amount_atoms", 0)) + delta
        if amount:
            by_key[key] = {
                "asset": command.asset,
                "owner": owner,
                "custody_domain": "accounts",
                "amount_atoms": amount,
            }
        else:
            by_key.pop(key, None)
    candidate["balances"] = [by_key[key] for key in sorted(by_key)]
    return candidate


TypedCase = tuple[
    str,
    AssetTransferStateV2,
    AssetTransferContextV2,
    AssetTransferCommandV2,
    str,
]


def _typed_cases() -> tuple[TypedCase, ...]:
    cases: list[TypedCase] = []

    def add(
        name: str,
        pre: AssetTransferStateV2,
        command: AssetTransferCommandV2,
        expected: str,
        context: AssetTransferContextV2 | None = None,
    ) -> None:
        cases.append((name, pre, context or _context(command), command, expected))

    other = EconomicAmountV2("custody", "B", "accounts", 3)
    add(
        "strict-cover-and-other-asset",
        _state(5, supply=10, others=(other,)),
        _command(),
        "ACCEPTED",
    )
    add("collector-distinct-positive", _state(10, fee=2), _command(3), "ACCEPTED")
    add("collector-is-sender", _state(3, fee=2, collector="sender"), _command(3), "ACCEPTED")
    add("collector-is-recipient", _state(5, fee=2, collector="recipient"), _command(3), "ACCEPTED")
    add("zero-distinct-collector-omitted", _state(5), _command(5), "ACCEPTED")
    add(
        "all-three-roles-alias-rejected",
        _state(5, collector="sender", fee=1),
        _command(recipient="sender"),
        "SELF_TRANSFER",
    )
    add(
        "sender-recipient-alias-rejected",
        _state(5, fee=1),
        _command(recipient="sender"),
        "SELF_TRANSFER",
    )
    add(
        "escaping-live-tokens",
        _state(10, owner='a"\\z', collector='c"\\z', fee=2),
        _command(sender='a"\\z', recipient='r"\\z'),
        "ACCEPTED",
    )

    absent = _command(asset="C")
    absent_context = _context(absent)
    add(
        "missing-before-absent-policy",
        _state(),
        absent,
        "MISSING_OCCURRENCE",
        replace(absent_context, occurrence=None),
    )
    add(
        "binding-before-absent-policy",
        _state(),
        absent,
        "OCCURRENCE_BINDING_MISMATCH",
        replace(
            absent_context, occurrence=replace(absent_context.occurrence, pre_state_root=OTHER)
        ),
    )
    add(
        "release-before-absent-policy",
        _state(),
        absent,
        "RELEASE_MISMATCH",
        replace(absent_context, module_release_id=OTHER),
    )
    add(
        "kind-before-absent-policy",
        _state(),
        _command(asset="C", command_kind="future"),
        "UNKNOWN_COMMAND",
    )
    add(
        "body-before-absent-policy",
        _state(),
        absent,
        "OCCURRENCE_COMMAND_MISMATCH",
        replace(
            absent_context, occurrence=replace(absent_context.occurrence, command_body_hash=OTHER)
        ),
    )
    add("absent-after-first-five", _state(), absent, "UNKNOWN_ASSET")
    add(
        "disabled-before-zero",
        _state(policies=(_policy(enabled=False), _policy("B"))),
        _command(0),
        "DISABLED_ASSET",
    )
    add(
        "missing-origin",
        _state(policies=(_policy(asset_origin_root=None), _policy("B"))),
        _command(),
        "UNREGISTERED_ASSET",
    )
    add("different-origin", _state(), _command(asset_origin_root=OTHER), "ASSET_ORIGIN_MISMATCH")
    native = _state(policies=(_policy("TAU", asset_class=AssetClassV2.TAU_NATIVE_COIN),))
    add(
        "native-accounting-closed",
        native,
        _command(asset="TAU"),
        "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
    )
    zero = _command(0)
    zero_context = _context(zero)
    add(
        "subject-before-zero",
        _state(),
        zero,
        "UNAUTHORIZED_SUBJECT",
        replace(zero_context, occurrence=replace(zero_context.occurrence, subject_id="other")),
    )
    add("zero", _state(), zero, "ZERO_AMOUNT")
    add("fee-limit", _state(fee=2), _command(max_fee=1), "FEE_LIMIT_EXCEEDED")
    add("insufficient", _state(1, fee=1), _command(1), "INSUFFICIENT_BALANCE")
    add(
        "sorted-recipient-overflow-before-sender-underflow",
        _state(U128, owner="a"),
        _command(sender="z", recipient="a"),
        "BALANCE_OVERFLOW",
    )
    add(
        "sorted-sender-underflow-before-recipient-overflow",
        _state(U128, owner="z"),
        _command(sender="a", recipient="z"),
        "INSUFFICIENT_BALANCE",
    )

    add("distinct-i128-min-debit", _state(I128 + 1, fee=1), _command(I128), "ACCEPTED")
    add(
        "distinct-i128-min-one-over",
        _state(I128 + 2, fee=2),
        _command(I128),
        "EFFECT_DELTA_OVERFLOW",
    )
    add(
        "sender-alias-large-gross-net-cancels",
        _state(I128, fee=I128, collector="sender"),
        _command(I128),
        "ACCEPTED",
    )
    add(
        "sender-alias-fee-still-must-fit",
        _state(1, fee=I128 + 1, collector="sender"),
        _command(),
        "EFFECT_DELTA_OVERFLOW",
    )
    add(
        "recipient-alias-i128-max",
        _state(I128, fee=1, collector="recipient"),
        _command(I128 - 1),
        "ACCEPTED",
    )
    add(
        "recipient-alias-positive-one-over",
        _state(I128 + 1, fee=1, collector="recipient"),
        _command(I128),
        "EFFECT_DELTA_OVERFLOW",
    )
    add(
        "sender-alias-positive-recipient-one-over",
        _state(I128 + 1, collector="sender"),
        _command(I128 + 1),
        "EFFECT_DELTA_OVERFLOW",
    )

    full_rows = tuple(
        EconomicAmountV2(f"o{index:04d}", "A", "accounts", 9) for index in range(4096)
    )
    full = AssetTransferStateV2(
        ROOT,
        (_policy(fee=1), _policy("B")),
        full_rows,
        (AssetSupplyV2("A", 9 * 4096), AssetSupplyV2("B", 0)),
    )
    add("final-two-new-rows-over-cap", full, _command(1, sender="o0000"), "STATE_RESOURCE_LIMIT")
    add("economic-zero-before-cap", full, _command(0, sender="o0000"), "ZERO_AMOUNT")
    full_zero = AssetTransferStateV2(ROOT, (_policy(), _policy("B")), full_rows, full.supplies)
    add(
        "credit-before-sender-deletion-final-cap",
        full_zero,
        _command(9, sender="o4095", recipient="a-new"),
        "ACCEPTED",
    )
    add(
        "same-full-table-existing-recipient",
        full_zero,
        _command(1, sender="o4095", recipient="o0000"),
        "ACCEPTED",
    )

    byte_rows = [
        {"owner": "a-recipient", "asset": "A", "custody_domain": "accounts", "amount_atoms": 9},
        {"owner": "b-sender", "asset": "A", "custody_domain": "accounts", "amount_atoms": 11},
    ]
    byte_rows.extend(
        {
            "owner": f"p{index:04d}" + "a" * 155,
            "asset": "A",
            "custody_domain": "accounts",
            "amount_atoms": 9,
        }
        for index in range(4093)
    )
    byte_wire = _wire(
        AssetTransferStateV2(
            ROOT, (_policy(), _policy("B")), (), (AssetSupplyV2("A", 99999), AssetSupplyV2("B", 0))
        )
    )
    byte_wire["balances"] = byte_rows
    needed = STATE_BYTE_CAP - len(_canonical(byte_wire).encode())
    assert 0 <= needed <= 4093 * 155
    for row in byte_rows[2:]:
        extra = min(needed, 155)
        row["owner"] = str(row["owner"])[:5] + '"' * extra + "a" * (155 - extra)
        needed -= extra
    assert len(_canonical(byte_wire).encode()) == STATE_BYTE_CAP

    def typed(wire: dict[str, object]) -> AssetTransferStateV2:
        wire_rows = wire["balances"]
        assert isinstance(wire_rows, list)
        return AssetTransferStateV2(
            ROOT,
            (_policy(), _policy("B")),
            tuple(
                EconomicAmountV2(str(row["owner"]), "A", "accounts", int(row["amount_atoms"]))
                for row in wire_rows
                if isinstance(row, dict)
            ),
            (AssetSupplyV2("A", 99999), AssetSupplyV2("B", 0)),
        )

    byte_state = typed(byte_wire)
    assert len(byte_state.balances) == len(byte_rows) == 4095
    add(
        "exact-byte-cap-one-byte-growth",
        byte_state,
        _command(sender="b-sender", recipient="a-recipient"),
        "STATE_RESOURCE_LIMIT",
    )
    byte_rows[-1]["owner"] = str(byte_rows[-1]["owner"])[:-1]
    assert len(_canonical(byte_wire).encode()) == STATE_BYTE_CAP - 1
    add(
        "one-byte-headroom-neighbor",
        typed(byte_wire),
        _command(sender="b-sender", recipient="a-recipient"),
        "ACCEPTED",
    )
    assert len(cases) == 37
    return tuple(cases)


@dataclass(frozen=True)
class Observation:
    case: TypedCase
    expected: dict[str, object]
    full_post_bytes: str | None


def _runtime_observation(case: TypedCase) -> Observation:
    name, pre, context, command, expected_code = case
    before = canonical_global_bytes_v2(pre)
    result = transition_asset_transfer_v2(context, pre, command)
    accepted = isinstance(result, AssetTransferAcceptedV2)
    assert isinstance(result, (AssetTransferAcceptedV2, AssetTransferRejectedV2))
    code = "ACCEPTED" if accepted else result.code.value
    assert code == expected_code, name
    assert canonical_global_bytes_v2(pre) == before, name
    post = result.post_state if accepted else pre
    if accepted:
        assert result.effects.is_empty is False, name
    else:
        assert result.pre_state_root == pre.state_root == result.post_state_root, name
        assert result.effects.is_empty, name
    assert post.supplies == pre.supplies, name
    post_bytes = canonical_global_bytes_v2(post)
    assert post_bytes.decode() == _canonical(_wire(post)), name
    full_post_bytes = post_bytes.decode() if len(post_bytes) < 10_000 else None
    candidate_bytes = None
    if code in {"ACCEPTED", "STATE_RESOURCE_LIMIT"}:
        candidate_bytes = len(_canonical(_candidate_wire(pre, command)).encode())
    effects_wire = _wire(result.effects)
    rows = effects_wire["rows"]
    assert isinstance(rows, list)
    movements = (
        [
            [row["principal"], row["delta_atoms"]]
            for row in rows
            if row["kind"] == "ACCOUNT_MOVEMENT"
        ]
        if accepted
        else None
    )
    fees = (
        [[row["principal"], row["delta_atoms"]] for row in rows if row["kind"] == "FEE_ALLOCATION"]
        if accepted
        else None
    )
    expected = {
        "name": name,
        "code": code,
        "pre_bytes": len(before),
        "post_bytes": len(post_bytes),
        "candidate_bytes": candidate_bytes,
        "post_balance_count": len(post.balances),
        "post_supply_assets": [row.asset for row in post.supplies],
        "post_supply_amounts": [row.amount_atoms for row in post.supplies],
        "post_account_totals": [
            sum(row.amount_atoms for row in post.balances if row.asset == policy.asset)
            for policy in post.policies
        ],
        "post_unchanged": post == pre,
        "effects_empty": result.effects.is_empty,
        "lane_writes": len(result.effects.lane_writes),
        "occurrence_consumptions": len(result.effects.occurrence_consumptions),
        "movements": movements,
        "fee_allocations": fees,
        "post_bytes_match": True if full_post_bytes is not None else None,
    }
    return Observation(case, expected, full_post_bytes)


CASE_PREAMBLE = r"""
import Proofs.AssetTransferFiniteOutcomeV2
import Lean.Data.Json

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Proofs.AssetTransferFiniteOutcomeV2

namespace IndependentTransferCases

def paddedIndex (i : Nat) : String :=
  String.ofList (List.replicate (4 - (toString i).length) '0') ++ toString i

def observation (name : String) (pre : State) (ctx : T.Context) (command : T.Command)
    (expectedPost : Option String) : Lean.Json := Id.run do
  let result := transition (fun bytes => toString bytes.length) ctx pre command
  let code := match result.verdict with | .accepted => "ACCEPTED" | .rejected code => code.code
  let totals := result.post.policies.map (fun policy =>
    Proofs.GlobalEconomicStateRefinementV2.amountForAsset result.post.balances policy.asset)
  let byteMatch := expectedPost.map (fun bytes => stateBytes result.post == B.raw bytes)
  let candidateBytes := if code == "ACCEPTED" || code == "STATE_RESOURCE_LIMIT" then
    some (stateBytes (candidate pre command)).length else none
  let movements := result.effects.payload.map (fun payload =>
    payload.movements.map (fun row => (row.principal, row.deltaAtoms)))
  let fees := result.effects.payload.map (fun payload =>
    payload.feeAllocations.map (fun row => (row.principal, row.deltaAtoms)))
  return Lean.Json.mkObj [
    ("name", Lean.toJson name), ("code", Lean.toJson code),
    ("pre_bytes", Lean.toJson (stateBytes pre).length),
    ("post_bytes", Lean.toJson (stateBytes result.post).length),
    ("candidate_bytes", Lean.toJson candidateBytes),
    ("post_balance_count", Lean.toJson result.post.balances.length),
    ("post_supply_assets", Lean.toJson (result.post.supplies.map (fun row => row.asset))),
    ("post_supply_amounts", Lean.toJson (result.post.supplies.map (fun row => row.amountAtoms))),
    ("post_account_totals", Lean.toJson totals),
    ("post_unchanged", Lean.toJson (result.post == pre)),
    ("effects_empty", Lean.toJson (result.effects == Proofs.AssetTransferRefinementV2.EffectEnvelope.empty)),
    ("lane_writes", Lean.toJson result.effects.laneWrites.length),
    ("occurrence_consumptions", Lean.toJson result.effects.occurrenceConsumptions.length),
    ("movements", Lean.toJson movements), ("fee_allocations", Lean.toJson fees),
    ("post_bytes_match", Lean.toJson byteMatch)]

#eval IO.println ((Lean.toJson (allRejectCodes.map RejectCode.code)).compress)
"""


def _case_source(observations: tuple[Observation, ...]) -> str:
    declarations: list[str] = []
    states: dict[str, str] = {}
    for index, observation in enumerate(observations):
        name, pre, context, command, _ = observation.case
        pre_bytes = canonical_global_bytes_v2(pre)
        state_hash = hashlib.sha256(pre_bytes).hexdigest()
        state_name = states.get(state_hash)
        if state_name is None:
            state_name = f"pre{len(states)}"
            states[state_hash] = state_name
            declarations.append(f"def {state_name} : State := {_lean_state(_wire(pre))}")
        expected_post = (
            "none"
            if observation.full_post_bytes is None
            else f"some {_lean_string(observation.full_post_bytes)}"
        )
        declarations.extend(
            (
                f"def command{index} : T.Command := {_lean_command(command)}",
                f"def context{index} : T.Context := {_lean_context(context)}",
                f"#eval IO.println ((observation {_lean_string(name)} {state_name} context{index} "
                f"command{index} ({expected_post})).compress)",
            )
        )
    return CASE_PREAMBLE + "\n\n".join(declarations) + "\nend IndependentTransferCases\n"


def _parse_case_output(output: str) -> tuple[list[str], list[dict[str, object]]]:
    registry: list[str] | None = None
    records: list[dict[str, object]] = []
    for line in output.splitlines():
        if line.startswith("["):
            assert registry is None
            decoded = json.loads(line)
            assert isinstance(decoded, list) and all(isinstance(item, str) for item in decoded)
            registry = decoded
        elif line.startswith("{"):
            decoded = json.loads(line)
            assert isinstance(decoded, dict)
            records.append(decoded)
        elif line.strip():
            raise AssertionError(f"unexpected Lean output: {line}")
    assert registry is not None
    return registry, records


def test_actual_typed_finite_vectors_match_lean_outcomes_and_bytes(
    transfer_outcome_lean: LeanSubject,
) -> None:
    cases = _typed_cases()
    observations = tuple(_runtime_observation(case) for case in cases)
    assert len(cases) == len(observations) == 37
    assert [code.value for code in AssetTransferRejectCodeV2] == EXPECTED_REJECT_CODES
    assert sum(item.full_post_bytes is not None for item in observations) == 31

    boundaries = {item.expected["name"]: item.expected for item in observations}
    assert boundaries["final-two-new-rows-over-cap"] == {
        **boundaries["final-two-new-rows-over-cap"],
        "code": "STATE_RESOURCE_LIMIT",
        "pre_bytes": 307889,
        "candidate_bytes": 308047,
        "post_balance_count": 4096,
        "post_unchanged": True,
    }
    assert boundaries["credit-before-sender-deletion-final-cap"] == {
        **boundaries["credit-before-sender-deletion-final-cap"],
        "code": "ACCEPTED",
        "pre_bytes": 307889,
        "candidate_bytes": 307889,
        "post_balance_count": 4096,
        "post_unchanged": False,
    }
    assert boundaries["exact-byte-cap-one-byte-growth"] == {
        **boundaries["exact-byte-cap-one-byte-growth"],
        "code": "STATE_RESOURCE_LIMIT",
        "pre_bytes": STATE_BYTE_CAP,
        "candidate_bytes": STATE_BYTE_CAP + 1,
        "post_unchanged": True,
    }
    assert boundaries["one-byte-headroom-neighbor"] == {
        **boundaries["one-byte-headroom-neighbor"],
        "code": "ACCEPTED",
        "pre_bytes": STATE_BYTE_CAP - 1,
        "candidate_bytes": STATE_BYTE_CAP,
        "post_unchanged": False,
    }

    # Bound each checker invocation without dropping large resource cases.
    records: list[dict[str, object]] = []
    for start in range(0, len(observations), 4):
        batch = observations[start : start + 4]
        result = _raw_consumer(
            transfer_outcome_lean,
            f"TransferFiniteOutcomeRuntimeCases{start}",
            _case_source(batch),
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stderr == ""
        registry, batch_records = _parse_case_output(result.stdout)
        assert registry == EXPECTED_REJECT_CODES
        assert [record["name"] for record in batch_records] == [item.case[0] for item in batch]
        records.extend(batch_records)
    assert len(records) == len(observations) == 37
    assert [record["name"] for record in records] == [item.case[0] for item in observations]
    assert all(record == item.expected for record, item in zip(records, observations, strict=True))
    observed_rejects = {str(record["code"]) for record in records if record["code"] != "ACCEPTED"}
    assert observed_rejects == set(EXPECTED_REJECT_CODES)
    accepted = [record for record in records if record["code"] == "ACCEPTED"]
    assert accepted
    assert all(
        record["movements"] is not None and record["fee_allocations"] is not None
        for record in accepted
    )
