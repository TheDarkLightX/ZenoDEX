"""Independent retained consumers for the finite managed-asset outcome proof.

The Lean model consumes actual finite policy, balance,
complete-supply, context, and command values generated from the 37 runtime
twins; it does not use the scalar post-state witness from the older parity
test.

This is bounded differential evidence for the proof/model and the current
runtime corpus.  It does not establish universal runtime refinement, digest or
serializer equivalence outside the emitted finite bytes, admission, registry,
coordinator, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

import pytest

from src.core.managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleStateV2,
)
from tests.formal.test_lean_asset_lane_finite_byte_accounting_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_finite_byte_accounting_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_asset_lane_finite_byte_accounting_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_finite_byte_accounting_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_lane_finite_byte_accounting_v2 import lean as lean
from tests.formal.test_lean_asset_lane_finite_byte_accounting_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_asset_lane_finite_byte_accounting_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_managed_asset_runtime_parity_v2 import (
    TWINS,
    Twin,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "ManagedAssetFiniteOutcomeV2"
NAMESPACE = f"Proofs.{MODULE}"
REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE = REPO_ROOT / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "7b9f48708aac9ecc491c06af78cdc1d4d8ea7c0d60ec2353c91ee7a010168a9b"
PREAMBLE = f"""import {NAMESPACE}
open Proofs
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1 Proofs.RegisteredSupplyViewV1
open {NAMESPACE}
attribute [local instance] lexOrd
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
"""

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
    "supply_lookup_u128",
    "balance_lookup_u128",
    "amountForAsset_nonnegative",
    "project_well_formed",
    "updateRows_supported",
    "updateRows_ordered",
    "economic_candidate_structural",
    "accepted_preserves_admission",
    "candidate_project",
    "accepted_selected_leaf",
    "accepted_accounting",
    "accepted_effect_delta_i128",
    "accepted_effects_bind",
    "selected_post_stage",
    "issue_supply_overflow_precedes_resources",
    "candidate_byte_equation",
    "candidate_resources_iff_source_capacity",
    "dormant_issue_at_row_cap_rejected",
    "accepted_iff_full_guards_capacity",
    "resource_reject_iff_full_guards_capacity",
    "accepted_supply_identity",
    "transition_preserves_admission",
    "trace_preserves_admission",
    "trace_prefixes_admitted",
)

# These are the externally meaningful outcome/capacity contracts.  The source
# declaration inventory and axiom probe below cover every theorem in the file.
THEOREM_TYPES = {
    "accepted_iff": """∀ (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State) (command : M.Command),
      (transition digest ctx pre command).verdict = .accepted ↔
        economicRejectCode ctx pre command = none ∧ Resources (candidate pre command)""",
    "resource_reject_iff": """∀ (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State) (command : M.Command),
      (transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
        economicRejectCode ctx pre command = none ∧ ¬ Resources (candidate pre command)""",
    "economic_reject_precedes_resource": """∀ (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State)
      (command : M.Command) (code : M.RejectCode)
      (_ : economicRejectCode ctx pre command = some code),
      transition digest ctx pre command = reject (.economic code) pre""",
    "rejected_noop": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State} {command : M.Command}
      {code : ManagedAssetFiniteOutcomeV2.RejectCode},
      (transition digest ctx pre command).verdict = .rejected code →
      (transition digest ctx pre command).post = pre ∧
        stateRoot digest (transition digest ctx pre command).post = stateRoot digest pre ∧
        (transition digest ctx pre command).effects =
          Proofs.AssetTransferRefinementV2.EffectEnvelope.empty""",
    "accepted_post_effects": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State} {command : M.Command},
      (transition digest ctx pre command).verdict = .accepted →
      (transition digest ctx pre command).post = candidate pre command ∧
        (transition digest ctx pre command).effects = acceptedEffects digest ctx pre command""",
    "accepted_effects_bind": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State} {command : M.Command},
      (transition digest ctx pre command).verdict = .accepted →
      (transition digest ctx pre command).effects.payload = some (payload pre command) ∧
        (transition digest ctx pre command).effects.laneWrites =
          [⟨stateRoot digest pre, stateRoot digest (transition digest ctx pre command).post⟩] ∧
        (transition digest ctx pre command).effects.occurrenceConsumptions = M.occurrenceIds ctx ∧
        (transition digest ctx pre command).effects.externalOutbox = [] ∧
        (transition digest ctx pre command).effects.externalRoots =
          AssetTransferRefinementV2.ExternalRoots.zero""",
    "accepted_accounting": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State}
      {command : M.Command} (_ : Structural pre)
      (_ : (transition digest ctx pre command).verdict = .accepted) (asset : Asset),
      amountForAsset (transition digest ctx pre command).post.balances asset =
          amountForAsset pre.balances asset +
            (if command.asset = asset then M.signedAmount command else 0) ∧
        supplyFor (numericRows (transition digest ctx pre command).post.supplies) asset =
          supplyFor (numericRows pre.supplies) asset +
            (if asset = command.asset then M.signedAmount command else 0)""",
    "candidate_resources_iff_source_capacity": """∀ {pre : State} {command : M.Command}
      (_ : S.Unique pre.balances) (_ : SourceAssetKeysUnique pre.supplies)
      (_ : command.asset ∈ pre.supplies.map V1SupplyRow.asset),
      Resources (candidate pre command) ↔ SourceCapacity pre command""",
    "accepted_supply_identity": """∀ {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State}
      {command : M.Command} (_ : Structural pre)
      (_ : (transition digest ctx pre command).verdict = .accepted),
      (transition digest ctx pre command).post.supplies.map V1SupplyRow.asset =
          pre.supplies.map V1SupplyRow.asset ∧
        numericRows (transition digest ctx pre command).post.supplies =
          adjustSparse command.asset (M.signedAmount command) (numericRows pre.supplies) ∧
        decode ⟨pre.supplies.map V1SupplyRow.asset,
          adjustSparse command.asset (M.signedAmount command) (numericRows pre.supplies)⟩ =
          (transition digest ctx pre command).post.supplies""",
    "trace_prefixes_admitted": """∀ {rootSyntax : String → Prop}
      {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → M.Root)
      (pre : State) (trace : List (M.Context × M.Command))
      (_ : Admitted rootSyntax namespaceSyntax pre)
      (_ : ∀ input ∈ trace, M.CommandWellFormed input.2 ∧ B.ValidToken input.2.accountOwner)
      (length : Nat),
      Admitted rootSyntax namespaceSyntax (executeTrace digest pre (trace.take length))""",
}


@pytest.fixture(scope="module")
def outcome_lean(byte_accounting_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    subject = byte_accounting_lean
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


def test_exact_theorem_surface_and_standard_axioms(outcome_lean: LeanSubject) -> None:
    source_code = SOURCE.read_text()
    declared = tuple(re.findall(r"^theorem\s+(\w+)", source_code, flags=re.MULTILINE))
    assert declared == THEOREM_NAMES
    assert len(declared) == len(set(declared)) == 42
    code = re.sub(r"/-.*?-/", "", source_code, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    body += "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in THEOREM_NAMES)
    result = _consumer(outcome_lean, "ManagedFiniteOutcomeContracts", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    assert result.stdout.count("depends on axioms") + result.stdout.count(
        "does not depend on any axioms"
    ) == len(THEOREM_TYPES) + len(THEOREM_NAMES)
    assert _axiom_names(result.stdout) <= {"propext", "Quot.sound", "Classical.choice"}


FINITE_CONSUMER = r"""
namespace IndependentFiniteOutcome

def release : String := "0x4444444444444444444444444444444444444444444444444444444444444444"
def origin : String := "0x1111111111111111111111111111111111111111111111111111111111111111"
def issueGrant : String := "0x2222222222222222222222222222222222222222222222222222222222222222"
def burnGrant : String := "0x3333333333333333333333333333333333333333333333333333333333333333"
def owner : String := "ali\"ce\\x"
def ordinary (asset : String) : M.Policy :=
  ⟨asset, .registeredOrdinaryToken, some origin, 8, some ⟨"issuer", issueGrant⟩, some burnGrant, true⟩
def issue : M.Command :=
  ⟨ManagedAssetLifecycleRefinementV2.issueCommandKind, "issue-body", "USD", .registeredOrdinaryToken,
    some origin, 8, some issueGrant, owner, 1⟩
def context : M.Context :=
  ⟨release, "global", some ⟨"global", [], issue.commandKind, "issue-body", "issuer", issueGrant, "occ-issue"⟩⟩
def pre : State :=
  ⟨release, [ordinary "AUD", ordinary "USD", ordinary "ZZZ"],
    [⟨"bob", "AUD", "accounts", 4⟩, ⟨owner, "USD", "accounts", 9⟩],
    [⟨"AUD", 4⟩, ⟨"USD", 9⟩, ⟨"ZZZ", 0⟩]⟩
def observe : B.Bytes → M.Root := fun bytes => toString bytes.length
def unknown : M.Command := {issue with asset := "MISSING"}
def ten : State := {pre with
  balances := [⟨"bob", "AUD", "accounts", 4⟩, ⟨owner, "USD", "accounts", 10⟩],
  supplies := [⟨"AUD", 4⟩, ⟨"USD", 10⟩, ⟨"ZZZ", 0⟩]}
def zero : State := {pre with
  balances := [⟨"bob", "AUD", "accounts", 4⟩],
  supplies := [⟨"AUD", 4⟩, ⟨"USD", 0⟩, ⟨"ZZZ", 0⟩]}
def one : State := {pre with
  balances := [⟨"bob", "AUD", "accounts", 4⟩, ⟨owner, "USD", "accounts", 1⟩],
  supplies := [⟨"AUD", 4⟩, ⟨"USD", 1⟩, ⟨"ZZZ", 0⟩]}
def burn : M.Command := {issue with
  commandKind := ManagedAssetLifecycleRefinementV2.burnCommandKind,
  commandBodyHash := "burn-body", authorizationRoot := some burnGrant, amountAtoms := 10}
def burnContext : M.Context :=
  ⟨release, "global", some ⟨"global", [], burn.commandKind, "burn-body", owner, burnGrant, "occ-burn"⟩⟩
def mixed : List (M.Context × M.Command) := [(context, issue), (context, unknown), (burnContext, burn), (context, issue)]

theorem sortAudUsd (atoms : Int) :
    C.sortOn S.balanceWire [⟨owner, "USD", "accounts", atoms⟩, ⟨"bob", "AUD", "accounts", 4⟩] =
      [⟨"bob", "AUD", "accounts", 4⟩, ⟨owner, "USD", "accounts", atoms⟩] :=
  AssetLaneFiniteRecompositionV2.sortOn_eq_of_perm_keys _ _ _
    (List.Perm.swap _ _ [])
    (by change ([(("AUD", "bob") : String × String), ("USD", owner)]).Nodup; decide)
    (by
      constructor
      · intro row member
        have same : row = (⟨owner, "USD", "accounts", atoms⟩ : AmountRow) := List.mem_singleton.mp member
        subst row
        change (compare (("AUD", "bob") : String × String) ("USD", owner)).isLE = true
        decide
      · exact List.pairwise_singleton _ _)

theorem exactRows : candidate pre issue = ten ∧ candidate ten burn = zero ∧ candidate zero issue = one := by
  simp +decide [candidate, pre, issue, ten, zero, one, burn,
    M.signedAmount, ManagedAssetLifecycleRefinementV2.issueCommandKind,
    ManagedAssetLifecycleRefinementV2.burnCommandKind, A.updateRows, C.lookupLast, C.amountKey,
    S.accountKey, S.putAmount, AssetTransferSparseTablesV1.eraseKey,
    AssetTransferSparseTablesV1.makeAmount, S.accounts, C.sortOn, S.balanceWire,
    adjustComplete]
  exact ⟨sortAudUsd 10, sortAudUsd 1⟩

example : B.ValidToken owner := by unfold B.ValidToken; decide
example : policyFor pre "USD" = some (ordinary "USD") := by decide
example : pre.supplies.map V1SupplyRow.asset = pre.policies.map (fun policy => policy.asset) ∧
    numericRows pre.supplies = [⟨"AUD", 4⟩, ⟨"USD", 9⟩] := by decide
example : (B.quoted owner).length = 12 ∧ (B.raw owner).length = 8 := by decide
example : AssetLaneFiniteByteAccountingV2.numberCost 0 = 1 ∧
    AssetLaneFiniteByteAccountingV2.numberCost 9 = 1 ∧
    AssetLaneFiniteByteAccountingV2.numberCost 10 = 2 ∧
    AssetLaneFiniteByteAccountingV2.numberCost 99 = 2 ∧
    AssetLaneFiniteByteAccountingV2.numberCost 100 = 3 ∧
    AssetLaneFiniteByteAccountingV2.numberCost
      (340282366920938463463374607431768211455 : Int) = 39 := by decide
example : (AssetLaneFiniteByteAccountingV2.balanceBytes []).length = 2 ∧
    (AssetLaneFiniteByteAccountingV2.supplyBytes
      [⟨"AUD", 0⟩, ⟨"USD", 0⟩, ⟨"ZZZ", 0⟩]).length ≠
      (AssetLaneFiniteByteAccountingV2.supplyBytes []).length := by decide
example : (candidate pre issue).balances.length = 2 ∧
    (candidate pre issue).supplies = ten.supplies := by
  rw [exactRows.1]
  decide
example : (transition observe context pre issue).verdict = .accepted := by
  apply (accepted_iff observe context pre issue).mpr
  refine ⟨by decide, ?_⟩
  apply (candidate_resources_iff_source_capacity (by unfold S.Unique; decide)
    (by unfold SourceAssetKeysUnique; decide) (by decide)).mpr
  unfold SourceCapacity
  decide
example : (transition observe context pre unknown).verdict =
    .rejected (.economic .unknownAsset) := by
  rw [economic_reject_precedes_resource observe context pre unknown .unknownAsset (by decide)]
  rfl
example : (transition observe context pre unknown).post = pre ∧
    (transition observe context pre unknown).effects =
      AssetTransferRefinementV2.EffectEnvelope.empty := by
  have rejected : (transition observe context pre unknown).verdict =
      .rejected (.economic .unknownAsset) := by
    rw [economic_reject_precedes_resource observe context pre unknown .unknownAsset (by decide)]
    rfl
  have noop := rejected_noop rejected
  exact ⟨noop.1, noop.2.2⟩
example : (transition observe burnContext ten burn).verdict = .accepted := by
  apply (accepted_iff observe burnContext ten burn).mpr
  refine ⟨by decide, ?_⟩
  apply (candidate_resources_iff_source_capacity (by unfold S.Unique; decide)
    (by unfold SourceAssetKeysUnique; decide) (by decide)).mpr
  unfold SourceCapacity
  decide
example : (transition observe context zero issue).verdict = .accepted := by
  apply (accepted_iff observe context zero issue).mpr
  refine ⟨by decide, ?_⟩
  apply (candidate_resources_iff_source_capacity (by unfold S.Unique; decide)
    (by unfold SourceAssetKeysUnique; decide) (by decide)).mpr
  unfold SourceCapacity
  decide
example : executeTrace observe pre mixed = one := by
  simp only [mixed, executeTrace]
  have issueAccepted : (transition observe context pre issue).verdict = .accepted := by
    apply (accepted_iff observe context pre issue).mpr
    refine ⟨by decide, ?_⟩
    apply (candidate_resources_iff_source_capacity (by unfold S.Unique; decide)
      (by unfold SourceAssetKeysUnique; decide) (by decide)).mpr
    unfold SourceCapacity
    decide
  rw [(accepted_post_effects (digest := observe) (ctx := context) (pre := pre)
    (command := issue) issueAccepted).1, exactRows.1]
  have unknownAtTen : (transition observe context ten unknown).verdict =
      .rejected (.economic .unknownAsset) := by
    rw [economic_reject_precedes_resource observe context ten unknown .unknownAsset (by decide)]
    rfl
  rw [(rejected_noop unknownAtTen).1]
  have burnAccepted : (transition observe burnContext ten burn).verdict = .accepted := by
    apply (accepted_iff observe burnContext ten burn).mpr
    refine ⟨by decide, ?_⟩
    apply (candidate_resources_iff_source_capacity (by unfold S.Unique; decide)
      (by unfold SourceAssetKeysUnique; decide) (by decide)).mpr
    unfold SourceCapacity
    decide
  rw [(accepted_post_effects (digest := observe) (ctx := burnContext) (pre := ten)
    (command := burn) burnAccepted).1, exactRows.2.1]
  have reissueAccepted : (transition observe context zero issue).verdict = .accepted := by
    apply (accepted_iff observe context zero issue).mpr
    refine ⟨by decide, ?_⟩
    apply (candidate_resources_iff_source_capacity (by unfold S.Unique; decide)
      (by unfold SourceAssetKeysUnique; decide) (by decide)).mpr
    unfold SourceCapacity
    decide
  rw [(accepted_post_effects (digest := observe) (ctx := context) (pre := zero)
    (command := issue) reissueAccepted).1]
  exact exactRows.2.2
example : (transition observe context pre issue).effects.externalOutbox = [] ∧
    (transition observe context pre issue).effects.externalRoots =
      AssetTransferRefinementV2.ExternalRoots.zero := by
  have accepted : (transition observe context pre issue).verdict = .accepted := by
    apply (accepted_iff observe context pre issue).mpr
    refine ⟨by decide, ?_⟩
    apply (candidate_resources_iff_source_capacity (by unfold S.Unique; decide)
      (by unfold SourceAssetKeysUnique; decide) (by decide)).mpr
    unfold SourceCapacity
    decide
  have bound := accepted_effects_bind accepted
  exact ⟨bound.2.2.2.1, bound.2.2.2.2⟩
example : allRejectCodes.length = 22 ∧
    (allRejectCodes.map ManagedAssetFiniteOutcomeV2.RejectCode.code).Nodup ∧
    ManagedAssetFiniteOutcomeV2.RejectCode.stateResourceLimit ∈ allRejectCodes := by decide

example {digest : B.Bytes → M.Root} {ctx : M.Context} {state : State} {command : M.Command}
    (shape : Structural state) (economic : economicRejectCode ctx state command = none)
    (isIssue : M.isIssue command) (positive : 0 < command.amountAtoms)
    (dormant : C.lookupLast (S.accountKey command.asset command.accountOwner) state.balances = 0)
    (full : state.balances.length = 4096) :
    (transition digest ctx state command).verdict = .rejected .stateResourceLimit ∧
      (transition digest ctx state command).post = state ∧
      (transition digest ctx state command).effects = AssetTransferRefinementV2.EffectEnvelope.empty := by
  have rejected := dormant_issue_at_row_cap_rejected shape economic isIssue positive dormant full
    (digest := digest)
  have noop := rejected_noop rejected
  exact ⟨rejected, noop.1, noop.2.2⟩

end IndependentFiniteOutcome
"""


def test_independent_finite_trace_resource_noop_and_literal_controls(
    outcome_lean: LeanSubject,
) -> None:
    result = _consumer(outcome_lean, "ManagedFiniteOutcomeConcrete", FINITE_CONSUMER)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""


def _semantic_false_control(
    subject: LeanSubject, name: str, proposition: str, expected_fragment: str
) -> None:
    result = _consumer(
        subject,
        name,
        f"example : {proposition} := by decide\n",
    )
    output = result.stdout + result.stderr
    assert result.returncode != 0
    assert result.stderr == ""
    assert result.stdout.count("error:") == 1, result.stdout
    assert expected_fragment in output, output
    assert "is false" in output
    assert "unexpected token" not in output
    assert "unexpected identifier" not in output
    assert "failed to synthesize" not in output


def test_finite_outcome_false_laws_are_semantic_failures(
    outcome_lean: LeanSubject,
) -> None:
    controls = (
        (
            "ManagedFiniteFalseOmittedResourceCode",
            "ManagedAssetFiniteOutcomeV2.RejectCode.stateResourceLimit ∉ allRejectCodes",
        ),
        (
            "ManagedFiniteFalseMissingOccurrenceBecomesUnknownAsset",
            "economicRejectCode "
            '⟨"release", "global", none⟩ '
            '⟨"release", [], [], []⟩ '
            '⟨"managed_asset_issue", "body", "MISSING", .registeredOrdinaryToken, '
            'none, 8, none, "owner", 1⟩ = some .unknownAsset',
        ),
        (
            "ManagedFiniteFalseRejectedConsumesOccurrence",
            '(transition (fun _ => "same") '
            '⟨"release", "global", some ⟨"global", [], '
            '"managed_asset_issue", "body", "issuer", "grant", "occ"⟩⟩ '
            '⟨"release", [], [], []⟩ '
            '⟨"managed_asset_issue", "body", "MISSING", .registeredOrdinaryToken, '
            'none, 8, none, "owner", 1⟩).effects.occurrenceConsumptions = ["occ"]',
        ),
        (
            "ManagedFiniteFalseConstantDigestImpliesEqualState",
            '((fun (_ : B.Bytes) => "same") '
            '(stateBytes ⟨"release", [], [], []⟩) = '
            '(fun (_ : B.Bytes) => "same") (stateBytes ⟨"other", [], [], []⟩)) → '
            '(⟨"release", [], [], []⟩ : State) = ⟨"other", [], [], []⟩',
        ),
    )
    for name, proposition in controls:
        _semantic_false_control(
            outcome_lean,
            name,
            proposition,
            "Tactic `decide` proved that the proposition",
        )


def _lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


_LEAN_ASSET_CLASSES = {
    "tau_native_coin": ".tauNativeCoin",
    "canonical_zusd": ".canonicalZusd",
    "lp_share": ".lpShare",
    "zdex_protocol_token": ".zdexProtocolToken",
    "sealed_bid_payment_or_inventory": ".sealedBidPaymentOrInventory",
    "registered_ordinary_token": ".registeredOrdinaryToken",
}


def _lean_option_string(value: str | None) -> str:
    return "none" if value is None else f"some {_lean_string(value)}"


def _lean_policy(policy: ManagedAssetLifecyclePolicyV2) -> str:
    issue_subject = policy.issue_authority_subject
    issue_root = policy.issue_authorization_root
    if issue_subject is None:
        issue_authority = "none"
    else:
        assert issue_root is not None
        issue_authority = f"some ⟨{_lean_string(issue_subject)}, {_lean_string(issue_root)}⟩"
    return (
        f"⟨{_lean_string(policy.asset)}, "
        f"{_LEAN_ASSET_CLASSES[policy.asset_class.value]}, "
        f"{_lean_option_string(policy.asset_origin_root)}, "
        f"{policy.atom_decimals}, {issue_authority}, "
        f"{_lean_option_string(policy.burn_authorization_root)}, "
        f"{'true' if policy.enabled else 'false'}⟩"
    )


def _lean_list(items: list[str]) -> str:
    return "[" + ", ".join(items) + "]"


def _lean_state(state: ManagedAssetLifecycleStateV2) -> str:
    policies = _lean_list([_lean_policy(policy) for policy in state.policies])
    balances = _lean_list(
        [
            f"⟨{_lean_string(row.owner)}, {_lean_string(row.asset)}, "
            f"{_lean_string(row.custody_domain)}, {row.amount_atoms}⟩"
            for row in state.balances
        ]
    )
    supplies = _lean_list(
        [f"⟨{_lean_string(row.asset)}, {row.amount_atoms}⟩" for row in state.supplies]
    )
    return f"⟨{_lean_string(state.module_release_id)}, {policies}, {balances}, {supplies}⟩"


def _lean_command(command: ManagedAssetLifecycleCommandV2) -> str:
    return (
        f"⟨{_lean_string(command.command_kind)}, {_lean_string(command.command_body_hash)}, "
        f"{_lean_string(command.asset)}, {_LEAN_ASSET_CLASSES[command.asset_class.value]}, "
        f"{_lean_option_string(command.asset_origin_root)}, {command.atom_decimals}, "
        f"{_lean_option_string(command.authorization_root)}, {_lean_string(command.account_owner)}, "
        f"{command.amount_atoms}⟩"
    )


def _lean_context(twin: Twin) -> str:
    context = twin.context
    occurrence = context.occurrence
    if occurrence is None:
        occurrence_literal = "none"
    else:
        consumed = _lean_list([_lean_string(item) for item in occurrence.consumed_object_ids])
        occurrence_literal = (
            f"some ⟨{_lean_string(occurrence.pre_state_root)}, {consumed}, "
            f"{_lean_string(occurrence.command_kind)}, {_lean_string(occurrence.command_body_hash)}, "
            f"{_lean_string(occurrence.subject_id)}, {_lean_string(occurrence.grant_root)}, "
            f"{_lean_string(occurrence.occurrence_id)}⟩"
        )
    return (
        f"⟨{_lean_string(context.module_release_id)}, {_lean_string(context.global_pre_state_root)}, "
        f"{occurrence_literal}⟩"
    )


def _vector_source() -> str:
    declarations: list[str] = []
    for index, twin in enumerate(TWINS):
        declarations.extend(
            (
                f"def v{index}Pre : State := {_lean_state(twin.state)}",
                f"def v{index}Context : M.Context := {_lean_context(twin)}",
                f"def v{index}Command : M.Command := {_lean_command(twin.command)}",
            )
        )
    return "\n".join(declarations)


VECTOR_PREAMBLE = r"""
def observe (bytes : B.Bytes) : M.Root := toString bytes.length
def renderBytes (bytes : B.Bytes) : String :=
  String.intercalate "," (bytes.map (fun byte => toString byte.toNat))
def verdictName : Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => ManagedAssetFiniteOutcomeV2.RejectCode.code code
def emit (name : String) (result : Result) : IO Unit := do
  IO.println ("OUTCOME|" ++ name ++ "|" ++ verdictName result.verdict)
  IO.println ("POST|" ++ name ++ "|" ++ renderBytes (stateBytes result.post))
"""


def _parse_vector_report(output: str) -> tuple[dict[str, str], dict[str, bytes]]:
    outcomes: dict[str, str] = {}
    posts: dict[str, bytes] = {}
    for line in output.splitlines():
        if line.startswith("OUTCOME|"):
            _, name, verdict = line.split("|", 2)
            assert name not in outcomes
            outcomes[name] = verdict
        elif line.startswith("POST|"):
            _, name, raw = line.split("|", 2)
            assert name not in posts
            posts[name] = bytes(int(value) for value in raw.split(",") if value)
        elif line.strip():
            raise AssertionError(f"unexpected Lean report line: {line}")
    return outcomes, posts


def _python_outcome(twin: Twin) -> tuple[str, bytes]:
    from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
    from src.core.managed_asset_lifecycle_module_v2 import (
        transition_managed_asset_lifecycle_v2,
    )
    from src.core.managed_asset_lifecycle_result_v2 import ManagedAssetLifecycleAcceptedV2

    result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
    if isinstance(result, ManagedAssetLifecycleAcceptedV2):
        return "ACCEPTED", canonical_global_bytes_v2(result.post_state.to_canonical())
    assert result.effects.is_empty
    assert result.pre_state_root == result.post_state_root == twin.state.state_root
    return result.code.value, canonical_global_bytes_v2(twin.state.to_canonical())


def test_actual_finite_runtime_twins_match_verdict_and_whole_post_state_bytes(
    outcome_lean: LeanSubject,
) -> None:
    body = (
        VECTOR_PREAMBLE
        + _vector_source()
        + "\ndef runVectors : IO Unit := do\n"
        + "\n".join(
            f'  emit "{twin.name}" (transition observe v{index}Context v{index}Pre v{index}Command)'
            for index, twin in enumerate(TWINS)
        )
        + "\n#eval runVectors\n"
    )
    result = _consumer(outcome_lean, "ManagedFiniteOutcomeRuntimeVectors", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    outcomes, posts = _parse_vector_report(result.stdout)
    assert tuple(outcomes) == tuple(twin.name for twin in TWINS)
    assert tuple(posts) == tuple(twin.name for twin in TWINS)
    assert len(outcomes) == len(posts) == len(TWINS) == 37
    for twin in TWINS:
        verdict, post_bytes = _python_outcome(twin)
        assert outcomes[twin.name] == verdict, twin.name
        assert posts[twin.name] == post_bytes, twin.name
        if verdict != "ACCEPTED":
            assert post_bytes == canonical_state_bytes(twin.state)
        else:
            assert post_bytes != canonical_state_bytes(twin.state)


def canonical_state_bytes(state: ManagedAssetLifecycleStateV2) -> bytes:
    from src.core.global_settlement_types_v2 import canonical_global_bytes_v2

    return canonical_global_bytes_v2(state.to_canonical())
