"""Annotation mirrors of the completed V1 transfer: theorem consumers and runtime controls.

Obligation: the completed pre-state-policy transfer plan satisfies the full five-clause
``AnnotationMirrors`` relation exactly when the selected fee is zero or its owner differs
from the sender.  The Lean lane compiles the fresh Std-only closure, restates every public
theorem independently, checks axioms, and applies the actual theorems to nonempty admitted
witnesses (grade 4).  The runtime lane calls the public ``transition_asset_transfer_v1``
entry point and the unchanged ``_require_fee_mirror_v1`` checker on fixed vectors whose
expected outcome is derived from the submitted policy and command, never from runtime
output (grade 2 decision table).  An executable Lean model of the same checker decides the
identical plans (grade 3 differential model).  Constructed plans give an independent
semantic negative for prefix overflow whose final sum fits, coordinate controls, wrong-key
fee credits, zero fee rows and residue mapping.  A final-sum-only mutant checker is shown to
accept the prefix-overflow plan that both real checkers refuse.

Nonclaims: structural admission is separate from authentication and from the global
``Verified`` record; finite comparisons prove no universal Python/Rust/compiler refinement,
custody conservation closure, signature/profile/store authority, cryptographic receipt or
publisher qualification.  The reward-label control separately checks the full runtime's
unsupported-effect refusal; the standalone fee observer does not implement that guard.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass

import pytest

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
)
from src.core.global_economic_state_effect_refinement_v1 import (
    _require_fee_mirror_v1,
    _require_supported_effects_v1,
)
from src.core.global_settlement_types_v1 import (
    FEE_RESIDUE_CONTROL_DOMAIN_V1,
    FEE_RESIDUE_PRINCIPAL_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    AssetSupplyV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
)
from tests.formal.test_lean_asset_transfer_effect_plan_v1 import (
    _commitment_term,
    _complete_expected_view,
    _effect_rows_expected,
)
from tests.formal.test_lean_asset_transfer_effect_plan_v1 import (
    lean as effect_plan_subject,  # noqa: F401 -- fresh predecessor closure with E.
)
from tests.formal.test_lean_asset_transfer_policy_selection_v1 import (
    Case,
    _case,
    _input_term,
    _state_term,
)
from tests.formal.test_lean_asset_transfer_policy_selection_v1 import (
    lean as policy_selection_subject,  # noqa: F401 -- predecessor fixture chain.
)
from tests.formal.test_lean_asset_transfer_sparse_state_admission_v1 import (
    lean as state_admission_subject,  # noqa: F401 -- predecessor fixture chain.
)
from tests.formal.test_lean_asset_transfer_sparse_supply_v1 import (
    lean as supply_subject,  # noqa: F401 -- predecessor fixture chain.
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
)

MODULE = "AssetTransferAnnotationMirrorsV1"
NAMESPACE = f"Proofs.{MODULE}"
FEE_MIRROR_MODULE = "AssetTransferFeeMirrorEligibilityV1"
EFFECT_PLAN_NAMESPACE = "Proofs.AssetTransferEffectPlanV1"
POLICY_NAMESPACE = "Proofs.AssetTransferPolicySelectionV1"
UPPER = MAX_DELTA_ATOMS_V1
LOWER = MIN_DELTA_ATOMS_V1
MIRRORED = "MIRRORED"
NOT_MIRRORED = "economic refinement fee allocation is not mirrored"
AGGREGATE_OVERFLOW = "economic refinement fee mirror aggregate overflow"
ZERO_FEE_ROW = "economic refinement zero fee conservation row is non-canonical"
RESIDUE_MISMATCH = "economic refinement fee residue state mapping mismatch"
SIGNED_OVERFLOW = "EFFECT_DELTA_OVERFLOW"
OTHER_ASSET = {"USD": "EUR", "EUR": "USD"}

OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open {POLICY_NAMESPACE}
open {EFFECT_PLAN_NAMESPACE}
attribute [local instance] lexOrd
"""

# Public signatures restated independently of the proof source.  The contract test fails if
# the proof worker changes this surface without a matching consumer update.
THEOREM_TYPES = {
    "running_totals_fit_of_pairwise_zero":
        "∀ {α : Type} (contribution : α → Int) (rows : List α), (∀ row ∈ rows, FitsI128 (contribution row)) → rows.Pairwise (fun left right => contribution left = 0 ∨ contribution right = 0) → RunningTotalsFitI128 contribution rows 0",
    "projectedPlan_state_bearing_pairwise_zero":
        "∀ {input : S.Input}, (S.step input).verdict = .accepted → ∀ (owner asset domain : String), (S.projectedPlan input).rows.Pairwise (fun left right => stateBearingContribution owner asset domain left = 0 ∨ stateBearingContribution owner asset domain right = 0)",
    "empty_annotation_mirrors":
        "AnnotationMirrors EffectPlan.empty",
    "complete_rejected_annotation_mirrors":
        "∀ {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}, (K.step input).verdict = .rejected code → (complete fields input).plan = EffectPlan.empty ∧ AnnotationMirrors (complete fields input).plan",
    "complete_selected_annotation_mirrors_iff":
        "∀ {fields : CommitmentFields} {input : K.Input} {policy : T.Policy}, K.StateAdmitted input.pre → T.CommandWellFormed input.command → (K.step input).verdict = .accepted → K.policyFor input.pre.policies input.command.asset = some policy → (AnnotationMirrors (complete fields input).plan ↔ policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender)",
    "complete_accepted_unconditional_clauses":
        "∀ (fields : CommitmentFields) {input : K.Input}, K.StateAdmitted input.pre → (K.step input).verdict = .accepted → StateBearingAggregatesFitI128 (complete fields input).plan ∧ RewardSlashMirrored (complete fields input).plan ∧ FeeRowsCanonical (complete fields input).plan ∧ FeeResidueExact (complete fields input).plan",
    "complete_annotation_mirrors_iff":
        "∀ (fields : CommitmentFields) {input : K.Input}, K.StateAdmitted input.pre → T.CommandWellFormed input.command → (K.step input).verdict = .accepted → (AnnotationMirrors (complete fields input).plan ↔ ∃ policy, K.policyFor input.pre.policies input.command.asset = some policy ∧ (policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender))",
    "complete_positive_sender_fee_not_mirrored":
        "∀ {fields : CommitmentFields} {input : K.Input} {policy : T.Policy}, K.StateAdmitted input.pre → T.CommandWellFormed input.command → (K.step input).verdict = .accepted → K.policyFor input.pre.policies input.command.asset = some policy → 0 < policy.transferFeeAtoms → policy.feeOwner = input.command.sender → ¬ AnnotationMirrors (complete fields input).plan",
}

SOURCE_PINS = {
    "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean":
        "2ce254367dc8e8299f82f8a93e09c1d470f3a218ed01af7efb766946a34255a4",
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean":
        "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    "lean-mathlib/Proofs/AssetTransferRefinementV1.lean":
        "2d9ed7beb6feb47b67afa63a40d1203bcca9004b49ba978b9927edded6a04932",
    "lean-mathlib/Proofs/AssetTransferCustodyCompositionV1.lean":
        "37375e914576993767eae7484e620e54be300798785b2a57a9953e86be2f34d2",
    "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean":
        "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "lean-mathlib/Proofs/AssetTransferPolicySelectionV1.lean":
        "6c330fb920885223089d774eaf6110a3007bd2790a3c69dc947f80255edff321",
    "lean-mathlib/Proofs/AssetTransferEffectPlanV1.lean":
        "14cea53d90e1fdc6f068e581dcc8e737526475b323100c5d6c27b9354f769de9",
    "lean-mathlib/Proofs/AssetTransferFeeMirrorEligibilityV1.lean":
        "03ae7a9c1db3b8355fb2cd3f09206565cee524c3c735855a0af6c5287ecc5a10",
    "src/core/asset_transfer_module_v1.py":
        "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py":
        "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_settlement_types_v1.py":
        "854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4",
    "src/core/global_economic_state_effect_refinement_v1.py":
        "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
}

# Executable Lean model of the unchanged Python ``_require_fee_mirror_v1`` decision: an ordered
# fold of state-bearing rows by full physical key with an i128 check at every step, the fee
# credit comparison, the zero fee row check and the residue mapping.  It is a probe-local
# oracle and never a proof.
MIRROR_MODEL = r'''
abbrev PhysicalKey := String × String × String

def stateBearing : EffectKind → Bool
  | .accountMovement => true
  | .custody => true
  | .reserve => true
  | _ => false

def totalAt (totals : List (PhysicalKey × Int)) (key : PhysicalKey) : Int :=
  ((totals.find? fun entry => entry.1 == key).map (fun entry => entry.2)).getD 0

def foldStateBearing : List EconomicEffectRow → List (PhysicalKey × Int) →
    Option (List (PhysicalKey × Int))
  | [], totals => some totals
  | row :: rows, totals =>
      if stateBearing row.kind then
        let key : PhysicalKey := (row.principal, row.asset, row.custodyDomain)
        let total := totalAt totals key + row.deltaAtoms
        if minI128 ≤ total ∧ total ≤ maxI128 then
          foldStateBearing rows ((key, total) :: totals.filter fun entry => entry.1 != key)
        else none
      else foldStateBearing rows totals

def residueEffects (plan : EffectPlan) : List (String × Int) :=
  plan.rows.filterMap fun row =>
    if row.kind == .reserve ∧ row.principal == feeResiduePrincipal ∧
        row.custodyDomain == feeResidueAccountingLocation ∧ 0 < row.deltaAtoms then
      some (row.asset, row.deltaAtoms)
    else none

def expectedResidue (plan : EffectPlan) : List (String × Int) :=
  plan.feeConservation.filterMap fun row =>
    if 0 < row.carriedResidueAtoms then some (row.asset, row.carriedResidueAtoms) else none

def mirrorVerdict (plan : EffectPlan) : String :=
  match foldStateBearing plan.rows [] with
  | none => "economic refinement fee mirror aggregate overflow"
  | some totals =>
      if plan.rows.any fun row =>
          row.kind == .feeAllocation ∧
            totalAt totals (row.principal, row.asset, row.custodyDomain) < row.deltaAtoms then
        "economic refinement fee allocation is not mirrored"
      else if plan.feeConservation.any fun row => row.feeChargedAtoms == 0 then
        "economic refinement zero fee conservation row is non-canonical"
      else if residueEffects plan != expectedResidue plan then
        "economic refinement fee residue state mapping mismatch"
      else "MIRRORED"

/-- Mutant checker: only final totals are checked.  It wrongly accepts prefix overflow. -/
def finalTotalsOnlyVerdict (plan : EffectPlan) : String :=
  if plan.rows.all fun row =>
      let total := stateBearingEffectFor plan row.principal row.asset row.custodyDomain
      decide (minI128 ≤ total ∧ total ≤ maxI128) then "MIRRORED"
  else "economic refinement fee mirror aggregate overflow"

def verdictCode : T.Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def effectRowsView (rows : List EconomicEffectRow) : List (List String) :=
  rows.map fun row =>
    [row.kind.code, row.principal, row.asset, row.custodyDomain, toString row.deltaAtoms]

/-- The theorem's right-hand side, decided on the actual first-match selected row. -/
def selectedEligibility (input : Input) : String :=
  match policyFor input.pre.policies input.command.asset with
  | some policy =>
      toString (decide (policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender))
  | none => "none"

def observeMirror (fields : CommitmentFields) (input : Input) : List (List String) :=
  let out := complete fields input
  [[verdictCode out.verdict], [mirrorVerdict out.plan], [selectedEligibility input]] ++
    effectRowsView out.plan.rows
'''


@pytest.fixture(scope="module")
def lean(effect_plan_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Compile the fee-eligibility dependency and the new proof in the fresh closure."""
    for name in (FEE_MIRROR_MODULE, MODULE):
        captured = effect_plan_subject.source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        imports = re.findall(r"^import (\S+)", captured.read_text(), re.MULTILINE)
        assert all(item.startswith("Proofs.") for item in imports), imports
        result = _compile(
            effect_plan_subject,
            captured,
            effect_plan_subject.library / "Proofs" / f"{name}.olean",
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return effect_plan_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _decode(output: str) -> list[list[list[str]]]:
    return [json.loads(json.loads(line)) for line in output.splitlines()]


def test_contract_axioms_placeholders_and_source_pins(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(THEOREM_TYPES)
    assert (PROJECT / "Proofs.lean").read_text().splitlines().count(f"import {NAMESPACE}") == 1
    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n"
        f"#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    report = " ".join(_probe(lean, "AnnotationMirrorConsumers", consumers).split())
    for name in THEOREM_TYPES:
        found = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
            report,
        )
        assert found, (name, report)
        axioms = {item.strip() for item in (found.group(1) or "").split(",") if item.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)
    for path, digest in SOURCE_PINS.items():
        assert hashlib.sha256((PROJECT.parent / path).read_bytes()).hexdigest() == digest, path


@dataclass(frozen=True)
class MirrorCase:
    """One runtime vector; ``expected`` is a fixed decision-table entry."""

    name: str
    owner: str
    fee: int
    amount: int
    expected: str
    asset: str = "USD"
    other_owner: str = "other_treasury"


# Sender/recipient/distinct aliases at zero, one atom and i128 boundaries, with a second
# asset whose own fee owner never influences the selected asset.  Each accepted boundary has
# an adjacent EFFECT_DELTA_OVERFLOW neighbour.
MIRROR_CASES = (
    MirrorCase("zero_fee_sender_owner", "alice", 0, 1, MIRRORED),
    MirrorCase("zero_fee_recipient_owner", "bob", 0, 1, MIRRORED),
    MirrorCase("zero_fee_distinct_owner", "treasury", 0, 1, MIRRORED),
    MirrorCase("one_atom_fee_sender_owner", "alice", 1, 1, NOT_MIRRORED),
    MirrorCase("one_atom_fee_recipient_owner", "bob", 1, 1, MIRRORED),
    MirrorCase("one_atom_fee_distinct_owner", "treasury", 1, 1, MIRRORED),
    MirrorCase("sender_owner_max_pair", "alice", UPPER, UPPER, NOT_MIRRORED),
    MirrorCase("distinct_owner_max_fee_min_debit", "treasury", UPPER, 1, MIRRORED),
    MirrorCase("distinct_owner_max_amount_min_fee", "treasury", 1, UPPER, MIRRORED),
    MirrorCase("recipient_owner_max_credit", "bob", UPPER - 1, 1, MIRRORED),
    MirrorCase("zero_fee_max_amount", "treasury", 0, UPPER, MIRRORED),
    MirrorCase("sender_owner_fee_overflow_neighbor", "alice", UPPER + 1, 1, SIGNED_OVERFLOW),
    MirrorCase("distinct_owner_debit_overflow_neighbor", "treasury", UPPER, 2, SIGNED_OVERFLOW),
    MirrorCase("recipient_owner_credit_overflow_neighbor", "bob", 1, UPPER, SIGNED_OVERFLOW),
    MirrorCase("zero_fee_amount_overflow_neighbor", "treasury", 0, UPPER + 1, SIGNED_OVERFLOW),
    MirrorCase("eur_sender_owner_refused", "alice", 2, 3, NOT_MIRRORED, asset="EUR"),
    MirrorCase("eur_distinct_owner_with_usd_sender_owner", "eur_treasury", 2, 3, MIRRORED,
               asset="EUR", other_owner="alice"),
    MirrorCase("usd_distinct_owner_with_eur_sender_owner", "treasury", 1, 4, MIRRORED,
               other_owner="alice"),
)


def _expected_from_inputs(case: MirrorCase) -> str:
    """Derive the decision from the submitted policy and command, never from runtime output."""
    events = (("alice", -case.amount - case.fee), ("bob", case.amount), (case.owner, case.fee))
    deltas = {owner: sum(delta for who, delta in events if who == owner) for owner, _ in events}
    if case.fee > UPPER or any(not LOWER <= delta <= UPPER for delta in deltas.values()):
        return SIGNED_OVERFLOW
    return MIRRORED if case.fee == 0 or case.owner != "alice" else NOT_MIRRORED


def _runtime_case(case: MirrorCase) -> Case:
    other = OTHER_ASSET[case.asset]
    other_fee = 2 if other == "EUR" else 1
    policies = tuple(sorted(
        (
            AssetTransferPolicyV1(case.asset, case.owner, case.fee, True),
            AssetTransferPolicyV1(other, case.other_owner, other_fee, True),
        ),
        key=lambda policy: policy.asset,
    ))
    balance = case.amount + case.fee
    supplies = tuple(sorted(
        (AssetSupplyV1(case.asset, balance), AssetSupplyV1(other, 45)),
        key=lambda supply: supply.asset,
    ))
    return _case(
        case.name,
        policies=policies,
        rows=(("alice", case.asset, balance), ("alice", other, 40), ("bob", other, 5)),
        supplies=supplies,
        asset=case.asset,
        amount=case.amount,
        max_fee=case.fee,
        error=SIGNED_OVERFLOW if case.expected == SIGNED_OVERFLOW else None,
    )


def _runtime_observation(case: MirrorCase) -> tuple[list[list[str]], Case, object]:
    assert _expected_from_inputs(case) == case.expected, case.name
    runtime = _runtime_case(case)
    view, result = _complete_expected_view(runtime)
    # The public entry point is called directly; the shared six-field view is deterministic.
    direct = transition_asset_transfer_v1(runtime.context, runtime.pre, runtime.command)
    assert type(direct) is type(result) and asdict(direct) == asdict(result)
    policy = next(policy for policy in runtime.pre.policies if policy.asset == case.asset)
    assert (policy.fee_owner, policy.transfer_fee_atoms) == (case.owner, case.fee)
    eligibility = str(case.fee == 0 or case.owner != runtime.command.sender).lower()
    if case.expected == SIGNED_OVERFLOW:
        assert isinstance(result, AssetTransferRejectedV1)
        assert result.effects == GlobalEconomicEffectPlanV1.empty()
        _require_fee_mirror_v1(result.effects)
        return [[SIGNED_OVERFLOW], [MIRRORED], [eligibility]], runtime, result
    assert isinstance(result, AssetTransferAcceptedV1)
    before = asdict(result.effects)
    if case.expected == NOT_MIRRORED:
        with pytest.raises(ValueError) as refusal:
            _require_fee_mirror_v1(result.effects)
        assert str(refusal.value) == NOT_MIRRORED
    else:
        _require_fee_mirror_v1(result.effects)
    assert asdict(result.effects) == before
    assert eligibility == str(case.expected == MIRRORED).lower()
    rows = _effect_rows_expected(runtime, policy)
    assert view[view.index(["ROWS"]) + 1:view.index(["ASSET_CONSERVATION"])] == rows
    return [["ACCEPTED"], [case.expected], [eligibility], *rows], runtime, result


def test_runtime_aliases_widths_and_second_asset_match_lean_model_and_theorem_rhs(
    lean: LeanSubject,
) -> None:
    observations = [_runtime_observation(case) for case in MIRROR_CASES]
    assert sorted({case.expected for case in MIRROR_CASES}) == sorted(
        {MIRRORED, NOT_MIRRORED, SIGNED_OVERFLOW}
    )
    probes = "\n".join(
        f"#eval IO.println (reprStr (reprStr (observeMirror ({_commitment_term(runtime, result)}) "
        f"({_input_term(runtime)} : {POLICY_NAMESPACE}.Input))))"
        for _, runtime, result in observations
    )
    decoded = _decode(_probe(lean, "AnnotationMirrorRuntimeCorpus", MIRROR_MODEL + probes))
    assert decoded == [expected for expected, _, _ in observations]
    # Finite instance of the theorem: for accepted plans the checker outcome, the executable
    # model and the decided right-hand side agree on every vector.
    for expected, _, _ in observations:
        if expected[0] == ["ACCEPTED"]:
            assert (expected[1] == [MIRRORED]) == (expected[2] == ["true"])


@dataclass(frozen=True)
class PlanControl:
    name: str
    rows: tuple[EconomicEffectRowV1, ...]
    fees: tuple[FeeConservationRowV1, ...]
    expected: str


def _row(kind: EconomicEffectKindV1, principal: str, asset: str, domain: str,
         delta: int) -> EconomicEffectRowV1:
    return EconomicEffectRowV1(kind, principal, asset, domain, delta)


MOVE, CUSTODY, RESERVE = (
    EconomicEffectKindV1.ACCOUNT_MOVEMENT, EconomicEffectKindV1.CUSTODY,
    EconomicEffectKindV1.RESERVE,
)
FEE, REWARD = EconomicEffectKindV1.FEE_ALLOCATION, EconomicEffectKindV1.REWARD
PREFIX_ROWS = (
    _row(MOVE, "alice", "USD", "accounts", UPPER),
    _row(CUSTODY, "alice", "USD", "accounts", 1),
    _row(RESERVE, "alice", "USD", "accounts", -1),
)
CREDIT_FEES = (FeeConservationRowV1("USD", 1, 1, 0),)
RESIDUE_FEES = (FeeConservationRowV1("USD", 2, 1, 1),)
PLAN_CONTROLS = (
    PlanControl("empty_plan", (), (), MIRRORED),
    PlanControl("prefix_overflow_final_sum_fits", PREFIX_ROWS, (), AGGREGATE_OVERFLOW),
    PlanControl("other_principal_prevents_false_overflow", (
        PREFIX_ROWS[0], _row(CUSTODY, "other", "USD", "accounts", 1), PREFIX_ROWS[2]), (),
        MIRRORED),
    PlanControl("other_asset_prevents_false_overflow", (
        PREFIX_ROWS[0], _row(CUSTODY, "alice", "EUR", "accounts", 1), PREFIX_ROWS[2]), (),
        MIRRORED),
    PlanControl("other_domain_prevents_false_overflow", (
        PREFIX_ROWS[0], _row(CUSTODY, "alice", "USD", "other", 1), PREFIX_ROWS[2]), (),
        MIRRORED),
    PlanControl("credit_exact", (
        _row(MOVE, "treasury", "USD", "accounts", 1), _row(FEE, "treasury", "USD", "accounts", 1)),
        CREDIT_FEES, MIRRORED),
    PlanControl("credit_short_by_one_atom", (
        _row(MOVE, "treasury", "USD", "accounts", 1), _row(FEE, "treasury", "USD", "accounts", 2)),
        (FeeConservationRowV1("USD", 2, 2, 0),), NOT_MIRRORED),
    PlanControl("credit_wrong_principal", (
        _row(MOVE, "other", "USD", "accounts", 1), _row(FEE, "treasury", "USD", "accounts", 1)),
        CREDIT_FEES, NOT_MIRRORED),
    PlanControl("credit_wrong_asset", (
        _row(MOVE, "treasury", "EUR", "accounts", 1), _row(FEE, "treasury", "USD", "accounts", 1)),
        CREDIT_FEES, NOT_MIRRORED),
    PlanControl("credit_wrong_domain", (
        _row(MOVE, "treasury", "USD", "other", 1), _row(FEE, "treasury", "USD", "accounts", 1)),
        CREDIT_FEES, NOT_MIRRORED),
    PlanControl("zero_fee_row_non_canonical", (_row(MOVE, "alice", "USD", "accounts", 1),),
                (FeeConservationRowV1("USD", 0, 0, 0),), ZERO_FEE_ROW),
    PlanControl("residue_matched", (
        _row(MOVE, "treasury", "USD", "accounts", 1), _row(FEE, "treasury", "USD", "accounts", 1),
        _row(RESERVE, FEE_RESIDUE_PRINCIPAL_V1, "USD", FEE_RESIDUE_CONTROL_DOMAIN_V1, 1)),
        RESIDUE_FEES, MIRRORED),
    PlanControl("residue_missing", (
        _row(MOVE, "treasury", "USD", "accounts", 1), _row(FEE, "treasury", "USD", "accounts", 1)),
        RESIDUE_FEES, RESIDUE_MISMATCH),
    PlanControl("reward_row_outside_transfer_shape", (_row(REWARD, "alice", "USD", "accounts", 1),),
                (), MIRRORED),
)
KINDS = {MOVE: "accountMovement", CUSTODY: "custody", RESERVE: "reserve",
         FEE: "feeAllocation", REWARD: "reward"}


def _plan(control: PlanControl) -> GlobalEconomicEffectPlanV1:
    return GlobalEconomicEffectPlanV1(control.rows, (), control.fees, (), (), ())


def _python_verdict(plan: GlobalEconomicEffectPlanV1) -> str:
    before = asdict(plan)
    try:
        _require_fee_mirror_v1(plan)
        verdict = MIRRORED
    except ValueError as error:
        verdict = str(error)
    assert asdict(plan) == before
    return verdict


def _final_totals_only_mutant(plan: GlobalEconomicEffectPlanV1) -> str:
    """Mutant checker that inspects only final aggregates; killed by the prefix control."""
    totals: dict[tuple[str, str, str], int] = {}
    for row in plan.rows:
        if row.kind in {MOVE, CUSTODY, RESERVE}:
            key = (row.principal, row.asset, row.custody_domain)
            totals[key] = totals.get(key, 0) + row.delta_atoms
    if all(LOWER <= total <= UPPER for total in totals.values()):
        return MIRRORED
    return AGGREGATE_OVERFLOW


def _plan_term(control: PlanControl) -> str:
    rows = ", ".join(
        f"⟨.{KINDS[row.kind]}, {json.dumps(row.principal)}, {json.dumps(row.asset)}, "
        f"{json.dumps(row.custody_domain)}, ({row.delta_atoms} : Int)⟩"
        for row in control.rows
    )
    fees = ", ".join(
        f"⟨{json.dumps(fee.asset)}, ({fee.fee_charged_atoms} : Int), "
        f"({fee.current_allocations_atoms} : Int), ({fee.carried_residue_atoms} : Int)⟩"
        for fee in control.fees
    )
    return f"{{ EffectPlan.empty with rows := [{rows}], feeConservation := [{fees}] }}"


def test_constructed_plans_prefix_overflow_coordinates_and_residue_match_lean_model(
    lean: LeanSubject,
) -> None:
    expected = []
    for control in PLAN_CONTROLS:
        plan = _plan(control)
        assert _python_verdict(plan) == control.expected, control.name
        expected.append([[control.name], [control.expected]])
    prefix = _plan(PLAN_CONTROLS[1])
    final_totals = {
        key: sum(row.delta_atoms for row in prefix.rows
                 if (row.principal, row.asset, row.custody_domain) == key)
        for key in {(row.principal, row.asset, row.custody_domain) for row in prefix.rows}
    }
    assert final_totals == {("alice", "USD", "accounts"): UPPER}
    assert all(LOWER <= row.delta_atoms <= UPPER for row in prefix.rows)
    assert _final_totals_only_mutant(prefix) == MIRRORED
    assert _python_verdict(prefix) == AGGREGATE_OVERFLOW
    # The fee-only observer accepts this orphan label. The full runtime's supported-effect
    # guard refuses it, and the Lean control below refutes the full annotation relation.
    reward_control = PLAN_CONTROLS[13]
    assert reward_control.name == "reward_row_outside_transfer_shape"
    reward_plan = _plan(reward_control)
    assert _python_verdict(reward_plan) == MIRRORED
    reward_before = asdict(reward_plan)
    with pytest.raises(ValueError) as unsupported:
        _require_supported_effects_v1(reward_plan)
    assert str(unsupported.value) == "economic refinement reward and slash labels are unmapped"
    assert asdict(reward_plan) == reward_before
    probes = "\n".join(
        f"def control{index} : EffectPlan := {_plan_term(control)}\n"
        f"#eval IO.println (reprStr (reprStr [[{json.dumps(control.name)}], "
        f"[mirrorVerdict control{index}]]))"
        for index, control in enumerate(PLAN_CONTROLS)
    )
    body = MIRROR_MODEL + probes + r'''
#eval IO.println (reprStr (reprStr [["MUTANT"], [finalTotalsOnlyVerdict control1]]))

/-- Independent semantic negative: each row and the final sum fit i128, yet the ordered
state-bearing subtotal at the physical key `("alice", "USD", "accounts")` leaves i128. -/
example : ∀ row ∈ control1.rows, FitsI128 row.deltaAtoms := by
  intro row member
  simp [control1, EffectPlan.empty] at member
  rcases member with rfl | rfl | rfl <;> simp [FitsI128, minI128, maxI128]

example : FitsI128 (stateBearingEffectFor control1 "alice" "USD" "accounts") := by
  simp [FitsI128, minI128, maxI128, stateBearingEffectFor, effectFor, control1, EffectPlan.empty]

example : ¬ StateBearingAggregatesFitI128 control1 := by
  intro fits
  have key := fits "alice" "USD" "accounts"
  simp [RunningTotalsFitI128, stateBearingContribution, control1, EffectPlan.empty,
    FitsI128, minI128, maxI128] at key

/-- The bridge premise fails here: two nonzero contributions share one physical key. -/
example : ¬ control1.rows.Pairwise (fun left right =>
    stateBearingContribution "alice" "USD" "accounts" left = 0 ∨
      stateBearingContribution "alice" "USD" "accounts" right = 0) := by
  decide

example : ¬ FeeAllocationCreditsMirrored control9 := by
  unfold FeeAllocationCreditsMirrored
  decide

example : ¬ FeeRowsCanonical control10 := by
  unfold FeeRowsCanonical
  decide

theorem orphan_reward_not_mirrored : ¬ RewardSlashMirrored control13 := by
  unfold RewardSlashMirrored
  decide

example : ¬ AnnotationMirrors control13 := by
  intro mirrors
  exact orphan_reward_not_mirrored mirrors.2.2.1
'''
    decoded = _decode(_probe(lean, "AnnotationMirrorPlanControls", body))
    assert decoded == [*expected, [["MUTANT"], [MIRRORED]]]
    assert PLAN_CONTROLS[9].name == "credit_wrong_domain"
    assert PLAN_CONTROLS[10].name == "zero_fee_row_non_canonical"


def _admission_proof(theorem: str, state: str, case: Case) -> str:
    balance_arms = " | ".join(["rfl"] * len(case.pre.balances))
    policy_arms = " | ".join(["rfl"] * len(case.pre.policies))
    supply_arms = " | ".join(["rfl"] * len(case.pre.supplies))
    assets = [supply.asset for supply in case.pre.supplies]
    coverage = ""
    names = []
    for index, asset in enumerate(assets):
        pad = "  " * (index + 2)
        lead = pad if index == 0 else ""
        names.append(f"asset{index}")
        coverage += (
            f"{lead}by_cases asset{index} : {json.dumps(asset)} = queried\n"
            f"{pad}· subst queried\n{pad}  decide\n{pad}· "
        )
    coverage += f"simp [{state}, amountForAsset, supplyFor, {', '.join(names)}]\n"
    return f"""
theorem {theorem} : StateAdmitted {state} := by
  refine ⟨?_, ?_, ?_, by decide, ?_⟩
  · unfold S.CanonicalBalances
    refine ⟨?_, ?_, by decide, ?_⟩
    · unfold S.Unique
      decide
    · intro row member
      simp [{state}] at member
      rcases member with {balance_arms} <;> decide
    · decide
  · unfold PoliciesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro candidate member
    simp [{state}] at member
    rcases member with {policy_arms} <;> decide
  · unfold SuppliesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro supply member
    simp [{state}] at member
    rcases member with {supply_arms} <;> decide
  · intro queried
{coverage}"""


def _witness_case(name: str, usd_owner: str, *, asset: str = "USD",
                  error: str | None = None) -> Case:
    policies = (
        AssetTransferPolicyV1("EUR", "eur_treasury", 2, True),
        AssetTransferPolicyV1("USD", usd_owner, 1, True),
    )
    return _case(
        name,
        policies=policies,
        rows=(("alice", "EUR", 9), ("alice", "USD", 40), ("bob", "USD", 5)),
        supplies=(AssetSupplyV1("EUR", 9), AssetSupplyV1("USD", 45)),
        asset=asset,
        amount=4,
        max_fee=1,
        error=error,
    )


def test_nonempty_admitted_witnesses_apply_the_actual_theorems(lean: LeanSubject) -> None:
    distinct = _witness_case("distinct_owner", "treasury")
    sender = _witness_case("sender_owner", "alice")
    rejected = _witness_case("rejected", "treasury", asset="GBP", error="UNKNOWN_ASSET")
    expected = []
    for case in (distinct, sender):
        view, result = _complete_expected_view(case)
        assert isinstance(result, AssetTransferAcceptedV1)
        policy = next(policy for policy in case.pre.policies if policy.asset == "USD")
        expected.append(_effect_rows_expected(case, policy))
    rejected_view, rejected_result = _complete_expected_view(rejected)
    assert isinstance(rejected_result, AssetTransferRejectedV1)
    assert rejected_view[0] == ["VERDICT", "UNKNOWN_ASSET"]
    assert _python_verdict(rejected_result.effects) == MIRRORED
    body = f"""
namespace AnnotationWitness

def distinctState : State := {_state_term(distinct)}
def senderState : State := {_state_term(sender)}
def usdPolicy : T.Policy := ⟨"USD", "treasury", (1 : Int), true⟩
def senderPolicy : T.Policy := ⟨"USD", "alice", (1 : Int), true⟩
def distinctInput : Input := {_input_term(distinct)}
def senderInput : Input := {_input_term(sender)}
def rejectedInput : Input := {_input_term(rejected)}
def fields : CommitmentFields := ⟨"opaque-pre", "opaque-post", "opaque-occurrence"⟩
{_admission_proof("distinct_admitted", "distinctState", distinct)}
{_admission_proof("sender_admitted", "senderState", sender)}
theorem distinct_pre : distinctInput.pre = distinctState := rfl
theorem sender_pre : senderInput.pre = senderState := rfl

example : T.CommandWellFormed distinctInput.command := ⟨by decide, by decide⟩
example : (K.step distinctInput).verdict = .accepted := by decide
example : (K.step senderInput).verdict = .accepted := by decide
example : (K.step rejectedInput).verdict = .rejected .unknownAsset := by decide

theorem distinct_selection :
    K.policyFor distinctInput.pre.policies distinctInput.command.asset = some usdPolicy := by
  simp [distinctInput, usdPolicy, K.policyFor]

theorem sender_selection :
    K.policyFor senderInput.pre.policies senderInput.command.asset = some senderPolicy := by
  simp [senderInput, senderPolicy, K.policyFor]

/-- The full five-clause relation, obtained through the front door with no caller selection. -/
theorem distinct_mirrored : AnnotationMirrors (complete fields distinctInput).plan :=
  ({NAMESPACE}.complete_annotation_mirrors_iff fields (distinct_pre ▸ distinct_admitted)
    ⟨by decide, by decide⟩ (by decide)).mpr ⟨usdPolicy, distinct_selection, Or.inr (by decide)⟩

/-- Positive sender fee: leaf accepted, global relation refuted. -/
theorem sender_not_mirrored : ¬ AnnotationMirrors (complete fields senderInput).plan :=
  {NAMESPACE}.complete_positive_sender_fee_not_mirrored (sender_pre ▸ sender_admitted)
    ⟨by decide, by decide⟩ (by decide) sender_selection (by decide) rfl

/-- The sender-fee plan still satisfies the four alias-independent clauses. -/
theorem sender_unconditional :
    StateBearingAggregatesFitI128 (complete fields senderInput).plan ∧
      RewardSlashMirrored (complete fields senderInput).plan ∧
      FeeRowsCanonical (complete fields senderInput).plan ∧
      FeeResidueExact (complete fields senderInput).plan :=
  {NAMESPACE}.complete_accepted_unconditional_clauses fields (sender_pre ▸ sender_admitted)
    (by decide)

theorem sender_credit_clause_fails :
    ¬ FeeAllocationCreditsMirrored (complete fields senderInput).plan := by
  intro credits
  exact sender_not_mirrored ⟨sender_unconditional.1, credits, sender_unconditional.2.1,
    sender_unconditional.2.2.1, sender_unconditional.2.2.2⟩

theorem rejected_mirrored :
    (complete fields rejectedInput).plan = EffectPlan.empty ∧
      AnnotationMirrors (complete fields rejectedInput).plan :=
  {NAMESPACE}.complete_rejected_annotation_mirrors (code := .unknownAsset) (by decide)

#eval IO.println (reprStr (reprStr (effectRowsView (complete fields distinctInput).plan.rows)))
#eval IO.println (reprStr (reprStr (effectRowsView (complete fields senderInput).plan.rows)))
#eval IO.println (reprStr (reprStr (effectRowsView (complete fields rejectedInput).plan.rows)))
#eval IO.println (reprStr (reprStr [[mirrorVerdict (complete fields distinctInput).plan],
  [mirrorVerdict (complete fields senderInput).plan],
  [mirrorVerdict (complete fields rejectedInput).plan]]))

end AnnotationWitness
"""
    decoded = _decode(_probe(lean, "AnnotationMirrorWitness", MIRROR_MODEL + body))
    assert decoded == [*expected, [], [[MIRRORED], [NOT_MIRRORED], [MIRRORED]]]
    assert len(expected[0]) == 4 and len(expected[1]) == 3


def test_unconditional_acceptance_mutant_is_refuted_by_sender_witness(lean: LeanSubject) -> None:
    sender = _witness_case("sender_owner_mutant", "alice")
    _, result = _complete_expected_view(sender)
    assert isinstance(result, AssetTransferAcceptedV1)
    assert _python_verdict(result.effects) == NOT_MIRRORED
    condition = ("def predictedMirrored (input : Input) : Bool :=\n"
                 "  selectedEligibility input == \"true\"")
    body = MIRROR_MODEL + f"""
def senderInput : Input := {_input_term(sender)}
{condition}
example : (K.step senderInput).verdict = .accepted := by decide
example : predictedMirrored senderInput = false := by decide
"""
    assert _probe(lean, "AnnotationMirrorPrediction", body) == ""
    # A model-only mutant predicting unconditional mirroring fails the same negative consumer.
    mutant = body.replace(condition, "def predictedMirrored (_input : Input) : Bool := true")
    assert mutant != body
    path = lean.source / "AnnotationMirrorPredictionMutant.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + mutant)
    outcome = _compile(lean, path)
    assert outcome.returncode != 0
    assert outcome.stdout.count("error:") == 1, outcome.stdout + outcome.stderr
    assert "unexpected token" not in outcome.stdout
    assert ("Tactic `decide` proved that the proposition\n"
            "  predictedMirrored senderInput = false\nis false") in outcome.stdout
