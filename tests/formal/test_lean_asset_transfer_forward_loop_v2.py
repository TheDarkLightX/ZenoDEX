"""Retained finite checks for the frozen V2 transfer forward-row loop.

The test pins the reviewed Lean source, consumes its public theorem surface,
and compares bounded current-runtime observations with direct Lean evaluation.
It covers finite row execution only.  It does not claim parser, serializer,
hash, journal, coordinator, general repeated-delta, or production refinement.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import os
import re
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v2 import (
    _post_balances,
    _prepare_transfer,
    transition_asset_transfer_v2,
)
from src.core.asset_transfer_types_v2 import (
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
    AssetTransferStateV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
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
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "AssetTransferForwardLoopV2"
NAMESPACE = f"Proofs.{MODULE}"
REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE = REPO_ROOT / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "f90cf6c80f327f86b9542b0db93dad98cee8a3409b9a579c6120ea1bd349c53d"

ROOT = "0x" + "1" * 64
ORIGIN = "0x" + "2" * 64
GLOBAL = "0x" + "3" * 64
U128 = 2**128 - 1

OPEN_PREAMBLE = f"""open Proofs
open Proofs.AssetTransferFiniteOutcomeV2
open Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1
open {NAMESPACE}
attribute [local instance] lexOrd
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
"""
PREAMBLE = f"import {NAMESPACE}\n{OPEN_PREAMBLE}"

THEOREM_NAMES = (
    "put_lookup",
    "put_positive",
    "checkedPut_spec",
    "initialScan_congr",
    "initialScan_none_iff",
    "forwardRaw_error",
    "forwardRaw_spec",
    "row_eq_of_key_amount",
    "member_of_lookup",
    "rows_perm_of_lookup",
    "tail_ordered",
    "forward_eq_scan_tail",
    "project_scan",
    "selected_forward_eq",
    "operationalCandidate_eq",
    "finite_accepts_iff_forward",
    "finite_resource_reject_iff_forward",
    "finite_accepted_forward_post",
    "forward_error_rejects_noop",
    "finite_economic_reject_iff_forward",
)

# These ascriptions make every reviewed theorem signature part of the retained
# source closure.  The separate axiom probe below covers the same full surface.
THEOREM_TYPES = {
    "put_lookup": """∀ (rows : List AmountRow) (asset owner : String) (amount : Int)
      (_ : S.Unique rows) (queryAsset queryOwner : String),
      C.lookupLast (S.accountKey queryAsset queryOwner)
          (S.putAmount (S.accountKey asset owner) amount rows) =
        if asset = queryAsset ∧ owner = queryOwner then amount
        else C.lookupLast (S.accountKey queryAsset queryOwner) rows""",
    "put_positive": """∀ (rows : List AmountRow) (asset owner : String) (amount : Int),
      S.PositiveAccounts rows → T.IsU128 amount →
        S.PositiveAccounts (S.putAmount (S.accountKey asset owner) amount rows)""",
    "checkedPut_spec": """∀ {rows out : List AmountRow} {asset owner : String} {delta : Int},
      checkedPut rows asset owner delta = .ok out →
        out = S.putAmount (S.accountKey asset owner)
            (C.lookupLast (S.accountKey asset owner) rows + delta) rows ∧
          T.IsU128 (C.lookupLast (S.accountKey asset owner) rows + delta)""",
    "initialScan_congr": """∀ (left right : List AmountRow) (asset : String)
      (delta : String → Int) (roles : List String),
      (∀ owner ∈ roles, C.lookupLast (S.accountKey asset owner) left =
        C.lookupLast (S.accountKey asset owner) right) →
        initialScan left asset delta roles = initialScan right asset delta roles""",
    "initialScan_none_iff": """∀ (rows : List AmountRow) (asset : String)
      (delta : String → Int) (roles : List String),
      initialScan rows asset delta roles = none ↔
        ∀ owner ∈ roles,
          T.IsU128 (C.lookupLast (S.accountKey asset owner) rows + delta owner)""",
    "forwardRaw_error": """∀ (rows : List AmountRow) (asset : String)
      (delta : String → Int) (roles : List String),
      S.Unique rows → roles.Nodup →
        errorCode (forwardRaw rows asset delta roles) = initialScan rows asset delta roles""",
    "forwardRaw_spec": """∀ {rows out : List AmountRow} {asset : String}
      {delta : String → Int} {roles : List String},
      S.Unique rows → S.PositiveAccounts rows → roles.Nodup →
      forwardRaw rows asset delta roles = .ok out →
        S.Unique out ∧ S.PositiveAccounts out ∧
          ∀ queryAsset queryOwner,
            C.lookupLast (S.accountKey queryAsset queryOwner) out =
              C.lookupLast (S.accountKey queryAsset queryOwner) rows +
                (if asset = queryAsset ∧ queryOwner ∈ roles then delta queryOwner else 0)""",
    "row_eq_of_key_amount": """∀ {left right : AmountRow},
      C.amountKey left = C.amountKey right → left.amountAtoms = right.amountAtoms → left = right""",
    "member_of_lookup": """∀ (rows : List AmountRow) (row : AmountRow),
      S.Unique rows → row.custodyDomain = S.accounts → row.amountAtoms ≠ 0 →
      C.lookupLast (S.accountKey row.asset row.owner) rows = row.amountAtoms → row ∈ rows""",
    "rows_perm_of_lookup": """∀ (left right : List AmountRow),
      S.Unique left → S.Unique right → S.PositiveAccounts left → S.PositiveAccounts right →
      (∀ asset owner, C.lookupLast (S.accountKey asset owner) left =
        C.lookupLast (S.accountKey asset owner) right) → left.Perm right""",
    "tail_ordered": """∀ (rows : List AmountRow) (asset : String)
      (delta : String → Int) (roles : List String),
      Ordered rows → Ordered (F.updateRoles rows asset delta roles)""",
    "forward_eq_scan_tail": """∀ (rows : List AmountRow) (asset : String)
      (delta : String → Int) (roles : List String),
      S.Unique rows → S.PositiveAccounts rows → Ordered rows → roles.Nodup →
        forward rows asset delta roles =
          match initialScan rows asset delta roles with
          | some code => .error code
          | none => .ok (F.updateRoles rows asset delta roles)""",
    "project_scan": """∀ (release : String) (policy : T.Policy) (rows : List AmountRow)
      (supply : Int) (command : T.Command) (roles : List String),
      initialScan rows policy.asset (T.delta (F.project release policy rows supply) command) roles =
        T.balanceCodeOn (F.project release policy rows supply) command roles""",
    "selected_forward_eq": """∀ (release : String) (policy : T.Policy) (rows : List AmountRow)
      (supply : Int) (command : T.Command),
      S.Unique rows → S.PositiveAccounts rows → Ordered rows →
      command.asset = policy.asset → command.sender ≠ command.recipient →
        forward rows command.asset (T.delta (F.project release policy rows supply) command)
            (T.orderedRoles (F.project release policy rows supply) command) =
          match T.balanceCodeOn (F.project release policy rows supply) command
              (T.orderedRoles (F.project release policy rows supply) command) with
          | some code => .error code
          | none => .ok (F.transferRows (F.project release policy rows supply) command rows)""",
    "operationalCandidate_eq": """∀ (ctx : T.Context) (pre : O.State) (command : T.Command),
      O.Structural pre →
        operationalCandidate ctx pre command =
          match O.economicRejectCode ctx pre command with
          | some code => .error code
          | none => .ok (O.candidate pre command)""",
    "finite_accepts_iff_forward": """∀ (digest : Proofs.AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
      (ctx : T.Context) (pre : O.State) (command : T.Command),
      O.Structural pre →
        ((O.transition digest ctx pre command).verdict = .accepted ↔
          ∃ post, operationalCandidate ctx pre command = .ok post ∧ O.Resources post)""",
    "finite_resource_reject_iff_forward": """∀ (digest : Proofs.AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
      (ctx : T.Context) (pre : O.State) (command : T.Command),
      O.Structural pre →
        ((O.transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
          ∃ post, operationalCandidate ctx pre command = .ok post ∧ ¬ O.Resources post)""",
    "finite_accepted_forward_post": """∀ {digest : Proofs.AssetLaneFiniteByteAccountingV2.Bytes → T.Root}
      {ctx : T.Context} {pre : O.State} {command : T.Command},
      O.Structural pre → (O.transition digest ctx pre command).verdict = .accepted →
        operationalCandidate ctx pre command = .ok (O.transition digest ctx pre command).post""",
    "forward_error_rejects_noop": """∀ (digest : Proofs.AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
      (ctx : T.Context) (pre : O.State) (command : T.Command),
      O.Structural pre → ∀ (code : T.RejectCode),
      operationalCandidate ctx pre command = .error code →
        O.transition digest ctx pre command = O.reject (.economic code) pre""",
    "finite_economic_reject_iff_forward": """∀ (digest : Proofs.AssetLaneFiniteByteAccountingV2.Bytes → T.Root)
      (ctx : T.Context) (pre : O.State) (command : T.Command),
      O.Structural pre → ∀ (code : T.RejectCode),
        (O.transition digest ctx pre command).verdict = .rejected (.economic code) ↔
          operationalCandidate ctx pre command = .error code""",
}


@pytest.fixture(scope="module")
def forward_loop_lean(request: pytest.FixtureRequest) -> LeanSubject:
    """Compile the frozen loop proof as module 27 of the Std-only closure."""

    outcome_subject: LeanSubject = request.getfixturevalue("transfer_outcome_lean")
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


def _axiom_names(output: str) -> set[str]:
    return {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }


def test_frozen_forward_loop_surface_and_standard_axioms(
    forward_loop_lean: LeanSubject,
) -> None:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    source_code = source.decode()
    declared = tuple(re.findall(r"^theorem\s+(\w+)", source_code, flags=re.MULTILINE))
    assert declared == THEOREM_NAMES
    assert len(declared) == len(set(declared)) == 20
    executable = re.sub(r"/-.*?-/", "", source_code, flags=re.DOTALL)
    executable = re.sub(r"--.*$", "", executable, flags=re.MULTILINE)
    assert (
        re.search(
            r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b",
            executable,
        )
        is None
    )

    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    result = _consumer(forward_loop_lean, "ForwardLoopContracts", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    reports = result.stdout.count("depends on axioms") + result.stdout.count(
        "does not depend on any axioms"
    )
    assert reports == len(THEOREM_NAMES)
    assert _axiom_names(result.stdout) <= {"propext", "Quot.sound", "Classical.choice"}


FORWARD_CONSUMER = r"""
import Proofs.AssetTransferForwardLoopV2

set_option warningAsError true
set_option maxRecDepth 100000

open Proofs.AssetTransferFiniteOutcomeV2
open Proofs.GlobalEconomicStateRefinementV2 Proofs.RegisteredSupplySupportV1

namespace IndependentForwardConsumer

deriving instance DecidableEq for Except

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

namespace L
export Proofs.AssetTransferForwardLoopV2 (Ordered checkedPut forwardRaw forward initialScan errorCode
  operationalCandidate operationalCandidate_eq forward_eq_scan_tail finite_accepts_iff_forward
  finite_resource_reject_iff_forward forward_error_rejects_noop finite_economic_reject_iff_forward)
end L
attribute [local instance] lexOrd

theorem base_pre_is_unique_positive_and_ordered :
    S.Unique base.balances ∧ S.PositiveAccounts base.balances ∧ L.Ordered base.balances :=
  ⟨base_structural.balanceUnique, base_structural.balancePositive, by
    change List.Pairwise _ base.balances
    simp [base]⟩

def post : State := {base with balances := [⟨"recipient", "A", "accounts", 5⟩]}

theorem direct_forward_success :
    L.forward base.balances "A" (T.delta (project base p) move) (T.orderedRoles (project base p) move) =
      .ok post.balances := by decide +kernel

theorem direct_operational_success : L.operationalCandidate ctx base move = .ok post := by decide +kernel

theorem independently_inhabited_operational_equality (ctx : T.Context) (command : T.Command) :
    L.operationalCandidate ctx base command =
      match economicRejectCode ctx base command with
      | some code => .error code
      | none => .ok (candidate base command) := L.operationalCandidate_eq ctx base command base_structural

theorem admitted_forward_instance :
    L.forward base.balances "A" (T.delta (project base p) move) (T.orderedRoles (project base p) move) =
      match L.initialScan base.balances "A" (T.delta (project base p) move) (T.orderedRoles (project base p) move) with
      | some code => .error code
      | none => .ok (F.updateRoles base.balances "A" (T.delta (project base p) move) (T.orderedRoles (project base p) move)) :=
  L.forward_eq_scan_tail _ _ _ _ base_structural.balanceUnique base_structural.balancePositive
    (by change List.Pairwise _ base.balances; simp [base]) (by decide)

theorem finite_acceptance_from_computed_forward : (transition constantDigest ctx base move).verdict = .accepted :=
  (L.finite_accepts_iff_forward constantDigest ctx base move base_structural).mpr
    ⟨post, direct_operational_success, by decide⟩

theorem missing_context_propagates_noop :
    transition constantDigest missing base move = reject (.economic .missingOccurrence) base :=
  L.forward_error_rejects_noop constantDigest missing base move base_structural .missingOccurrence (by decide)

def duplicateRows : List AmountRow := [⟨"dup", "A", "accounts", 1⟩]
def repeatedDelta (_ : String) : Int := -1

theorem duplicate_roles_lack_nodup : ¬ ["dup", "dup"].Nodup := by decide

theorem repeated_owner_rechecks_current_value :
    L.initialScan duplicateRows "A" repeatedDelta ["dup", "dup"] = none ∧
    L.forwardRaw duplicateRows "A" repeatedDelta ["dup", "dup"] = .error .insufficientBalance ∧
    L.forward duplicateRows "A" repeatedDelta ["dup", "dup"] = .error .insufficientBalance := by decide

def competingRows : List AmountRow := [⟨"a", "A", "accounts", Proofs.AssetTransferRefinementV2.u128Max⟩]
def competingDelta (owner : String) : Int := if owner = "a" then 1 else -1

theorem supplied_order_controls_competing_failures :
    L.forward competingRows "A" competingDelta ["a", "z"] = .error .balanceOverflow ∧
    L.forward competingRows "A" competingDelta ["z", "a"] = .error .insufficientBalance := by decide

def unordered : List AmountRow := [⟨"z", "A", "accounts", 1⟩, ⟨"a", "A", "accounts", 1⟩]
def canonical : List AmountRow := [⟨"a", "A", "accounts", 1⟩, ⟨"z", "A", "accounts", 1⟩]

theorem empty_loop_still_canonicalizes : L.forward unordered "A" (fun _ => 0) [] = .ok canonical := by
  change Except.ok (Proofs.CanonicalEpochEconomicRowsV1.sortOn S.balanceWire unordered) = Except.ok canonical
  congr 1
  exact Proofs.AssetLaneFiniteRecompositionV2.sortOn_eq_of_perm_keys _ _ _ (by decide) (by decide) (by decide)

theorem omitted_ordered_premise_is_false :
    L.forward unordered "A" (fun _ => 0) [] ≠ .ok (F.updateRoles unordered "A" (fun _ => 0) []) := by
  rw [empty_loop_still_canonicalizes]
  decide

theorem duplicate_pre_keys_excluded : ¬ Structural {base with balances := duplicateRows ++ duplicateRows} := by
  intro bad
  have impossible : ¬ S.Unique (duplicateRows ++ duplicateRows) := by decide
  exact impossible bad.balanceUnique

theorem stored_zero_rows_excluded : ¬ Structural {base with balances := [⟨"dup", "A", "accounts", 0⟩]} := by
  intro bad
  have positive := bad.balancePositive ⟨"dup", "A", "accounts", 0⟩ (by simp)
  exact positive.2.2 rfl

end IndependentForwardConsumer
"""


@pytest.fixture(scope="module")
def forward_loop_consumer_lean(forward_loop_lean: LeanSubject) -> LeanSubject:
    path = forward_loop_lean.source / "ForwardLoopConsumer.lean"
    path.write_text(FORWARD_CONSUMER)
    result = _compile(
        forward_loop_lean,
        path,
        forward_loop_lean.library / "ForwardLoopConsumer.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return forward_loop_lean


def test_independent_forward_consumer_covers_admitted_pre_and_noop(
    forward_loop_consumer_lean: LeanSubject,
) -> None:
    assert (forward_loop_consumer_lean.library / "ForwardLoopConsumer.olean").is_file()


def _semantic_false_control(
    subject: LeanSubject,
    name: str,
    proposition: str,
    proof: str = "by decide",
) -> None:
    path = subject.source / f"{name}.lean"
    path.write_text(
        "import ForwardLoopConsumer\n"
        + OPEN_PREAMBLE
        + "open IndependentForwardConsumer\n"
        + f"example : {proposition} := {proof}\n"
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


def test_omitted_preconditions_and_wrong_failure_order_are_false(
    forward_loop_consumer_lean: LeanSubject,
) -> None:
    controls = (
        (
            "ForwardFalseOmittedNodup",
            'L.forward duplicateRows "A" repeatedDelta ["dup", "dup"] = Except.ok []',
            "by decide",
        ),
        (
            "ForwardFalseInitialTableAlwaysEnough",
            'L.errorCode (L.forwardRaw duplicateRows "A" repeatedDelta ["dup", "dup"]) = '
            'L.initialScan duplicateRows "A" repeatedDelta ["dup", "dup"]',
            "by decide",
        ),
        (
            "ForwardFalseReverseFailureOrder",
            'L.forward competingRows "A" competingDelta ["a", "z"] = Except.error .insufficientBalance',
            "by decide",
        ),
        (
            "ForwardFalseUnsortedEmptyLoop",
            'L.forward unordered "A" (fun _ => 0) [] = Except.ok unordered',
            "by\n  rw [empty_loop_still_canonicalizes]\n  decide",
        ),
    )
    for name, proposition, proof in controls:
        _semantic_false_control(forward_loop_consumer_lean, name, proposition, proof)


def _policy(
    asset: str = "A",
    collector: str = "collector",
    fee: int = 0,
) -> AssetTransferPolicyV2:
    return AssetTransferPolicyV2(
        asset,
        collector,
        fee,
        True,
        AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        ORIGIN,
        8,
    )


def _state(
    rows: list[EconomicAmountV2] | tuple[EconomicAmountV2, ...],
    collector: str = "collector",
    fee: int = 0,
) -> AssetTransferStateV2:
    canonical_rows = tuple(sorted(rows, key=lambda row: (row.asset, row.owner)))
    return AssetTransferStateV2(
        ROOT,
        (_policy(collector=collector, fee=fee), _policy(asset="B")),
        canonical_rows,
        tuple(
            AssetSupplyV2(
                asset,
                sum(row.amount_atoms for row in canonical_rows if row.asset == asset),
            )
            for asset in ("A", "B")
        ),
    )


def _command(
    sender: str = "sender",
    recipient: str = "recipient",
    amount: int = 3,
) -> AssetTransferCommandV2:
    return AssetTransferCommandV2("asset_transfer", "A", sender, recipient, amount, U128, ORIGIN)


def _context(command: AssetTransferCommandV2) -> AssetTransferContextV2:
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
        ROOT,
        1,
        ROOT,
        GLOBAL,
        (),
    )
    return AssetTransferContextV2(1, ROOT, GLOBAL, occurrence)


def _row_wire(rows: list[EconomicAmountV2] | tuple[EconomicAmountV2, ...]) -> list[list[object]]:
    return [[row.asset, row.owner, row.custody_domain, row.amount_atoms] for row in rows]


def _outcome(
    name: str,
    result: AssetTransferRejectCodeV2 | list[EconomicAmountV2] | tuple[EconomicAmountV2, ...],
) -> dict[str, object]:
    return {
        "name": name,
        "code": result.value if isinstance(result, AssetTransferRejectCodeV2) else "OK",
        "rows": None if isinstance(result, AssetTransferRejectCodeV2) else _row_wire(result),
    }


def _lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def _lean_rows(rows: list[EconomicAmountV2] | tuple[EconomicAmountV2, ...]) -> str:
    return (
        "["
        + ", ".join(
            "⟨"
            + ", ".join(
                (
                    _lean_string(row.owner),
                    _lean_string(row.asset),
                    _lean_string(row.custody_domain),
                    str(row.amount_atoms),
                )
            )
            + "⟩"
            for row in rows
        )
        + "]"
    )


def _lean_state(pre: AssetTransferStateV2, compact_4096: bool = False) -> str:
    policies = (
        "["
        + ", ".join(
            "⟨"
            + ", ".join(
                (
                    _lean_string(policy.asset),
                    _lean_string(policy.fee_owner),
                    str(policy.transfer_fee_atoms),
                    "true",
                    ".registeredOrdinaryToken",
                    "some " + _lean_string(ORIGIN),
                    "8",
                )
            )
            + "⟩"
            for policy in pre.policies
        )
        + "]"
    )
    if compact_4096:
        assert len(pre.balances) == 4096
        assert all(
            row == EconomicAmountV2(f"o{index:04d}", "A", "accounts", 9)
            for index, row in enumerate(pre.balances)
        )
        rows = '((List.range 4096).map (fun i => ⟨"o" ++ padded i, "A", "accounts", 9⟩))'
    else:
        rows = _lean_rows(pre.balances)
    supplies = (
        "["
        + ", ".join(
            f"⟨{_lean_string(supply.asset)}, {supply.amount_atoms}⟩" for supply in pre.supplies
        )
        + "]"
    )
    return f"⟨{_lean_string(ROOT)}, {policies}, {rows}, {supplies}⟩"


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
                "some " + _lean_string(ORIGIN),
            )
        )
        + "⟩"
    )


def _lean_context(context: AssetTransferContextV2) -> str:
    occurrence = context.occurrence
    occurrence_expr = "none"
    if occurrence is not None:
        occurrence_expr = (
            "(some ⟨"
            + ", ".join(
                (
                    _lean_string(occurrence.pre_state_root),
                    "[]",
                    _lean_string(occurrence.command_kind),
                    _lean_string(occurrence.command_body_hash),
                    _lean_string(occurrence.subject_id),
                    _lean_string(occurrence.grant_root),
                    _lean_string(occurrence.occurrence_id),
                )
            )
            + "⟩)"
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


def _initial_scan_code(
    pre: AssetTransferStateV2,
    asset: str,
    deltas: tuple[tuple[str, int], ...],
) -> str | None:
    """Independent initial-table scan for the bounded two-owner corpus."""

    initial = {(row.asset, row.owner): row.amount_atoms for row in pre.balances}
    for owner, delta in deltas:
        amount = initial.get((asset, owner), 0) + delta
        if amount < 0:
            return "INSUFFICIENT_BALANCE"
        if amount > U128:
            return "BALANCE_OVERFLOW"
    return None


def _lean_delta(deltas: tuple[tuple[str, int], ...]) -> str:
    """Encode only same-value duplicate owners as a per-owner Lean function."""

    by_owner: dict[str, int] = {}
    for owner, delta in deltas:
        previous = by_owner.setdefault(owner, delta)
        assert previous == delta
    branches = "".join(
        f"if owner = {_lean_string(owner)} then {delta} else " for owner, delta in by_owner.items()
    )
    return f"(fun owner => {branches}0)"


CASE_HEADER = r"""
import Proofs.AssetTransferForwardLoopV2
import Lean.Data.Json
set_option warningAsError true
set_option maxRecDepth 100000
open Proofs.AssetTransferForwardLoopV2 Proofs.GlobalEconomicStateRefinementV2
namespace IndependentForwardCases
deriving instance DecidableEq for Except
def padded (i : Nat) : String := String.ofList (List.replicate (4 - (toString i).length) '0') ++ toString i
def rowsJson (rows : List AmountRow) : Lean.Json := Lean.Json.arr ((rows.map (fun r =>
  Lean.Json.arr #[Lean.toJson r.asset, Lean.toJson r.owner, Lean.toJson r.custodyDomain, Lean.toJson r.amountAtoms])).toArray)
def resultJson (name : String) (result : Except T.RejectCode (List AmountRow)) : Lean.Json :=
  let code := match result with | .ok _ => "OK" | .error code => code.code
  let rows := match result with | .ok rows => rowsJson rows | .error _ => Lean.Json.null
  Lean.Json.mkObj [("name",Lean.toJson name),("code",Lean.toJson code),("rows",rows)]
def genericRows (a b : Nat) : List AmountRow :=
  (if a = 0 then [] else [⟨"a","A","accounts",Int.ofNat a⟩]) ++
  (if b = 0 then [] else [⟨"b","A","accounts",Int.ofNat b⟩]) ++ [⟨"other","B","accounts",7⟩]
def roleChoices : List (List String) := [[],["a"],["b"],["a","b"],["b","a"],["a","a"],["b","b"]]
def sample (a b : Nat) (da db : Int) (roles : List String) (index : Nat) : IO Unit := do
  let name := toString a ++ "," ++ toString b ++ "," ++ toString da ++ "," ++ toString db ++ "," ++ toString index
  let delta := fun owner => if owner = "a" then da else db
  let rows := genericRows a b
  let actual := forward rows "A" delta roles
  let scan := initialScan rows "A" delta roles
  let predicted := match scan with | some code => Except.error code | none => Except.ok (F.updateRoles rows "A" delta roles)
  IO.println ((Lean.Json.mkObj [("result",resultJson name actual),("roles_unique",Lean.toJson (decide roles.Nodup)),
    ("initial_scan",Lean.toJson (scan.map (fun c => c.code))),
    ("scan_tail_match",Lean.toJson (decide (actual = predicted)))]).compress)
def runGenericRange (first stop : Nat) : IO Unit := do
  let mut position := 0
  for a in List.range 3 do
    for b in List.range 3 do
      for da in ([-2,-1,0,1,2] : List Int) do
        for db in ([-2,-1,0,1,2] : List Int) do
          for (roles,index) in roleChoices.zipIdx do
            if first ≤ position ∧ position < stop then sample a b da db roles index
            position := position + 1
def operational (name : String) (ctx : T.Context) (pre : O.State) (cmd : T.Command) : Lean.Json :=
  let actual := operationalCandidate ctx pre cmd
  let result := actual.map (fun post => post.balances)
  let finite := O.transition (fun bytes => toString bytes.length) ctx pre cmd
  let finiteCode := match finite.verdict with | .accepted => "ACCEPTED" | .rejected code => code.code
  let resource := match actual with | .error _ => none | .ok post => some (decide (O.Resources post))
  Lean.Json.mkObj [("result",resultJson name result),("finite_code",Lean.toJson finiteCode),
    ("candidate_resources",Lean.toJson resource),
    ("finite_noop",Lean.toJson (finite.post == pre)),
    ("effects_empty",Lean.toJson (finite.effects == Proofs.AssetTransferRefinementV2.EffectEnvelope.empty))]
"""


def _compile_case_batch(
    subject: LeanSubject,
    batch: int,
    declarations: list[str],
) -> list[dict[str, object]]:
    path = subject.source / f"ForwardLoopCases{batch}.lean"
    path.write_text(CASE_HEADER + "\n".join(declarations) + "\nend IndependentForwardCases\n")
    command = [
        str(subject.executable),
        "-DwarningAsError=true",
        "-R",
        str(subject.source),
        str(path),
    ]
    result = subprocess.run(
        command,
        cwd=subject.source,
        env=dict(os.environ, LEAN_PATH=str(subject.library)),
        capture_output=True,
        text=True,
        check=False,
        timeout=90,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]


def test_bounded_python_rows_and_operational_paths_match_lean_batches(
    forward_loop_lean: LeanSubject,
) -> None:
    roles = ((), ("a",), ("b",), ("a", "b"), ("b", "a"), ("a", "a"), ("b", "b"))
    generic_expected: list[dict[str, object]] = []
    generic_scans: list[str | None] = []
    for a, b in itertools.product(range(3), repeat=2):
        rows: list[EconomicAmountV2] = [EconomicAmountV2("other", "B", "accounts", 7)]
        if a:
            rows.append(EconomicAmountV2("a", "A", "accounts", a))
        if b:
            rows.append(EconomicAmountV2("b", "A", "accounts", b))
        pre = _state(rows)
        before = canonical_global_bytes_v2(pre)
        for da, db in itertools.product(range(-2, 3), repeat=2):
            for index, owners in enumerate(roles):
                deltas = tuple((owner, da if owner == "a" else db) for owner in owners)
                name = f"{a},{b},{da},{db},{index}"
                result = _post_balances(pre, asset="A", deltas=deltas)
                generic_expected.append(_outcome(name, result))
                generic_scans.append(_initial_scan_code(pre, "A", deltas))
        assert canonical_global_bytes_v2(pre) == before
    assert len(generic_expected) == len(generic_scans) == 1575

    endpoints = [
        (
            "second-touch-overflow",
            _state([EconomicAmountV2("a", "A", "accounts", U128 - 1)]),
            (("a", 1), ("a", 1)),
            "BALANCE_OVERFLOW",
        ),
        (
            "second-touch-underflow",
            _state([EconomicAmountV2("a", "A", "accounts", 1)]),
            (("a", -1), ("a", -1)),
            "INSUFFICIENT_BALANCE",
        ),
        (
            "negative-before-later-overflow",
            _state([EconomicAmountV2("a", "A", "accounts", U128)]),
            (("z", -1), ("a", 1)),
            "INSUFFICIENT_BALANCE",
        ),
        (
            "overflow-before-later-negative",
            _state([EconomicAmountV2("a", "A", "accounts", U128)]),
            (("a", 1), ("z", -1)),
            "BALANCE_OVERFLOW",
        ),
    ]
    endpoint_expected: list[dict[str, object]] = []
    endpoint_declarations: list[str] = []
    for name, pre, deltas, wanted in endpoints:
        result = _post_balances(pre, asset="A", deltas=deltas)
        assert isinstance(result, AssetTransferRejectCodeV2)
        assert result.value == wanted
        endpoint_expected.append(_outcome(name, result))
        endpoint_declarations.append(
            "#eval IO.println ((resultJson "
            + _lean_string(name)
            + " (forward "
            + _lean_rows(pre.balances)
            + ' "A" '
            + _lean_delta(deltas)
            + " ["
            + ", ".join(_lean_string(owner) for owner, _ in deltas)
            + "])).compress)"
        )

    other = EconomicAmountV2("other", "B", "accounts", 7)
    operational_cases: list[
        tuple[
            str,
            AssetTransferStateV2,
            AssetTransferCommandV2,
            str,
            AssetTransferContextV2,
            bool,
        ]
    ] = []

    def add_operational(
        name: str,
        pre: AssetTransferStateV2,
        command: AssetTransferCommandV2,
        wanted: str,
        context: AssetTransferContextV2 | None = None,
        compact_4096: bool = False,
    ) -> None:
        operational_cases.append(
            (
                name,
                pre,
                command,
                wanted,
                context if context is not None else _context(command),
                compact_4096,
            )
        )

    add_operational(
        "distinct-fee",
        _state([EconomicAmountV2("sender", "A", "accounts", 10), other], fee=2),
        _command(),
        "ACCEPTED",
    )
    add_operational(
        "sender-collector-alias",
        _state(
            [EconomicAmountV2("sender", "A", "accounts", 3), other],
            collector="sender",
            fee=2,
        ),
        _command(),
        "ACCEPTED",
    )
    add_operational(
        "recipient-collector-alias",
        _state(
            [EconomicAmountV2("sender", "A", "accounts", 5), other],
            collector="recipient",
            fee=2,
        ),
        _command(),
        "ACCEPTED",
    )
    add_operational(
        "zero-fee-distinct",
        _state([EconomicAmountV2("sender", "A", "accounts", 3), other]),
        _command(),
        "ACCEPTED",
    )
    add_operational(
        "self-before-arithmetic",
        _state([EconomicAmountV2("sender", "A", "accounts", 3)]),
        _command(recipient="sender"),
        "SELF_TRANSFER",
    )
    absent = replace(_command(), asset="missing")
    absent_context = _context(absent)
    add_operational(
        "missing-context-before-policy",
        _state([]),
        absent,
        "MISSING_OCCURRENCE",
        replace(absent_context, occurrence=None),
    )
    add_operational("absent-policy-after-context", _state([]), absent, "UNKNOWN_ASSET")
    add_operational(
        "selected-forward-overflow-first",
        _state([EconomicAmountV2("a", "A", "accounts", U128)]),
        _command(sender="z", recipient="a", amount=1),
        "BALANCE_OVERFLOW",
    )
    full_rows = tuple(
        EconomicAmountV2(f"o{index:04d}", "A", "accounts", 9) for index in range(4096)
    )
    full = _state(full_rows)
    add_operational(
        "temporary-4097-final-4096",
        full,
        _command(sender="o4095", recipient="a-new", amount=9),
        "ACCEPTED",
        compact_4096=True,
    )
    add_operational(
        "final-4098-resource-noop",
        _state(full_rows, fee=1),
        _command(sender="o0000", amount=1),
        "STATE_RESOURCE_LIMIT",
        compact_4096=True,
    )

    operational_expected: list[dict[str, object]] = []
    operational_declarations: list[str] = []
    for index, (name, pre, command, wanted, context, compact_4096) in enumerate(operational_cases):
        before = canonical_global_bytes_v2(pre)
        prepared = _prepare_transfer(context, pre, command)
        helper = (
            prepared
            if isinstance(prepared, AssetTransferRejectCodeV2)
            else _post_balances(pre, asset=command.asset, deltas=prepared.deltas)
        )
        finite = transition_asset_transfer_v2(context, pre, command)
        code = "ACCEPTED" if isinstance(finite, AssetTransferAcceptedV2) else finite.code.value
        assert code == wanted
        assert canonical_global_bytes_v2(pre) == before
        resource = None if isinstance(helper, AssetTransferRejectCodeV2) else code == "ACCEPTED"
        post = finite.post_state if isinstance(finite, AssetTransferAcceptedV2) else pre
        if code != "ACCEPTED":
            assert post == pre
            assert finite.effects.is_empty
        operational_expected.append(
            {
                "result": _outcome(name, helper),
                "finite_code": code,
                "candidate_resources": resource,
                "finite_noop": post == pre,
                "effects_empty": finite.effects.is_empty,
            }
        )
        operational_declarations.extend(
            (
                f"def pre{index} : O.State := {_lean_state(pre, compact_4096)}",
                f"def cmd{index} : T.Command := {_lean_command(command)}",
                f"def ctx{index} : T.Context := {_lean_context(context)}",
                f"#eval IO.println ((operational {_lean_string(name)} ctx{index} pre{index} cmd{index}).compress)",
            )
        )
        if name == "temporary-4097-final-4096":
            credit = _post_balances(pre, asset="A", deltas=(("a-new", 9),))
            assert not isinstance(credit, AssetTransferRejectCodeV2)
            assert len(credit) == 4097
            assert not isinstance(helper, AssetTransferRejectCodeV2)
            assert len(helper) == 4096
            operational_declarations.append(
                '#eval IO.println ((Lean.Json.mkObj [("intermediate_rows",Lean.toJson '
                f'(match checkedPut pre{index}.balances "A" "a-new" 9 with | .ok rows => rows.length | .error _ => 0)),'
                f'("final_rows",Lean.toJson (match operationalCandidate ctx{index} pre{index} cmd{index} '
                "with | .ok post => post.balances.length | .error _ => 0))]).compress)"
            )

    assert len(operational_expected) == 10
    # Four bounded compiler invocations keep the finite evaluator replayable on
    # low-disk hosts.  No batch filters a case; together they emit every row.
    batch_declarations = [
        ["#eval runGenericRange 0 394"] + endpoint_declarations,
        ["#eval runGenericRange 394 788"] + operational_declarations[0:16],
        ["#eval runGenericRange 788 1182"] + operational_declarations[16:28],
        ["#eval runGenericRange 1182 1575"] + operational_declarations[28:],
    ]
    assert tuple(
        sum(declaration.startswith("#eval") for declaration in declarations)
        for declarations in batch_declarations
    ) == (5, 5, 4, 5)
    observations: list[dict[str, object]] = []
    for batch, declarations in enumerate(batch_declarations):
        observations.extend(_compile_case_batch(forward_loop_lean, batch, declarations))

    generic = [record for record in observations if "roles_unique" in record]
    endpoint = [record for record in observations if "name" in record]
    operational = [record for record in observations if "finite_code" in record]
    intermediate = [record for record in observations if "intermediate_rows" in record]

    assert len(generic) == 1575
    assert [record["result"] for record in generic] == generic_expected
    assert [record["initial_scan"] for record in generic] == generic_scans
    assert endpoint == endpoint_expected
    assert operational == operational_expected
    assert intermediate == [{"intermediate_rows": 4097, "final_rows": 4096}]

    unique = [record for record in generic if record["roles_unique"]]
    duplicate_counterexamples = [
        record["result"]["name"]
        for record in generic
        if not record["roles_unique"] and not record["scan_tail_match"]
    ]
    assert len(unique) == 1125
    assert all(record["scan_tail_match"] for record in unique)
    assert len(duplicate_counterexamples) == 60
    assert "1,0,-1,0,5" in duplicate_counterexamples
