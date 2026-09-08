"""Retained finite checks for the frozen transfer effect-plan construction.

The source pin, declaration inventory, and signatures bind this harness to the
reviewed Lean module. Concrete vectors compare the current Python transfer
constructor with all six Lean plan fields for bounded inputs. Exact state-byte
equality is checked only for emitted small states through a finite lookup
digest. The compact 4,096-row resource case checks the empty rejected plan and
byte lengths without asserting a universal serializer or hash property.

This bounded Lean/Python closure makes no Rust-parity claim.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferRejectedV2,
    AssetTransferStateV2,
)
from src.core.global_settlement_primitives_v2 import MAX_TOKEN_BYTES_V2
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    GlobalEconomicEffectPlanV2,
    canonical_global_bytes_v2,
)
from tests.formal.test_lean_asset_lane_finite_effect_plan_v2 import (
    effect_plan_lean as effect_plan_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    I128,
    ROOT,
    _command,
    _context,
    _lean_command,
    _lean_context,
    _lean_policy,
    _lean_state,
    _lean_string,
    _policy,
    _state,
    _wire,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    transfer_consumer_lean as transfer_consumer_lean,
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
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import outcome_lean as outcome_lean
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import shared_lean as shared_lean
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

MODULE = "AssetTransferFiniteEffectPlanV2"
NAMESPACE = f"Proofs.{MODULE}"
REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE = REPO_ROOT / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"

SOURCE_SHA256 = "ff36e13be89431ac338b8df685336584fde6fba929808001a130fba1de49f6d6"
THEOREM_DECLARATIONS = (
    ("public", "transfer_rejected_empty"),
    ("public", "movementRows_member"),
    ("public", "movementRows_principals_unique"),
    ("public", "lift_wire_unique"),
    ("public", "transfer_raw_unique"),
    ("public", "transfer_rows_admitted"),
    ("public", "transfer_conservation_admitted"),
    ("public", "transfer_fees_admitted"),
    ("private", "sum_int_append"),
    ("private", "sum_zero_rows"),
    ("public", "transfer_projection"),
    ("public", "transfer_fee_projection"),
    ("public", "transfer_keys_ordered"),
    ("public", "transfer_items"),
    ("public", "transfer_plan_admitted"),
    ("public", "transfer_asset_token"),
    ("public", "transfer_plan_tokens"),
    ("public", "transfer_accepted_fields"),
    ("public", "movement_sum_unique"),
    ("public", "ordered_movement_sum"),
    ("public", "lifted_movement_effect"),
    ("public", "raw_account_effect"),
    ("public", "transfer_account_effect"),
    ("public", "transfer_fee_effect"),
    ("public", "transfer_effect_frame"),
)
THEOREM_NAMES = tuple(name for visibility, name in THEOREM_DECLARATIONS if visibility == "public")
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

# These contracts cover the constructed plan, exact six-field shape, and the
# per-owner movement and fee queries.  The declaration inventory still pins
# every public and private theorem in the frozen source.
MEANINGFUL_TYPES = {
    "transfer_rejected_empty": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
      {command : T.Command} {code : AssetTransferFiniteOutcomeV2.RejectCode},
      (FT.transition digest ctx pre command).verdict = .rejected code →
        transferPlan digest ctx pre command = EffectPlan.empty""",
    "transfer_plan_admitted": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
      {command : T.Command}, FT.Structural pre →
        (FT.transition digest ctx pre command).verdict = .accepted →
          EffectPlanAdmitted (transferPlan digest ctx pre command)""",
    "transfer_plan_tokens": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
      {command : T.Command}, FT.Structural pre → FT.CommandAdmission command →
        (FT.transition digest ctx pre command).verdict = .accepted →
          PlanTokens (transferPlan digest ctx pre command)""",
    "transfer_keys_ordered": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
      {command : T.Command}, FT.Structural pre →
        (FT.transition digest ctx pre command).verdict = .accepted →
          PlanKeysUnique (transferPlan digest ctx pre command) ∧
            PlanOrdered (transferPlan digest ctx pre command)""",
    "transfer_items": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
      {command : T.Command}, (FT.transition digest ctx pre command).verdict = .accepted →
        (transferPlan digest ctx pre command).rows.length ≤ 4 ∧
          PlanWithinItemBounds (transferPlan digest ctx pre command)""",
    "transfer_accepted_fields": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
      {command : T.Command}, (FT.transition digest ctx pre command).verdict = .accepted →
        ∃ (policy : AssetTransferRefinementV2.Policy) (occurrence : AssetTransferRefinementV2.Occurrence),
          FT.policyFor pre command.asset = some policy ∧
          ctx.occurrence = some occurrence ∧
          transferPlan digest ctx pre command =
            ⟨C.sortOn effectWire (transferRawRows (FT.project pre policy) command),
              [transferConservation pre (FT.transition digest ctx pre command).post command],
              transferFees command.asset policy.transferFeeAtoms,
              [⟨.assetTransfer, FT.stateRoot digest pre,
                FT.stateRoot digest (FT.transition digest ctx pre command).post⟩],
              [occurrence.occurrenceId], []⟩""",
    "transfer_account_effect": """∀ {digest : AssetLaneFiniteByteAccountingV2.Bytes → String}
      {ctx : AssetTransferRefinementV2.Context} {pre : AssetTransferFiniteOutcomeV2.State}
      {command : T.Command}, AssetTransferSparseTablesV1.Unique pre.balances →
        (AssetTransferFiniteOutcomeV2.transition digest ctx pre command).verdict = .accepted →
        ∀ owner asset : String,
          GlobalEconomicStateRefinementV2.effectFor .accountMovement
            (transferPlan digest ctx pre command) owner asset AssetTransferSparseTablesV1.accounts =
              CanonicalEpochEconomicRowsV1.lookupLast
                (AssetTransferSparseTablesV1.accountKey asset owner)
                (AssetTransferFiniteOutcomeV2.transition digest ctx pre command).post.balances -
              CanonicalEpochEconomicRowsV1.lookupLast
                (AssetTransferSparseTablesV1.accountKey asset owner) pre.balances""",
    "transfer_fee_effect": """∀ {digest : AssetLaneFiniteByteAccountingV2.Bytes → String}
      {ctx : AssetTransferRefinementV2.Context} {pre : AssetTransferFiniteOutcomeV2.State}
      {command : T.Command} {policy : AssetTransferRefinementV2.Policy},
        AssetTransferFiniteOutcomeV2.policyFor pre command.asset = some policy →
        (AssetTransferFiniteOutcomeV2.transition digest ctx pre command).verdict = .accepted →
        ∀ owner asset domain : String,
          GlobalEconomicStateRefinementV2.effectFor .feeAllocation
            (transferPlan digest ctx pre command) owner asset domain =
              if policy.feeOwner = owner ∧ command.asset = asset ∧
                  AssetTransferSparseTablesV1.accounts = domain then
                policy.transferFeeAtoms else 0""",
    "transfer_effect_frame": """∀ {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
      {command : T.Command}, (FT.transition digest ctx pre command).verdict = .accepted →
        ∀ (kind : EffectKind) (owner asset domain : String),
          ((kind ≠ .accountMovement ∧ kind ≠ .feeAllocation) ∨
            command.asset ≠ asset ∨ S.accounts ≠ domain) →
          effectFor kind (transferPlan digest ctx pre command) owner asset domain = 0""",
}

OPEN_PREAMBLE = f"""open Proofs
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1
open Proofs.AssetTransferFiniteOutcomeV2
open Proofs.AssetLaneFiniteEffectPlanV2
open {NAMESPACE}
attribute [local instance] lexOrd
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
"""
PREAMBLE = f"import {NAMESPACE}\n{OPEN_PREAMBLE}"


@pytest.fixture(scope="module")
def transfer_effect_plan_lean(
    transfer_outcome_lean: LeanSubject,
    effect_plan_lean: LeanSubject,
    transfer_consumer_lean: LeanSubject,
) -> LeanSubject:
    """Compile the frozen transfer plan after both existing plan dependencies."""

    assert transfer_outcome_lean is effect_plan_lean is transfer_consumer_lean
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    path = transfer_outcome_lean.source / "Proofs" / f"{MODULE}.lean"
    path.write_bytes(source)
    result = _compile(
        transfer_outcome_lean,
        path,
        transfer_outcome_lean.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return transfer_outcome_lean


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


def test_axiom_parser_exposes_nonstandard_axioms() -> None:
    parsed = _axiom_names("example depends on axioms: [sorryAx, unexpectedAxiom]")
    assert parsed == {"sorryAx", "unexpectedAxiom"}
    assert parsed - STANDARD_AXIOMS == {"sorryAx", "unexpectedAxiom"}


def test_frozen_transfer_effect_plan_surface_and_standard_axioms(
    transfer_effect_plan_lean: LeanSubject,
) -> None:
    source = SOURCE.read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == SOURCE_SHA256
    declared = tuple(
        ("private" if visibility else "public", name)
        for visibility, name in re.findall(
            r"^(private )?theorem\s+(\w+)", source, flags=re.MULTILINE
        )
    )
    assert declared == THEOREM_DECLARATIONS
    assert len(declared) == len({name for _, name in declared}) == 25
    assert len(THEOREM_NAMES) == 23
    executable = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
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
    result = _consumer(transfer_effect_plan_lean, "TransferFiniteEffectPlanContracts", body)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    reports = result.stdout.count("depends on axioms") + result.stdout.count(
        "does not depend on any axioms"
    )
    assert reports == len(MEANINGFUL_TYPES) + len(THEOREM_NAMES)
    assert _axiom_names(result.stdout) <= STANDARD_AXIOMS


INDEPENDENT_CONSUMER = r"""
import TransferFiniteOutcomeConsumer
import Proofs.AssetTransferFiniteEffectPlanV2

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Proofs Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.AssetLaneFiniteEffectPlanV2 Proofs.AssetTransferFiniteOutcomeV2
open Proofs.AssetTransferFiniteEffectPlanV2
attribute [local instance] lexOrd

namespace IndependentTransferEffectPlanConsumer

open IndependentTransferConsumer

namespace P
export Proofs.AssetTransferFiniteEffectPlanV2 (transferPlan transfer_rejected_empty
  transfer_plan_admitted transfer_plan_tokens transfer_keys_ordered transfer_items
  transfer_accepted_fields transfer_account_effect transfer_fee_effect transfer_effect_frame)
end P

def plan := P.transferPlan constantDigest ctx base move

theorem plan_numeric_admitted : EffectPlanAdmitted plan :=
  P.transfer_plan_admitted base_structural accepted_nonvacuous

theorem plan_tokens_and_order : PlanTokens plan ∧ PlanOrdered plan :=
  ⟨P.transfer_plan_tokens base_structural command_admitted accepted_nonvacuous,
    (P.transfer_keys_ordered base_structural accepted_nonvacuous).2⟩

theorem plan_item_bound : plan.rows.length ≤ 4 :=
  (P.transfer_items accepted_nonvacuous).1

theorem accepted_fields_are_computed :
    ∃ policy occurrence, FT.policyFor base move.asset = some policy ∧
      ctx.occurrence = some occurrence ∧
      plan =
        ⟨C.sortOn effectWire (transferRawRows (FT.project base policy) move),
          [transferConservation base (FT.transition constantDigest ctx base move).post move],
          transferFees move.asset policy.transferFeeAtoms,
          [⟨.assetTransfer, FT.stateRoot constantDigest base,
            FT.stateRoot constantDigest (FT.transition constantDigest ctx base move).post⟩],
          [occurrence.occurrenceId], []⟩ :=
  P.transfer_accepted_fields accepted_nonvacuous

theorem rejected_is_six_empty_fields :
    P.transferPlan constantDigest missing base move = EffectPlan.empty :=
  P.transfer_rejected_empty rejected_nonvacuous

theorem selected_base_policy : FT.policyFor base move.asset = some p := by decide

theorem unknown_owner_account_effect_zero :
    effectFor .accountMovement plan "unknown-owner" "A" AssetTransferSparseTablesV1.accounts = 0 := by
  unfold plan
  rw [P.transfer_account_effect base_structural.balanceUnique accepted_nonvacuous]
  rw [(FT.accepted_post_effects accepted_nonvacuous).1]
  unfold FT.candidate
  rw [selected_base_policy]
  unfold AssetTransferFiniteOutcomeV2.candidateFor
  decide +kernel

theorem other_asset_account_effect_zero :
    effectFor .accountMovement plan "sender" "other-asset" AssetTransferSparseTablesV1.accounts = 0 := by
  unfold plan
  rw [P.transfer_account_effect base_structural.balanceUnique accepted_nonvacuous]
  rw [(FT.accepted_post_effects accepted_nonvacuous).1]
  unfold FT.candidate
  rw [selected_base_policy]
  unfold AssetTransferFiniteOutcomeV2.candidateFor
  decide +kernel

theorem other_domain_account_effect_zero :
    effectFor .accountMovement plan "sender" "A" "other-domain" = 0 := by
  unfold plan
  apply P.transfer_effect_frame accepted_nonvacuous
  simp [AssetTransferSparseTablesV1.accounts]

theorem zero_fee_allocation_effect_zero :
    effectFor .feeAllocation plan "collector" "A" AssetTransferSparseTablesV1.accounts = 0 := by
  unfold plan
  rw [P.transfer_fee_effect selected_base_policy accepted_nonvacuous]
  decide

end IndependentTransferEffectPlanConsumer
"""


@pytest.fixture(scope="module")
def transfer_effect_plan_consumer_lean(
    transfer_effect_plan_lean: LeanSubject,
) -> LeanSubject:
    path = transfer_effect_plan_lean.source / "TransferFiniteEffectPlanConsumer.lean"
    path.write_text(INDEPENDENT_CONSUMER)
    result = _compile(
        transfer_effect_plan_lean,
        path,
        transfer_effect_plan_lean.library / "TransferFiniteEffectPlanConsumer.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return transfer_effect_plan_lean


def test_independent_admission_tokens_order_and_zero_frames(
    transfer_effect_plan_consumer_lean: LeanSubject,
) -> None:
    assert (
        transfer_effect_plan_consumer_lean.library / "TransferFiniteEffectPlanConsumer.olean"
    ).is_file()


@dataclass(frozen=True)
class EffectCase:
    name: str
    pre: AssetTransferStateV2
    context: AssetTransferContextV2
    command: AssetTransferCommandV2
    expected_code: str
    exact_state_bytes: bool


@dataclass(frozen=True)
class PlanObservation:
    case: EffectCase
    expected: dict[str, object]
    pre_bytes: str | None
    post_bytes: str | None
    pre_root: str
    post_root: str


def _effect_fields(plan: GlobalEconomicEffectPlanV2) -> dict[str, object]:
    """Render all six plan fields without relying on a plan root."""

    rows = plan.rows
    asset_conservation = plan.asset_conservation
    fee_conservation = plan.fee_conservation
    lane_writes = plan.lane_writes
    occurrences = plan.occurrence_consumptions
    outbox = plan.external_outbox_enqueue
    return {
        "rows": [
            [row.kind.value, row.principal, row.asset, row.custody_domain, row.delta_atoms]
            for row in rows
        ],
        "asset_conservation": [
            [
                row.asset,
                row.owned_and_custodied_pre_atoms,
                row.owned_and_custodied_post_atoms,
                row.supply_pre_atoms,
                row.supply_post_atoms,
                row.authorized_issue_atoms,
                row.authorized_burn_atoms,
            ]
            for row in asset_conservation
        ],
        "fee_conservation": [
            [
                row.asset,
                row.fee_charged_atoms,
                row.current_allocations_atoms,
                row.carried_residue_atoms,
            ]
            for row in fee_conservation
        ],
        "lane_writes": [
            [write.lane_id.value, write.pre_root, write.post_root] for write in lane_writes
        ],
        "occurrence_consumptions": list(occurrences),
        "external_outbox_enqueue": [
            [
                row.effect_id,
                row.destination_id,
                row.payload_hash,
                row.adapter_profile_root,
            ]
            for row in outbox
        ],
    }


def _effect_for(
    plan: GlobalEconomicEffectPlanV2,
    kind: str,
    owner: str,
    asset: str,
    domain: str,
) -> int:
    return sum(
        row.delta_atoms
        for row in plan.rows
        if row.kind.value == kind
        and row.principal == owner
        and row.asset == asset
        and row.custody_domain == domain
    )


def _queries(
    plan: GlobalEconomicEffectPlanV2,
    command: AssetTransferCommandV2,
    fee_owner: str,
) -> dict[str, list[list[object]]]:
    account = "accounts"
    return {
        "account_queries": [
            [
                "sender",
                _effect_for(plan, "ACCOUNT_MOVEMENT", command.sender, command.asset, account),
            ],
            [
                "recipient",
                _effect_for(plan, "ACCOUNT_MOVEMENT", command.recipient, command.asset, account),
            ],
            [
                "fee_owner",
                _effect_for(plan, "ACCOUNT_MOVEMENT", fee_owner, command.asset, account),
            ],
            [
                "unknown_owner",
                _effect_for(plan, "ACCOUNT_MOVEMENT", "unknown-owner", command.asset, account),
            ],
            [
                "other_asset",
                _effect_for(plan, "ACCOUNT_MOVEMENT", command.sender, "other-asset", account),
            ],
            [
                "other_domain",
                _effect_for(
                    plan, "ACCOUNT_MOVEMENT", command.sender, command.asset, "other-domain"
                ),
            ],
        ],
        "fee_queries": [
            [
                "fee_owner",
                _effect_for(plan, "FEE_ALLOCATION", fee_owner, command.asset, account),
            ],
            [
                "unknown_owner",
                _effect_for(plan, "FEE_ALLOCATION", "unknown-owner", command.asset, account),
            ],
            [
                "other_asset",
                _effect_for(plan, "FEE_ALLOCATION", fee_owner, "other-asset", account),
            ],
            [
                "other_domain",
                _effect_for(plan, "FEE_ALLOCATION", fee_owner, command.asset, "other-domain"),
            ],
        ],
    }


def _effect_cases() -> tuple[EffectCase, ...]:
    escaped_sender = "s" + '"' * (MAX_TOKEN_BYTES_V2 - 1)
    escaped_recipient = "r" + "\\" * (MAX_TOKEN_BYTES_V2 - 1)
    escaped_collector = "c" + '"' * (MAX_TOKEN_BYTES_V2 - 1)
    assert {
        len(value.encode()) for value in (escaped_sender, escaped_recipient, escaped_collector)
    } == {MAX_TOKEN_BYTES_V2}

    cases: list[EffectCase] = []

    def add(
        name: str,
        pre: AssetTransferStateV2,
        command: AssetTransferCommandV2,
        expected_code: str = "ACCEPTED",
        *,
        exact_state_bytes: bool = True,
    ) -> None:
        cases.append(
            EffectCase(name, pre, _context(command), command, expected_code, exact_state_bytes)
        )

    add("fee_zero", _state(5), _command(3))
    add("fee_distinct_collector", _state(10, fee=2), _command(3))
    add(
        "fee_collector_sender",
        _state(5, fee=2, collector="sender"),
        _command(3),
    )
    add(
        "fee_collector_recipient",
        _state(5, fee=2, collector="recipient"),
        _command(3),
    )
    add(
        "escaped_max_identifiers",
        _state(5, owner=escaped_sender, collector=escaped_collector, fee=2),
        _command(3, sender=escaped_sender, recipient=escaped_recipient),
    )
    add("i128_min_debit", _state(I128 + 1, fee=1), _command(I128))

    full_rows = tuple(
        EconomicAmountV2(f"o{index:04d}", "A", "accounts", 9) for index in range(4096)
    )
    full = AssetTransferStateV2(
        ROOT,
        (_policy(fee=1), _policy("B")),
        full_rows,
        (AssetSupplyV2("A", 9 * 4096), AssetSupplyV2("B", 0)),
    )
    add(
        "final_two_new_rows_over_cap",
        full,
        _command(1, sender="o0000"),
        "STATE_RESOURCE_LIMIT",
        exact_state_bytes=False,
    )
    assert len(cases) == 7
    return tuple(cases)


def _runtime_observation(case: EffectCase) -> PlanObservation:
    before = canonical_global_bytes_v2(case.pre)
    result = transition_asset_transfer_v2(case.context, case.pre, case.command)
    assert isinstance(result, (AssetTransferAcceptedV2, AssetTransferRejectedV2))
    accepted = isinstance(result, AssetTransferAcceptedV2)
    code = "ACCEPTED" if accepted else result.code.value
    assert code == case.expected_code, case.name
    assert canonical_global_bytes_v2(case.pre) == before, case.name

    post = result.post_state if accepted else case.pre
    post_bytes = canonical_global_bytes_v2(post)
    expected: dict[str, object] = {
        "name": case.name,
        "code": code,
        "state_bytes": [len(before), len(post_bytes)],
        "pre_bytes_match": True if case.exact_state_bytes else None,
        "post_bytes_match": True if case.exact_state_bytes else None,
        "post_unchanged": post == case.pre,
    }
    if accepted:
        plan = result.effects
        plan.validate()
        policy = next(policy for policy in case.pre.policies if policy.asset == case.command.asset)
        occurrence = case.context.occurrence
        assert occurrence is not None
        assert plan.lane_writes[0].pre_root == case.pre.state_root
        assert plan.lane_writes[0].post_root == post.state_root
        assert plan.occurrence_consumptions == (occurrence.occurrence_id,)
        assert plan.external_outbox_enqueue == ()
        for owner in {case.command.sender, case.command.recipient, policy.fee_owner}:
            assert _effect_for(plan, "ACCOUNT_MOVEMENT", owner, case.command.asset, "accounts") == (
                post.balance_atoms(owner, case.command.asset)
                - case.pre.balance_atoms(owner, case.command.asset)
            )
        assert (
            _effect_for(plan, "FEE_ALLOCATION", policy.fee_owner, case.command.asset, "accounts")
            == policy.transfer_fee_atoms
        )
        expected.update(_effect_fields(plan))
        expected.update(_queries(plan, case.command, policy.fee_owner))
    else:
        assert isinstance(result, AssetTransferRejectedV2)
        assert result.pre_state_root == result.post_state_root == case.pre.state_root
        assert result.effects.is_empty
        expected.update(_effect_fields(result.effects))
        policy = next(policy for policy in case.pre.policies if policy.asset == case.command.asset)
        expected.update(_queries(result.effects, case.command, policy.fee_owner))
    return PlanObservation(
        case,
        expected,
        before.decode() if case.exact_state_bytes else None,
        post_bytes.decode() if case.exact_state_bytes else None,
        case.pre.state_root,
        post.state_root,
    )


CASE_PREAMBLE = f"""import {NAMESPACE}
import Lean.Data.Json

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Proofs
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.AssetTransferFiniteOutcomeV2
open {NAMESPACE}

namespace IndependentTransferEffectPlanCases

def paddedIndex (i : Nat) : String :=
  String.ofList (List.replicate (4 - (toString i).length) '0') ++ toString i

def observation (name : String) (pre : FT.State) (ctx : T.Context) (command : T.Command)
    (feeOwner : String) (expectedPre expectedPost : Option B.Bytes) (digest : B.Bytes → T.Root) :
    Lean.Json := Id.run do
  let result := FT.transition digest ctx pre command
  let plan := transferPlan digest ctx pre command
  let code := match result.verdict with | .accepted => "ACCEPTED" | .rejected reject => reject.code
  let accountEffect := Proofs.GlobalEconomicStateRefinementV2.effectFor .accountMovement plan
  let feeEffect := Proofs.GlobalEconomicStateRefinementV2.effectFor .feeAllocation plan
  return Lean.Json.mkObj [
    ("name", Lean.toJson name),
    ("code", Lean.toJson code),
    ("state_bytes", Lean.toJson [
      (Proofs.AssetTransferFiniteOutcomeV2.stateBytes pre).length,
      (Proofs.AssetTransferFiniteOutcomeV2.stateBytes result.post).length]),
    ("pre_bytes_match", Lean.toJson (expectedPre.map (fun bytes =>
      Proofs.AssetTransferFiniteOutcomeV2.stateBytes pre == bytes))),
    ("post_bytes_match", Lean.toJson (expectedPost.map (fun bytes =>
      Proofs.AssetTransferFiniteOutcomeV2.stateBytes result.post == bytes))),
    ("post_unchanged", Lean.toJson (result.post == pre)),
    ("rows", Lean.Json.arr ((plan.rows.map (fun row => Lean.Json.arr #[
      Lean.toJson row.kind.code, Lean.toJson row.principal, Lean.toJson row.asset,
      Lean.toJson row.custodyDomain, Lean.toJson row.deltaAtoms])).toArray)),
    ("asset_conservation", Lean.Json.arr ((plan.assetConservation.map (fun row => Lean.Json.arr #[
      Lean.toJson row.asset, Lean.toJson row.ownedAndCustodiedPreAtoms,
      Lean.toJson row.ownedAndCustodiedPostAtoms, Lean.toJson row.supplyPreAtoms,
      Lean.toJson row.supplyPostAtoms, Lean.toJson row.authorizedIssueAtoms,
      Lean.toJson row.authorizedBurnAtoms])).toArray)),
    ("fee_conservation", Lean.Json.arr ((plan.feeConservation.map (fun row => Lean.Json.arr #[
      Lean.toJson row.asset, Lean.toJson row.feeChargedAtoms,
      Lean.toJson row.currentAllocationsAtoms, Lean.toJson row.carriedResidueAtoms])).toArray)),
    ("lane_writes", Lean.Json.arr ((plan.laneWrites.map (fun row => Lean.Json.arr #[
      Lean.toJson row.laneId.code, Lean.toJson row.preRoot, Lean.toJson row.postRoot])).toArray)),
    ("occurrence_consumptions", Lean.toJson plan.occurrenceConsumptions),
    ("external_outbox_enqueue", Lean.Json.arr ((plan.externalOutboxEnqueue.map (fun row => Lean.Json.arr #[
      Lean.toJson row.effectId, Lean.toJson row.destinationId, Lean.toJson row.payloadHash,
      Lean.toJson row.adapterProfileRoot])).toArray)),
    ("account_queries", Lean.Json.arr #[
      Lean.Json.arr #[Lean.toJson "sender", Lean.toJson (accountEffect command.sender command.asset S.accounts)],
      Lean.Json.arr #[Lean.toJson "recipient", Lean.toJson (accountEffect command.recipient command.asset S.accounts)],
      Lean.Json.arr #[Lean.toJson "fee_owner", Lean.toJson (accountEffect feeOwner command.asset S.accounts)],
      Lean.Json.arr #[Lean.toJson "unknown_owner", Lean.toJson (accountEffect "unknown-owner" command.asset S.accounts)],
      Lean.Json.arr #[Lean.toJson "other_asset", Lean.toJson (accountEffect command.sender "other-asset" S.accounts)],
      Lean.Json.arr #[Lean.toJson "other_domain", Lean.toJson (accountEffect command.sender command.asset "other-domain")]]),
    ("fee_queries", Lean.Json.arr #[
      Lean.Json.arr #[Lean.toJson "fee_owner", Lean.toJson (feeEffect feeOwner command.asset S.accounts)],
      Lean.Json.arr #[Lean.toJson "unknown_owner", Lean.toJson (feeEffect "unknown-owner" command.asset S.accounts)],
      Lean.Json.arr #[Lean.toJson "other_asset", Lean.toJson (feeEffect feeOwner "other-asset" S.accounts)],
      Lean.Json.arr #[Lean.toJson "other_domain", Lean.toJson (feeEffect feeOwner command.asset "other-domain")]])]

"""


def _case_source(observations: tuple[PlanObservation, ...]) -> str:
    declarations: list[str] = []
    for index, observation in enumerate(observations):
        case = observation.case
        policy = next(policy for policy in case.pre.policies if policy.asset == case.command.asset)
        expected_pre = (
            "none"
            if observation.pre_bytes is None
            else f"some (Proofs.AssetTransferFiniteOutcomeV2.B.raw {_lean_string(observation.pre_bytes)})"
        )
        expected_post = (
            "none"
            if observation.post_bytes is None
            else f"some (Proofs.AssetTransferFiniteOutcomeV2.B.raw {_lean_string(observation.post_bytes)})"
        )
        if observation.pre_bytes is None or observation.post_bytes is None:
            digest = f'def digest{index} (_ : B.Bytes) : T.Root := "resource-digest"'
        else:
            digest = (
                f"def digest{index} (bytes : B.Bytes) : T.Root :=\n"
                f"  if bytes == Proofs.AssetTransferFiniteOutcomeV2.B.raw {_lean_string(observation.pre_bytes)} "
                f"then {_lean_string(observation.pre_root)}\n"
                f"  else if bytes == Proofs.AssetTransferFiniteOutcomeV2.B.raw {_lean_string(observation.post_bytes)} "
                f"then {_lean_string(observation.post_root)}\n"
                '  else "unmatched-digest"'
            )
        declarations.extend(
            (
                f"def pre{index} : FT.State := {_lean_state(_wire(case.pre))}",
                f"def command{index} : T.Command := {_lean_command(case.command)}",
                f"def context{index} : T.Context := {_lean_context(case.context)}",
                digest,
                f"#eval IO.println ((observation {_lean_string(case.name)} pre{index} context{index} "
                f"command{index} {_lean_string(policy.fee_owner)} ({expected_pre}) ({expected_post}) "
                f"digest{index}).compress)",
            )
        )
    return CASE_PREAMBLE + "\n\n".join(declarations) + "\nend IndependentTransferEffectPlanCases\n"


def _parse_observations(output: str) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        assert line.startswith("{"), f"unexpected Lean output: {line}"
        decoded = json.loads(line)
        assert isinstance(decoded, dict)
        records.append(decoded)
    return records


def test_actual_python_transfer_effect_plan_matches_bounded_lean_observations(
    transfer_effect_plan_lean: LeanSubject,
) -> None:
    observations = tuple(_runtime_observation(case) for case in _effect_cases())
    assert len(observations) == 7
    accepted = tuple(item for item in observations if item.case.expected_code == "ACCEPTED")
    resource = tuple(item for item in observations if item.case.expected_code != "ACCEPTED")
    assert len(accepted) == 6
    assert len(resource) == 1

    records: list[dict[str, object]] = []
    for start in range(0, len(accepted), 3):
        batch = accepted[start : start + 3]
        result = _raw_consumer(
            transfer_effect_plan_lean,
            f"TransferFiniteEffectPlanCases{start}",
            _case_source(batch),
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stderr == ""
        records.extend(_parse_observations(result.stdout))

    resource_result = _raw_consumer(
        transfer_effect_plan_lean,
        "TransferFiniteEffectPlanResourceCase",
        _case_source(resource),
    )
    assert resource_result.returncode == 0, resource_result.stdout + resource_result.stderr
    assert resource_result.stderr == ""
    records.extend(_parse_observations(resource_result.stdout))

    assert records == [item.expected for item in observations]
    assert all(record["pre_bytes_match"] is True for record in records[:6])
    assert all(record["post_bytes_match"] is True for record in records[:6])
    assert records[-1]["code"] == "STATE_RESOURCE_LIMIT"
    assert records[-1]["post_unchanged"] is True
    assert records[-1]["rows"] == []
    assert records[-1]["fee_conservation"] == []


# Raw-row controls avoid evaluating a resource branch. The independently
# consumed `transfer_accepted_fields` theorem binds these rows into accepted plans.
def _false_raw_case_source(case: EffectCase, raw_name: str, proposition: str) -> str:
    policies = _wire(case.pre)["policies"]
    assert isinstance(policies, list) and policies
    selected_policy = policies[0]
    assert isinstance(selected_policy, dict)
    return (
        f"import {NAMESPACE}\n"
        + OPEN_PREAMBLE
        + "namespace TransferFiniteEffectPlanFalseControl\n"
        + f"def pre : FT.State := {_lean_state(_wire(case.pre))}\n"
        + f"def command : T.Command := {_lean_command(case.command)}\n"
        + f"def selectedPolicy : T.Policy := {_lean_policy(selected_policy)}\n"
        + f"def {raw_name} := transferRawRows (FT.project pre selectedPolicy) command\n"
        + f"example : {proposition} := by decide\n"
        + "end TransferFiniteEffectPlanFalseControl\n"
    )


def _semantic_false_control(
    subject: LeanSubject,
    name: str,
    source: str,
    fragment: str,
) -> None:
    result = _raw_consumer(subject, name, source)
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


def test_alias_double_count_and_fee_omission_or_misattribution_are_semantic_false_controls(
    transfer_effect_plan_lean: LeanSubject,
) -> None:
    cases = {case.name: case for case in _effect_cases()}
    alias = cases["fee_collector_sender"]
    distinct = cases["fee_distinct_collector"]
    _semantic_false_control(
        transfer_effect_plan_lean,
        "TransferFiniteEffectPlanFalseUncoalescedAlias",
        _false_raw_case_source(
            alias,
            "aliasRaw",
            '⟨.accountMovement, "sender", "A", "accounts", -5⟩ ∈ aliasRaw ∨ '
            '⟨.accountMovement, "sender", "A", "accounts", -2⟩ ∈ aliasRaw',
        ),
        "aliasRaw",
    )
    _semantic_false_control(
        transfer_effect_plan_lean,
        "TransferFiniteEffectPlanFalseFeeOmittedOrMisattributed",
        _false_raw_case_source(
            distinct,
            "distinctRaw",
            '¬ ⟨.feeAllocation, "collector", "A", "accounts", 2⟩ ∈ distinctRaw ∨ '
            '⟨.feeAllocation, "recipient", "A", "accounts", 2⟩ ∈ distinctRaw',
        ),
        "distinctRaw",
    )
