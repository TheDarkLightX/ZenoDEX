"""Independent consumers for the constructed sparse transfer effect plan.

The Lean lane transports the public policy-selection transition into all six
effect-plan fields.  The Python lane calls the public
``transition_asset_transfer_v1`` entry point and derives the expected rows and
conservation values from the submitted command and pre/post account tables.
Opaque roots and occurrence identifiers are transport observations.  Global
fee mirroring, canonical root decoding, authenticated policy membership,
journals, receipts, publication, and complete Python/Rust refinement remain
outside this bounded harness.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict

import pytest

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
)
from src.core.global_economic_state_delta_v1 import _derive_global_economic_state_delta_v1
from src.core.global_economic_state_effect_refinement_v1 import (
    _require_conservation_refinement_v1,
    _require_fee_mirror_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_policy_selection_v1 import (
    Case,
    _balances_view,
    _case,
    _corpus,
    _input_term,
)
from tests.formal.test_lean_asset_transfer_policy_selection_v1 import (
    lean as policy_selection_subject,  # noqa: F401 -- fresh predecessor closure.
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

MODULE = "AssetTransferEffectPlanV1"
NAMESPACE = f"Proofs.{MODULE}"
POLICY_NAMESPACE = "Proofs.AssetTransferPolicySelectionV1"
OTHER_ROOT = "0x" + "02" * 32

OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open {POLICY_NAMESPACE}
open {NAMESPACE}
attribute [local instance] lexOrd
"""

# Public signatures are written here independently of the proof source.  The
# contract test deliberately fails if the proof worker changes this surface
# without a corresponding consumer update.
THEOREM_TYPES = {
    "selectedPlan_rows":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).rows = (S.projectedPlan input).rows",
    "selectedPlan_asset_conservation":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).assetConservation = [conservationRow input]",
    "selectedPlan_fee_conservation":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).feeConservation = feeRows input",
    "selectedPlan_lane_writes":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).laneWrites = [{ laneId := .assetTransfer, preRoot := fields.preLaneRoot, postRoot := fields.postLaneRoot }]",
    "selectedPlan_occurrences":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).occurrenceConsumptions = [fields.occurrenceId]",
    "selectedPlan_outbox":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).externalOutboxEnqueue = []",
    "selectedPlan_rows_sorted":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).rows.Pairwise (fun left right => (compare (S.effectWire left) (S.effectWire right)).isLE = true)",
    "projectedPlan_keys_unique":
        "∀ {input : S.Input}, (S.step input).verdict = .accepted → ((S.projectedPlan input).rows.map EconomicEffectRow.key).Nodup",
    "selectedPlan_fee_projection":
        "∀ (fields : CommitmentFields) (input : S.Input), FeeProjectionMatches (selectedPlan fields input)",
    "selectedPlan_projection":
        "∀ (fields : CommitmentFields) (input : S.Input), ProjectionMatches (selectedPlan fields input)",
    "selectedPlan_rows_length_le_four":
        "∀ (fields : CommitmentFields) (input : S.Input), (selectedPlan fields input).rows.length ≤ 4",
    "complete_preserves_verdict_post":
        "∀ (fields : CommitmentFields) (input : K.Input), (complete fields input).verdict = (K.step input).verdict ∧ (complete fields input).post = (K.step input).post",
    "complete_rejected":
        "∀ {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}, (K.step input).verdict = .rejected code → complete fields input = K.step input",
    "complete_rejected_empty":
        "∀ {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}, (K.step input).verdict = .rejected code → (complete fields input).post = input.pre ∧ (complete fields input).plan = EffectPlan.empty",
    "complete_accepted_plan":
        "∀ {fields : CommitmentFields} {input : K.Input} {policy : T.Policy}, (K.step input).verdict = .accepted → K.policyFor input.pre.policies input.command.asset = some policy → (complete fields input).plan = selectedPlan fields (K.selectedInput input policy)",
    "complete_preserves_rows":
        "∀ (fields : CommitmentFields) (input : K.Input), (complete fields input).plan.rows = (K.step input).plan.rows",
    "complete_effect_plan_admitted":
        "∀ (fields : CommitmentFields) (input : K.Input), K.StateAdmitted input.pre → EffectPlanAdmitted (complete fields input).plan",
    "complete_accepted_exact_relations":
        "∀ {fields : CommitmentFields} {input : K.Input}, K.StateAdmitted input.pre → (K.step input).verdict = .accepted → ExactEconomicTables input.pre.economic (complete fields input).post.economic (complete fields input).plan ∧ ExactSupplyEffects input.pre.economic (complete fields input).post.economic (complete fields input).plan",
}

SOURCE_PINS = {
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean":
        "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean":
        "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "lean-mathlib/Proofs/AssetTransferSparseTraceV1.lean":
        "5a77ac04b4e214ab7d0dc6cb4b77e2369e16a7914d02cffb5df1d0b88f119b83",
    "lean-mathlib/Proofs/AssetTransferSparseStateAdmissionV1.lean":
        "82f54f4d5a5ba5e28a2ed2a96cd6b4155e70458c05d104b31eea0717aaae8649",
    "lean-mathlib/Proofs/AssetTransferSparseAuthorizationV1.lean":
        "91d41486e814f80a876746a1d8a542daeda77599415792b0915f4a2fccc495fa",
    "lean-mathlib/Proofs/AssetTransferPolicySelectionV1.lean":
        "6c330fb920885223089d774eaf6110a3007bd2790a3c69dc947f80255edff321",
    "lean-mathlib/Proofs/AssetTransferEffectPlanV1.lean":
        "14cea53d90e1fdc6f068e581dcc8e737526475b323100c5d6c27b9354f769de9",
    "src/core/asset_transfer_module_v1.py":
        "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py":
        "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_settlement_types_v1.py":
        "854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4",
    "src/core/global_economic_state_effect_refinement_v1.py":
        "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
    "src/core/global_economic_state_delta_v1.py":
        "5b06120b14176985a2889b81cc784145339b7f72720d7b161c74b296cb4e5634",
}


@pytest.fixture(scope="module")
def lean(policy_selection_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Compile the new source in the predecessor's fresh Lean closure."""
    captured = policy_selection_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes((PROJECT / "Proofs" / f"{MODULE}.lean").read_bytes())
    result = _compile(
        policy_selection_subject,
        captured,
        policy_selection_subject.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return policy_selection_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _decode(output: str) -> list[list[list[str]]]:
    return [json.loads(json.loads(line)) for line in output.splitlines()]


def _policy_view(policies: tuple[AssetTransferPolicyV1, ...]) -> list[list[str]]:
    return [
        [policy.asset, policy.fee_owner, str(policy.transfer_fee_atoms), str(policy.enabled).lower()]
        for policy in policies
    ]


def _supplies_view(supplies: tuple[AssetSupplyV1, ...]) -> list[list[str]]:
    return [[supply.asset, str(supply.amount_atoms)] for supply in supplies]


def _effect_rows_expected(case: Case, policy: AssetTransferPolicyV1) -> list[list[str]]:
    command = case.command
    events = (
        (command.sender, -command.amount_atoms - policy.transfer_fee_atoms),
        (command.recipient, command.amount_atoms),
        (policy.fee_owner, policy.transfer_fee_atoms),
    )
    movement = {
        owner: sum(delta for event_owner, delta in events if event_owner == owner)
        for owner, _ in events
    }
    rows = [
        ["ACCOUNT_MOVEMENT", owner, command.asset, "accounts", str(delta)]
        for owner, delta in movement.items()
        if delta
    ]
    if policy.transfer_fee_atoms:
        rows.append([
            "FEE_ALLOCATION", policy.fee_owner, command.asset, "accounts",
            str(policy.transfer_fee_atoms),
        ])
    rows.sort(key=lambda row: (row[0], row[2], row[1], row[3]))
    return rows


def _global_state(
    case: Case,
    balances: tuple[EconomicAmountV1, ...],
    custody: tuple[EconomicAmountV1, ...] = (),
    *,
    asset_lane_root: str | None = None,
) -> GlobalEconomicStateV1:
    lane_roots = tuple(
        LaneStateRootV1(
            lane,
            case.context.module_release_id,
            True,
            asset_lane_root if lane is LaneIdV1.ASSET_TRANSFER and asset_lane_root else case.pre.state_root,
        )
        for lane in ALL_LANE_IDS_V1
    )
    return GlobalEconomicStateV1(
        chain_id=case.context.chain_id,
        deployment_root=case.context.deployment_root,
        writer_epoch=case.context.writer_epoch,
        height=1,
        profile_root=case.context.profile_root,
        lane_roots=lane_roots,
        balances=balances,
        supplies=case.pre.supplies,
        custody=custody,
    )


def _complete_expected_view(case: Case) -> tuple[list[list[str]], object]:
    """Return an input-derived complete view and the runtime result for roots."""
    before = (
        canonical_global_bytes_v1(case.context),
        canonical_global_bytes_v1(case.pre),
        canonical_global_bytes_v1(case.command),
        asdict(case.context),
        asdict(case.pre),
        asdict(case.command),
    )
    result = transition_asset_transfer_v1(case.context, case.pre, case.command)
    after = (
        canonical_global_bytes_v1(case.context),
        canonical_global_bytes_v1(case.pre),
        canonical_global_bytes_v1(case.command),
        asdict(case.context),
        asdict(case.pre),
        asdict(case.command),
    )
    assert before == after
    if case.error is not None:
        assert isinstance(result, AssetTransferRejectedV1)
        assert result.code.value == case.error
        assert result.pre_state_root == result.post_state_root == case.pre.state_root
        assert result.effects.rows == ()
        assert result.effects.asset_conservation == ()
        assert result.effects.fee_conservation == ()
        assert result.effects.lane_writes == ()
        assert result.effects.occurrence_consumptions == ()
        assert result.effects.external_outbox_enqueue == ()
        policy = None
        post = case.pre
        rows: list[list[str]] = []
        assets: list[list[str]] = []
        fees: list[list[str]] = []
        lanes: list[list[str]] = []
        occurrences: list[list[str]] = []
        outbox: list[list[str]] = []
    else:
        assert isinstance(result, AssetTransferAcceptedV1)
        policy = next(policy for policy in case.pre.policies if policy.asset == case.command.asset)
        post = result.post_state
        assert post.policies == case.pre.policies
        assert post.supplies == case.pre.supplies
        rows = _effect_rows_expected(case, policy)
        assert [
            [row.kind.value, row.principal, row.asset, row.custody_domain, str(row.delta_atoms)]
            for row in result.effects.rows
        ] == rows
        pre_owned = sum(row.amount_atoms for row in case.pre.balances if row.asset == case.command.asset)
        post_owned = sum(row.amount_atoms for row in post.balances if row.asset == case.command.asset)
        pre_supply = next(row.amount_atoms for row in case.pre.supplies if row.asset == case.command.asset)
        post_supply = next(row.amount_atoms for row in post.supplies if row.asset == case.command.asset)
        assets = [[
            case.command.asset, str(pre_owned), str(post_owned), str(pre_supply),
            str(post_supply), "0", "0",
        ]]
        fees = ([[case.command.asset, str(policy.transfer_fee_atoms),
                  str(policy.transfer_fee_atoms), "0"]]
                if policy.transfer_fee_atoms else [])
        lanes = [["ASSET_TRANSFER", case.pre.state_root, post.state_root]]
        occurrences = [[case.context.command_occurrence_id]]
        outbox = []
        assert [
            [row.asset, str(row.owned_and_custodied_pre_atoms),
             str(row.owned_and_custodied_post_atoms), str(row.supply_pre_atoms),
             str(row.supply_post_atoms), str(row.authorized_issue_atoms),
             str(row.authorized_burn_atoms)]
            for row in result.effects.asset_conservation
        ] == assets
        assert [
            [row.asset, str(row.fee_charged_atoms),
             str(row.current_allocations_atoms), str(row.carried_residue_atoms)]
            for row in result.effects.fee_conservation
        ] == fees
        assert [
            [row.lane_id.value, row.pre_root, row.post_root]
            for row in result.effects.lane_writes
        ] == lanes
        assert [[occurrence] for occurrence in result.effects.occurrence_consumptions] == occurrences
        assert result.effects.external_outbox_enqueue == ()
    verdict = case.error or "ACCEPTED"
    view = [
        ["VERDICT", verdict],
        ["POST_BALANCES"], *_balances_view(post.balances),
        ["POST_POLICIES"], *_policy_view(post.policies),
        ["POST_SUPPLIES"], *_supplies_view(post.supplies),
        ["ROWS"], *rows,
        ["ASSET_CONSERVATION"], *assets,
        ["FEE_CONSERVATION"], *fees,
        ["LANE_WRITES"], *lanes,
        ["OCCURRENCE_CONSUMPTIONS"], *occurrences,
        ["EXTERNAL_OUTBOX_ENQUEUE"], *outbox,
    ]
    return view, result


OBSERVERS = r'''
def verdictCode : T.Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def balancesView (rows : List G.AmountRow) : List (List String) :=
  rows.map fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]

def policyView (rows : List T.Policy) : List (List String) :=
  rows.map fun policy =>
    [policy.asset, policy.feeOwner, toString policy.transferFeeAtoms,
      toString policy.enabled]

def suppliesView (rows : List G.SupplyRow) : List (List String) :=
  rows.map fun supply => [supply.asset, toString supply.amountAtoms]

def effectRowsView (rows : List EconomicEffectRow) : List (List String) :=
  rows.map fun row =>
    [row.kind.code, row.principal, row.asset, row.custodyDomain, toString row.deltaAtoms]

def assetConservationView (rows : List AssetConservationRow) : List (List String) :=
  rows.map fun row =>
    [row.asset, toString row.ownedAndCustodiedPreAtoms,
      toString row.ownedAndCustodiedPostAtoms, toString row.supplyPreAtoms,
      toString row.supplyPostAtoms, toString row.authorizedIssueAtoms,
      toString row.authorizedBurnAtoms]

def feeConservationView (rows : List FeeConservationRow) : List (List String) :=
  rows.map fun row =>
    [row.asset, toString row.feeChargedAtoms,
      toString row.currentAllocationsAtoms, toString row.carriedResidueAtoms]

def laneWritesView (rows : List LaneWrite) : List (List String) :=
  rows.map fun row => [row.laneId.code, row.preRoot, row.postRoot]

def occurrenceView (rows : List RootId) : List (List String) :=
  rows.map fun occurrence => [occurrence]

def outboxView (rows : List ExternalOutboxEnqueue) : List (List String) :=
  rows.map fun row =>
    [row.effectId, row.destinationId, row.payloadHash, row.adapterProfileRoot]

def observe (out : Proofs.AssetTransferPolicySelectionV1.Result) : List (List String) :=
  [["VERDICT", verdictCode out.verdict], ["POST_BALANCES"]] ++
    balancesView out.post.economic.balances ++ [["POST_POLICIES"]] ++
    policyView out.post.policies ++ [["POST_SUPPLIES"]] ++
    suppliesView out.post.economic.supplies ++ [["ROWS"]] ++
    effectRowsView out.plan.rows ++ [["ASSET_CONSERVATION"]] ++
    assetConservationView out.plan.assetConservation ++ [["FEE_CONSERVATION"]] ++
    feeConservationView out.plan.feeConservation ++ [["LANE_WRITES"]] ++
    laneWritesView out.plan.laneWrites ++ [["OCCURRENCE_CONSUMPTIONS"]] ++
    occurrenceView out.plan.occurrenceConsumptions ++ [["EXTERNAL_OUTBOX_ENQUEUE"]] ++
    outboxView out.plan.externalOutboxEnqueue
'''


def _commitment_term(case: Case, result: object) -> str:
    if isinstance(result, AssetTransferAcceptedV1):
        post_root = result.post_state.state_root
    else:
        post_root = case.pre.state_root
    return "⟨" + ",".join(
        json.dumps(value)
        for value in (case.pre.state_root, post_root, case.context.command_occurrence_id)
    ) + "⟩"


def test_public_complete_compares_all_six_effect_plan_fields_from_input_oracle(
    lean: LeanSubject,
) -> None:
    cases = _corpus()
    expected_results = [_complete_expected_view(case) for case in cases]
    expected = [view for view, _ in expected_results]
    probes = "\n".join(
        f"#eval IO.println (reprStr (reprStr (observe (complete ({_commitment_term(case, result)}) "
        f"({_input_term(case)} : {POLICY_NAMESPACE}.Input)))))"
        for case, (_, result) in zip(cases, expected_results, strict=True)
    )
    assert _decode(_probe(lean, "EffectPlanRuntimeCorpus", OBSERVERS + probes)) == expected


def test_positive_sender_fee_remains_refused_by_global_mirror() -> None:
    case = _case(
        "sender_fee", policies=(
            AssetTransferPolicyV1("EUR", "alice", 2, True),
            AssetTransferPolicyV1("USD", "usd_treasury", 1, True),
        ), asset="EUR", amount=3, max_fee=2,
    )
    result = transition_asset_transfer_v1(case.context, case.pre, case.command)
    assert isinstance(result, AssetTransferAcceptedV1)
    with pytest.raises(ValueError, match="^economic refinement fee allocation is not mirrored$"):
        _require_fee_mirror_v1(result.effects)


def test_accounts_only_conservation_boundary_excludes_global_custody() -> None:
    accounts_only = _case(
        "accounts_only",
        supplies=(AssetSupplyV1("EUR", 45), AssetSupplyV1("USD", 57)),
    )
    result = transition_asset_transfer_v1(
        accounts_only.context, accounts_only.pre, accounts_only.command,
    )
    assert isinstance(result, AssetTransferAcceptedV1)
    _require_fee_mirror_v1(result.effects)
    pre_global = _global_state(accounts_only, accounts_only.pre.balances)
    post_global = _global_state(
        accounts_only,
        result.post_state.balances,
        asset_lane_root=result.post_state.state_root,
    )
    delta = _derive_global_economic_state_delta_v1(pre_global, post_global, result.effects, ())
    _require_conservation_refinement_v1(pre_global, post_global, result.effects, delta)

    custody = (
        EconomicAmountV1("pool", "EUR", "custody", 55),
        EconomicAmountV1("pool", "USD", "custody", 43),
    )
    with_custody = _case(
        "with_custody",
        supplies=(AssetSupplyV1("EUR", 100), AssetSupplyV1("USD", 100)),
    )
    custody_result = transition_asset_transfer_v1(
        with_custody.context, with_custody.pre, with_custody.command,
    )
    assert isinstance(custody_result, AssetTransferAcceptedV1)
    _require_fee_mirror_v1(custody_result.effects)
    custody_pre = _global_state(with_custody, with_custody.pre.balances, custody)
    custody_post = _global_state(
        with_custody,
        custody_result.post_state.balances,
        custody,
        asset_lane_root=custody_result.post_state.state_root,
    )
    custody_delta = _derive_global_economic_state_delta_v1(
        custody_pre, custody_post, custody_result.effects, (),
    )
    assert sum(row.amount_atoms for row in custody_pre.balances if row.asset == "USD") == 57
    assert sum(row.amount_atoms for row in custody_pre.custody if row.asset == "USD") == 43
    assert sum(row.amount_atoms for row in custody_pre.balances if row.asset == "USD") + sum(
        row.amount_atoms for row in custody_pre.custody if row.asset == "USD"
    ) == 100
    with pytest.raises(ValueError, match="^economic refinement conservation state mismatch$"):
        _require_conservation_refinement_v1(
            custody_pre, custody_post, custody_result.effects, custody_delta,
        )


def test_contract_axioms_placeholders_registration_and_source_pins(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(THEOREM_TYPES)
    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n"
        f"#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    report = " ".join(_probe(lean, "EffectPlanIndependentConsumers", consumers).split())
    for name in THEOREM_TYPES:
        found = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
            report,
        )
        assert found, (name, report)
        axioms = {
            item.strip() for item in (found.group(1) or "").split(",") if item.strip()
        }
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)
    assert f"import {NAMESPACE}" in (PROJECT / "Proofs.lean").read_text().splitlines()
    for path, digest in SOURCE_PINS.items():
        assert hashlib.sha256((PROJECT.parent / path).read_bytes()).hexdigest() == digest


def test_nonempty_complete_witness_proves_admission_with_opaque_roots(
    lean: LeanSubject,
) -> None:
    body = r'''
namespace NonemptyCompleteWitness

def policy : T.Policy := ⟨"USD", "treasury", 1, true⟩

def initial : State :=
  { moduleReleaseId := "release"
    policies := [policy]
    economic := { staticGlobalState with
      balances := [
        ⟨"alice", "USD", "accounts", 40⟩,
        ⟨"bob", "USD", "accounts", 5⟩]
      supplies := [⟨"USD", 45⟩] } }

def input : Input :=
  { context := ⟨"release", "alice"⟩
    command := ⟨"asset_transfer", "USD", "alice", "bob", 4, 1⟩
    pre := initial }

def fields : CommitmentFields :=
  ⟨"opaque-pre", "opaque-post", "opaque-occurrence"⟩

def output := complete fields input

theorem initial_admitted : StateAdmitted initial := by
  refine ⟨?_, ?_, ?_, by decide, ?_⟩
  · unfold S.CanonicalBalances
    refine ⟨?_, ?_, by decide, ?_⟩
    · unfold S.Unique
      decide
    · intro row member
      simp [initial] at member
      rcases member with rfl | rfl <;> decide
    · decide
  · unfold PoliciesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro candidate member
    simp [initial] at member
    rcases member with rfl <;> decide
  · unfold SuppliesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro supply member
    simp [initial] at member
    rcases member with rfl <;> decide
  · intro asset
    by_cases usd : "USD" = asset
    · subst asset
      decide
    · simp [initial, amountForAsset, supplyFor, usd]

example : T.CommandWellFormed input.command := by
  exact ⟨by decide, by decide⟩
example : (K.step input).verdict = .accepted := by decide
example : output.verdict = .accepted := by decide
example : EffectPlanAdmitted output.plan :=
  complete_effect_plan_admitted fields input initial_admitted
example :
    ExactEconomicTables initial.economic output.post.economic output.plan ∧
      ExactSupplyEffects initial.economic output.post.economic output.plan :=
  complete_accepted_exact_relations initial_admitted (by decide)
example : output.plan.rows.length = 4 := by
  have accepted : (K.step input).verdict = .accepted := by decide
  have selection : K.policyFor input.pre.policies input.command.asset = some policy := by
    simp [input, initial, policy, K.policyFor]
  change (complete fields input).plan.rows.length = 4
  rw [complete_accepted_plan (fields := fields) accepted selection]
  change (C.sortOn S.effectWire _).length = 4
  rw [(C.sortOn_perm S.effectWire _).length_eq]
  decide
example : output.plan.assetConservation.length = 1 := by rfl
example : output.plan.feeConservation.length = 1 := by rfl
example : output.plan.laneWrites.length = 1 := by rfl
example : output.plan.occurrenceConsumptions.length = 1 := by rfl
example : output.plan.externalOutboxEnqueue.length = 0 := by rfl
example : amountAt output.post.economic.balances "alice" "USD" "accounts" = 35 := by
  change amountAt (complete fields input).post.economic.balances "alice" "USD" "accounts" = 35
  have selection : policyFor input.pre.policies input.command.asset = some policy := by
    simp [input, initial, policy, policyFor]
  have frontDoor : step input = lift input (S.step (selectedInput input policy)) :=
    step_selected (input := input) (policy := policy) (by rfl) (by rfl) selection
  rw [(complete_preserves_verdict_post fields input).2, frontDoor]
  simp only [lift]
  have equation := Proofs.AssetTransferSparseTablesV1.accepted_balance_equation
    (input := selectedInput input policy)
    initial_admitted.1.1 initial_admitted.1.2.1 (by decide)
    "alice" "USD" "accounts"
  have equation' :
      amountAt (S.step (selectedInput input policy)).post.balances
          "alice" "USD" "accounts" -
        amountAt input.pre.economic.balances "alice" "USD" "accounts" = -5 := by
    simpa [selectedInput, input, initial, policy,
      Proofs.AssetTransferSparseTablesV1.localState,
      Proofs.AssetTransferRefinementV1.delta,
      Proofs.AssetTransferRefinementV1.indicator] using equation
  have preAmount : amountAt input.pre.economic.balances "alice" "USD" "accounts" = 40 := by
    simp [input, initial, amountAt]
  omega
example : amountAt output.post.economic.balances "bob" "USD" "accounts" = 9 := by
  change amountAt (complete fields input).post.economic.balances "bob" "USD" "accounts" = 9
  have selection : policyFor input.pre.policies input.command.asset = some policy := by
    simp [input, initial, policy, policyFor]
  have frontDoor : step input = lift input (S.step (selectedInput input policy)) :=
    step_selected (input := input) (policy := policy) (by rfl) (by rfl) selection
  rw [(complete_preserves_verdict_post fields input).2, frontDoor]
  simp only [lift]
  have equation := Proofs.AssetTransferSparseTablesV1.accepted_balance_equation
    (input := selectedInput input policy)
    initial_admitted.1.1 initial_admitted.1.2.1 (by decide)
    "bob" "USD" "accounts"
  have equation' :
      amountAt (S.step (selectedInput input policy)).post.balances
          "bob" "USD" "accounts" -
        amountAt input.pre.economic.balances "bob" "USD" "accounts" = 4 := by
    simpa [selectedInput, input, initial, policy,
      Proofs.AssetTransferSparseTablesV1.localState,
      Proofs.AssetTransferRefinementV1.delta,
      Proofs.AssetTransferRefinementV1.indicator] using equation
  have preAmount : amountAt input.pre.economic.balances "bob" "USD" "accounts" = 5 := by
    simp [input, initial, amountAt]
  omega
example : amountAt output.post.economic.balances "treasury" "USD" "accounts" = 1 := by
  change amountAt (complete fields input).post.economic.balances "treasury" "USD" "accounts" = 1
  have selection : policyFor input.pre.policies input.command.asset = some policy := by
    simp [input, initial, policy, policyFor]
  have frontDoor : step input = lift input (S.step (selectedInput input policy)) :=
    step_selected (input := input) (policy := policy) (by rfl) (by rfl) selection
  rw [(complete_preserves_verdict_post fields input).2, frontDoor]
  simp only [lift]
  have equation := Proofs.AssetTransferSparseTablesV1.accepted_balance_equation
    (input := selectedInput input policy)
    initial_admitted.1.1 initial_admitted.1.2.1 (by decide)
    "treasury" "USD" "accounts"
  have equation' :
      amountAt (S.step (selectedInput input policy)).post.balances
          "treasury" "USD" "accounts" -
        amountAt input.pre.economic.balances "treasury" "USD" "accounts" = 1 := by
    simpa [selectedInput, input, initial, policy,
      Proofs.AssetTransferSparseTablesV1.localState,
      Proofs.AssetTransferRefinementV1.delta,
      Proofs.AssetTransferRefinementV1.indicator] using equation
  have preAmount : amountAt input.pre.economic.balances "treasury" "USD" "accounts" = 0 := by
    simp [input, initial, amountAt]
  omega
example : output.plan.laneWrites = [
    ⟨.assetTransfer, "opaque-pre", "opaque-post"⟩] := by rfl
example : output.plan.occurrenceConsumptions = ["opaque-occurrence"] := by rfl

#eval IO.println (reprStr (reprStr [
  ["ALICE", toString (amountAt output.post.economic.balances "alice" "USD" "accounts")],
  ["BOB", toString (amountAt output.post.economic.balances "bob" "USD" "accounts")],
  ["TREASURY", toString (amountAt output.post.economic.balances "treasury" "USD" "accounts")],
  ["ROWS", toString output.plan.rows.length],
  ["ASSET_ROWS", toString output.plan.assetConservation.length],
  ["FEE_ROWS", toString output.plan.feeConservation.length],
  ["LANES", toString output.plan.laneWrites.length],
  ["OCCURRENCES", toString output.plan.occurrenceConsumptions.length],
  ["OUTBOX", toString output.plan.externalOutboxEnqueue.length]]))

end NonemptyCompleteWitness
'''
    assert json.loads(json.loads(_probe(lean, "NonemptyCompleteWitness", body).strip())) == [
        ["ALICE", "35"], ["BOB", "9"], ["TREASURY", "1"],
        ["ROWS", "4"], ["ASSET_ROWS", "1"], ["FEE_ROWS", "1"],
        ["LANES", "1"], ["OCCURRENCES", "1"], ["OUTBOX", "0"],
    ]


def test_complete_rejection_is_exact_six_field_noop(lean: LeanSubject) -> None:
    case = _case(
        "rejected", context_release=OTHER_ROOT, command_kind="other",
        asset="MISSING", error="RELEASE_MISMATCH",
    )
    expected, result = _complete_expected_view(case)
    assert isinstance(result, AssetTransferRejectedV1)
    body = f'''
def rejected : {POLICY_NAMESPACE}.Input := {_input_term(case)}
def fields : CommitmentFields := ⟨"opaque-pre", "opaque-post", "opaque-occurrence"⟩
def output := complete fields rejected
example : output.verdict = .rejected .releaseMismatch := by decide
example : output.post = rejected.pre :=
  (complete_rejected_empty (fields := fields) (input := rejected)
    (code := .releaseMismatch) (by decide)).1
example : output.plan.rows = [] := by
  have empty := (complete_rejected_empty (fields := fields) (input := rejected)
    (code := .releaseMismatch) (by decide)).2
  simpa [EffectPlan.empty] using congrArg (fun plan => plan.rows) empty
example : output.plan.assetConservation = [] := by
  have empty := (complete_rejected_empty (fields := fields) (input := rejected)
    (code := .releaseMismatch) (by decide)).2
  simpa [EffectPlan.empty] using congrArg (fun plan => plan.assetConservation) empty
example : output.plan.feeConservation = [] := by
  have empty := (complete_rejected_empty (fields := fields) (input := rejected)
    (code := .releaseMismatch) (by decide)).2
  simpa [EffectPlan.empty] using congrArg (fun plan => plan.feeConservation) empty
example : output.plan.laneWrites = [] := by
  have empty := (complete_rejected_empty (fields := fields) (input := rejected)
    (code := .releaseMismatch) (by decide)).2
  simpa [EffectPlan.empty] using congrArg (fun plan => plan.laneWrites) empty
example : output.plan.occurrenceConsumptions = [] := by
  have empty := (complete_rejected_empty (fields := fields) (input := rejected)
    (code := .releaseMismatch) (by decide)).2
  simpa [EffectPlan.empty] using congrArg (fun plan => plan.occurrenceConsumptions) empty
example : output.plan.externalOutboxEnqueue = [] := by
  have empty := (complete_rejected_empty (fields := fields) (input := rejected)
    (code := .releaseMismatch) (by decide)).2
  simpa [EffectPlan.empty] using congrArg (fun plan => plan.externalOutboxEnqueue) empty
'''
    assert expected[0] == ["VERDICT", "RELEASE_MISMATCH"]
    _probe(lean, "EffectPlanRejectedNoop", body)


def test_paired_issue_burn_preserves_net_but_fails_projection(
    lean: LeanSubject,
) -> None:
    captured_path = lean.source / "Proofs" / f"{MODULE}.lean"
    original_path = PROJECT / "Proofs" / f"{MODULE}.lean"
    original_bytes = original_path.read_bytes()
    assert captured_path.read_bytes() == original_bytes
    source = captured_path.read_text()
    conservation_block_match = re.search(
        r"^def conservationRow .*?(?=^/-- The runtime omits)",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert conservation_block_match is not None
    conservation_block = conservation_block_match.group(0)
    issue_needle = "    authorizedIssueAtoms := 0"
    burn_needle = "    authorizedBurnAtoms := 0"
    assert conservation_block.count(issue_needle) == 1
    assert conservation_block.count(burn_needle) == 1
    mutated_block = conservation_block.replace(issue_needle, "    authorizedIssueAtoms := 1", 1)
    mutated_block = mutated_block.replace(burn_needle, "    authorizedBurnAtoms := 1", 1)
    mutated = source.replace(conservation_block, mutated_block, 1)

    theorem_blocks = list(re.finditer(
        r"^theorem (\w+).*?(?=^theorem \w+|^end AssetTransferEffectPlanV1$)",
        mutated, flags=re.MULTILINE | re.DOTALL,
    ))
    target = next(block for block in theorem_blocks if block.group(1) == "selectedPlan_projection")
    first_theorem = theorem_blocks[0]
    prefix = mutated[:first_theorem.start()]
    prefix += r'''
def mutantPre : GlobalState := { staticGlobalState with
  balances := [⟨"alice", "USD", "accounts", 40⟩, ⟨"bob", "USD", "accounts", 5⟩]
  supplies := [⟨"USD", 45⟩] }
def mutantInput : Proofs.AssetTransferSparseTablesV1.Input :=
  ⟨⟨"release", "alice"⟩, "release", ⟨"USD", "treasury", 1, true⟩,
    ⟨"asset_transfer", "USD", "alice", "bob", 4, 1⟩, mutantPre⟩
def mutantPlan := selectedPlan ⟨"opaque-pre", "opaque-post", "opaque-occurrence"⟩ mutantInput
open Proofs.CheckedEpochEconomicTablesV1
#eval IO.println (reprStr (reprStr [
  toString mutantPlan.assetConservation.length,
  match mutantPlan.assetConservation with
  | row :: _ => toString row.authorizedIssueAtoms
  | [] => "NONE",
  match mutantPlan.assetConservation with
  | row :: _ => toString row.authorizedBurnAtoms
  | [] => "NONE",
  toString (declaredIssueFor "USD" mutantPlan.assetConservation),
  toString (declaredBurnFor "USD" mutantPlan.assetConservation),
  toString (issuedFor "USD" mutantPlan.rows),
  toString (burnedFor "USD" mutantPlan.rows),
  toString (declaredIssueFor "USD" mutantPlan.assetConservation -
    declaredBurnFor "USD" mutantPlan.assetConservation),
  toString (issuedFor "USD" mutantPlan.rows - burnedFor "USD" mutantPlan.rows)]))

example : NetProjectionMatches mutantPlan := by
  intro asset
  have issueZero : issuedFor asset (S.projectedPlan mutantInput).rows = 0 := by
    simpa [G.issueDeltaFor] using (S.projectedPlan_supply_zero mutantInput asset).1
  have burnZero : burnedFor asset (S.projectedPlan mutantInput).rows = 0 := by
    simpa [G.burnDeltaFor] using (S.projectedPlan_supply_zero mutantInput asset).2
  simp [mutantPlan, selectedPlan, conservationRow,
    declaredIssueFor, declaredBurnFor, issueZero, burnZero]

example : ¬ ProjectionMatches mutantPlan := by
  intro projection
  have issue := (projection "USD").1
  have issueZero : issuedFor "USD" (S.projectedPlan mutantInput).rows = 0 := by
    simpa [G.issueDeltaFor] using (S.projectedPlan_supply_zero mutantInput "USD").1
  simp [mutantPlan, selectedPlan, conservationRow, declaredIssueFor, issueZero] at issue
  exact issue (by rfl)

end AssetTransferEffectPlanV1
end Proofs
'''
    prefix_path = lean.source / "MutantIssueBurnPrefix.lean"
    prefix_path.write_text(prefix)
    prefix_result = _compile(lean, prefix_path)
    assert prefix_result.returncode == 0, prefix_result.stdout + prefix_result.stderr
    assert json.loads(json.loads(prefix_result.stdout.strip())) == [
        "1", "1", "1", "1", "1", "0", "0", "0", "0",
    ]

    full_path = lean.source / "MutantIssueBurn.lean"
    full_path.write_text(mutated)
    full_result = _compile(lean, full_path)
    output = full_result.stdout + full_result.stderr
    assert full_result.returncode != 0
    assert "unexpected token" not in output
    assert "unknown identifier" not in output.lower()
    error_lines = {
        int(line)
        for line in re.findall(rf"{re.escape(str(full_path))}:(\d+):\d+: error:", output)
    }
    first = mutated.count("\n", 0, target.start()) + 1
    following = mutated.count("\n", 0, target.end()) + 1
    assert any(first <= line < following for line in error_lines), output
    assert captured_path.read_bytes() == original_bytes
    assert original_path.read_bytes() == original_bytes
