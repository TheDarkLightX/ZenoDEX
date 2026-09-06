"""Independent consumers for custody-complete transfer effect plans.

The Lean lane consumes the public custody completion model from a fresh Lean
4.27 source closure.  Its independent signatures cover the six plan fields,
the accepted physical projection (balances plus custody), exact table and
conservation relations, and the empty-reserves condition needed to relate the
physical projection to the global owned-supply predicate.

The Python lane calls the public custody transition and the actual global
economic delta/conservation checks.  Expected balances, physical totals,
coverage assets, and fee rows are calculated from the submitted input tables
and command.  Rejections are checked as exact no-ops.  The finite corpus does
not claim a universal Python/Lean refinement, authenticated roots, claimant
settlement, or release authority.  The global checker fixtures use synthetic
enabled lane metadata and height-one snapshots whose lane roots are bound to
the emitted leaf write; they do not claim authenticated adjacent snapshots.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass, replace

import pytest

from src.core.asset_lane_projection_v1 import project_asset_transfer_state_v1
from src.core.asset_transfer_lane_module_custody_v1 import (
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_types_v1 import (
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_economic_state_delta_v1 import (
    _derive_global_economic_state_delta_v1,
)
from src.core.global_economic_state_effect_refinement_v1 import (
    _require_conservation_refinement_v1,
    _require_fee_mirror_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_ATOMS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_annotation_mirrors_v1 import (
    lean as annotation_mirrors_subject,  # noqa: F401 -- fresh predecessor closure.
)
from tests.formal.test_lean_asset_transfer_effect_plan_v1 import (
    lean as effect_plan_subject,  # noqa: F401 -- predecessor fixture dependency.
)
from tests.formal.test_lean_asset_transfer_policy_selection_v1 import (
    lean as policy_selection_subject,  # noqa: F401 -- predecessor fixture dependency.
)
from tests.formal.test_lean_asset_transfer_sparse_state_admission_v1 import (
    lean as state_admission_subject,  # noqa: F401 -- predecessor fixture dependency.
)
from tests.formal.test_lean_asset_transfer_sparse_supply_v1 import (
    lean as supply_subject,  # noqa: F401 -- predecessor fixture dependency.
)
from tests.formal.test_lean_asset_transfer_sparse_tables_v1 import _amounts_term
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
)

MODULE = "AssetTransferCustodyEffectPlanV1"
NAMESPACE = f"Proofs.{MODULE}"
EFFECT_NAMESPACE = "Proofs.AssetTransferEffectPlanV1"
POLICY_NAMESPACE = "Proofs.AssetTransferPolicySelectionV1"
ANNOTATION_NAMESPACE = "Proofs.AssetTransferAnnotationMirrorsV1"

ROOT = "0x" + "01" * 32
DEPLOYMENT_ROOT = "0x" + "02" * 32
PROFILE_ROOT = "0x" + "03" * 32
OCCURRENCE_ROOT = "0x" + "04" * 32
GRANT_ROOT = "0x" + "05" * 32
ASSET_REGISTRY_ROOT = "0x" + "06" * 32
FEE_REGISTRY_ROOT = "0x" + "07" * 32
OTHER_LANE_ROOT = "0x" + "08" * 32
OPAQUE_PRE = "opaque-pre-lane"
OPAQUE_POST = "opaque-post-lane"
OPAQUE_OCCURRENCE = "opaque-occurrence"

# This is an independently written consumer contract.  The source theorem
# set is compared as a set so declaration order remains an implementation
# detail while additions and removals remain review-visible.
THEOREM_TYPES = {
    "completeConservationRow_asset":
        "∀ (pre post : G.GlobalState) (row : AssetConservationRow), (completeConservationRow pre post row).asset = row.asset",
    "completeConservationRow_supply_pre":
        "∀ (pre post : G.GlobalState) (row : AssetConservationRow), (completeConservationRow pre post row).supplyPreAtoms = row.supplyPreAtoms",
    "completeConservationRow_supply_post":
        "∀ (pre post : G.GlobalState) (row : AssetConservationRow), (completeConservationRow pre post row).supplyPostAtoms = row.supplyPostAtoms",
    "completeConservationRow_authorized_issue":
        "∀ (pre post : G.GlobalState) (row : AssetConservationRow), (completeConservationRow pre post row).authorizedIssueAtoms = row.authorizedIssueAtoms",
    "completeConservationRow_authorized_burn":
        "∀ (pre post : G.GlobalState) (row : AssetConservationRow), (completeConservationRow pre post row).authorizedBurnAtoms = row.authorizedBurnAtoms",
    "completePlan_rows":
        "∀ (pre post : G.GlobalState) (plan : EffectPlan), (completePlan pre post plan).rows = plan.rows",
    "completePlan_fee_conservation":
        "∀ (pre post : G.GlobalState) (plan : EffectPlan), (completePlan pre post plan).feeConservation = plan.feeConservation",
    "completePlan_lane_writes":
        "∀ (pre post : G.GlobalState) (plan : EffectPlan), (completePlan pre post plan).laneWrites = plan.laneWrites",
    "completePlan_occurrences":
        "∀ (pre post : G.GlobalState) (plan : EffectPlan), (completePlan pre post plan).occurrenceConsumptions = plan.occurrenceConsumptions",
    "completePlan_outbox":
        "∀ (pre post : G.GlobalState) (plan : EffectPlan), (completePlan pre post plan).externalOutboxEnqueue = plan.externalOutboxEnqueue",
    "completePlan_conservation":
        "∀ (pre post : G.GlobalState) (plan : EffectPlan), (completePlan pre post plan).assetConservation = plan.assetConservation.map (completeConservationRow pre post)",
    "complete_preserves_verdict_post":
        "∀ (fields : CommitmentFields) (input : K.Input), (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).verdict = (E.complete fields input).verdict ∧ (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).post = (E.complete fields input).post",
    "complete_rejected":
        "∀ {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}, (K.step input).verdict = .rejected code → Proofs.AssetTransferCustodyEffectPlanV1.complete fields input = E.complete fields input",
    "complete_rejected_empty":
        "∀ {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}, (K.step input).verdict = .rejected code → (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).post = input.pre ∧ (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan = EffectPlan.empty",
    "complete_rejected_exact":
        "∀ {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}, (K.step input).verdict = .rejected code → Proofs.AssetTransferCustodyEffectPlanV1.complete fields input = ⟨.rejected code, input.pre, EffectPlan.empty⟩",
    "complete_preserves_other_plan_fields":
        "∀ (fields : CommitmentFields) (input : K.Input), (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan.rows = (E.complete fields input).plan.rows ∧ (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan.feeConservation = (E.complete fields input).plan.feeConservation ∧ (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan.laneWrites = (E.complete fields input).plan.laneWrites ∧ (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan.occurrenceConsumptions = (E.complete fields input).plan.occurrenceConsumptions ∧ (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan.externalOutboxEnqueue = (E.complete fields input).plan.externalOutboxEnqueue",
    "complete_accepted_plan":
        "∀ {fields : CommitmentFields} {input : K.Input}, (K.step input).verdict = .accepted → (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan = completePlan input.pre.economic (E.complete fields input).post.economic (E.complete fields input).plan",
    "complete_accepted_exact_relations":
        "∀ {fields : CommitmentFields} {input : K.Input}, K.StateAdmitted input.pre → (K.step input).verdict = .accepted → ExactEconomicTables input.pre.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).post.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan ∧ ExactSupplyEffects input.pre.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).post.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan",
    "complete_effect_plan_admitted":
        "∀ (fields : CommitmentFields) (input : K.Input), K.StateAdmitted input.pre → G.StateQuantitiesAdmitted input.pre.economic → EffectPlanAdmitted (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan",
    "complete_accepted_conservation":
        "∀ {fields : CommitmentFields} {input : K.Input}, K.StateAdmitted input.pre → input.pre.economic.reserves = [] → T.CommandWellFormed input.command → (K.step input).verdict = .accepted → ExactConservationCoverage input.pre.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).post.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan ∧ ConservationRowsMatchState input.pre.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).post.economic (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan",
    "complete_accepted_preserves_owned_supply":
        "∀ {fields : CommitmentFields} {input : K.Input}, K.StateAdmitted input.pre → G.OwnedMatchesSupply input.pre.economic → (K.step input).verdict = .accepted → G.OwnedMatchesSupply (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).post.economic",
    "complete_annotation_mirrors_iff":
        "∀ (fields : CommitmentFields) {input : K.Input}, K.StateAdmitted input.pre → T.CommandWellFormed input.command → (K.step input).verdict = .accepted → (AnnotationMirrors (Proofs.AssetTransferCustodyEffectPlanV1.complete fields input).plan ↔ ∃ policy, K.policyFor input.pre.policies input.command.asset = some policy ∧ (policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender))",
}

# Proof dependencies are checked from the actual checkout.  The proof source
# and Proofs.lean registration are checked separately; the aggregator's full
# digest is owned by the integration packet.
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
    "lean-mathlib/Proofs/AssetTransferFeeMirrorEligibilityV1.lean":
        "03ae7a9c1db3b8355fb2cd3f09206565cee524c3c735855a0af6c5287ecc5a10",
    "lean-mathlib/Proofs/AssetTransferAnnotationMirrorsV1.lean":
        "81e0fae0addd597b509f7890e4fa8cb1206f6b650414a5db948fcb75633afc30",
    "lean-mathlib/Proofs/AssetTransferCustodyEffectPlanV1.lean":
        "77364c36dbd2f8730ec9683167915b914e2ad9a4aa5a7d9c726e69bf89f8fa23",
    "src/core/asset_transfer_lane_module_custody_v1.py":
        "0d2118f275f6aa5bd308125b83b7c4528dbfc086749c8cb744bacea15983b45e",
    "src/core/asset_transfer_lane_module_v1.py":
        "7c043b222d4e8aa3d54477ad7508ff65afd716f1b720f76f63995afc4daa7c1a",
    "src/core/asset_lane_projection_v1.py":
        "5420112e2dd321ce7f74604e66c13933ca714fc93467150f5cb6358f403b6839",
    "src/core/asset_transfer_module_v1.py":
        "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py":
        "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_settlement_types_v1.py":
        "854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4",
    "src/core/global_economic_state_delta_v1.py":
        "5b06120b14176985a2889b81cc784145339b7f72720d7b161c74b296cb4e5634",
    "src/core/global_economic_state_effect_refinement_v1.py":
        "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
}

OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open {POLICY_NAMESPACE}
open {EFFECT_NAMESPACE}
open {ANNOTATION_NAMESPACE}
open {NAMESPACE}
attribute [local instance] lexOrd
"""

# The negative-command boundary intentionally imports the predecessor alone.
# Bringing the custody namespace into that probe would create duplicate `K`,
# `S`, and `T` aliases and hide the point being controlled: the older formal
# leaf accepts a negative amount that the runtime command constructor excludes.
LEGACY_EFFECT_PLAN_OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open {POLICY_NAMESPACE}
open {EFFECT_NAMESPACE}
attribute [local instance] lexOrd
"""


@pytest.fixture(scope="module")
def lean(annotation_mirrors_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Compile the new source after the annotation predecessor closure."""
    captured = annotation_mirrors_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes((PROJECT / "Proofs" / f"{MODULE}.lean").read_bytes())
    imports = re.findall(r"^import (\S+)", captured.read_text(), re.MULTILINE)
    assert all(item.startswith("Proofs.") for item in imports), imports
    result = _compile(
        annotation_mirrors_subject,
        captured,
        annotation_mirrors_subject.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return annotation_mirrors_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _legacy_effect_plan_probe(lean: LeanSubject, name: str, body: str) -> str:
    """Compile an old-effect-plan boundary probe without custody aliases."""
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {EFFECT_NAMESPACE}\n" + LEGACY_EFFECT_PLAN_OPENS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _decode(output: str) -> list[list[list[str]]]:
    return [json.loads(json.loads(line)) for line in output.splitlines()]


@dataclass(frozen=True)
class CustodyVector:
    name: str
    module_input: AssetTransferLaneModuleInputV1
    liabilities: tuple[EconomicAmountV1, ...]
    expected_error: str | None = None


def _amounts(
    values: tuple[tuple[str, str, str, int], ...],
) -> tuple[EconomicAmountV1, ...]:
    return tuple(
        sorted(
            (EconomicAmountV1(owner, asset, domain, atoms)
             for owner, asset, domain, atoms in values),
            key=lambda row: row.key,
        )
    )


def _accounts(values: tuple[tuple[str, str, int], ...]) -> tuple[EconomicAmountV1, ...]:
    return _amounts(tuple((owner, asset, "accounts", atoms) for owner, asset, atoms in values))


def _policies(values: tuple[tuple[str, str, int, bool], ...]) -> tuple[AssetTransferPolicyV1, ...]:
    return tuple(
        sorted(
            (AssetTransferPolicyV1(asset, owner, fee, enabled)
             for asset, owner, fee, enabled in values),
            key=lambda policy: policy.asset,
        )
    )


def _supplies(values: tuple[tuple[str, int], ...]) -> tuple[AssetSupplyV1, ...]:
    return tuple(sorted((AssetSupplyV1(asset, atoms) for asset, atoms in values), key=lambda row: row.asset))


def _vector(
    name: str,
    *,
    policies: tuple[tuple[str, str, int, bool], ...] = (
        ("EUR", "eur_treasury", 0, True),
        ("USD", "usd_treasury", 1, True),
    ),
    balances: tuple[tuple[str, str, int], ...] = (
        ("alice", "EUR", 45),
        ("alice", "USD", 57),
    ),
    custody: tuple[tuple[str, str, str, int], ...] = (
        ("eur-vault", "EUR", "escrow", 55),
        ("usd-vault", "USD", "escrow", 43),
    ),
    supplies: tuple[tuple[str, int], ...] = (("EUR", 100), ("USD", 100)),
    liabilities: tuple[tuple[str, str, str, int], ...] = (
        ("claimant-eur", "EUR", "escrow", 7),
        ("claimant-usd", "USD", "escrow", 5),
    ),
    context_release: str = ROOT,
    subject: str = "alice",
    command_kind: str = "asset_transfer",
    asset: str = "USD",
    sender: str = "alice",
    recipient: str = "bob",
    amount: int = 4,
    max_fee: int = 1,
    expected_error: str | None = None,
) -> CustodyVector:
    context = AssetTransferContextV1(
        "custody-test", DEPLOYMENT_ROOT, PROFILE_ROOT, 1, context_release,
        OCCURRENCE_ROOT, subject, GRANT_ROOT,
    )
    state = AssetTransferStateV1(
        ROOT, _policies(policies), _accounts(balances), _supplies(supplies),
    )
    command = AssetTransferCommandV1(
        command_kind, asset, sender, recipient, amount, max_fee,
    )
    module_input = AssetTransferLaneModuleInputV1(
        context=context,
        pre_state=state,
        command=command,
        asset_policy_registry_root=ASSET_REGISTRY_ROOT,
        fee_policy_registry_root=FEE_REGISTRY_ROOT,
        custody=_amounts(custody),
    )
    return CustodyVector(name, module_input, _amounts(liabilities), expected_error)


def _policy(vector: CustodyVector) -> AssetTransferPolicyV1:
    command = vector.module_input.command
    return next(
        policy for policy in vector.module_input.pre_state.policies
        if policy.asset == command.asset
    )


def _expected_balances(vector: CustodyVector) -> tuple[EconomicAmountV1, ...]:
    module_input = vector.module_input
    policy = _policy(vector)
    command = module_input.command
    values = {
        (row.asset, row.owner): row.amount_atoms
        for row in module_input.pre_state.balances
    }
    events = (
        (command.sender, -command.amount_atoms - policy.transfer_fee_atoms),
        (command.recipient, command.amount_atoms),
        (policy.fee_owner, policy.transfer_fee_atoms),
    )
    for owner, delta in events:
        key = (command.asset, owner)
        values[key] = values.get(key, 0) + delta
    return tuple(
        EconomicAmountV1(owner, asset, "accounts", amount)
        for (asset, owner), amount in sorted(values.items())
        if amount
    )


def _physical_from_input(vector: CustodyVector, asset: str) -> int:
    return sum(
        row.amount_atoms
        for row in (*vector.module_input.pre_state.balances, *vector.module_input.custody)
        if row.asset == asset
    )


def _physical_from_expected_post(vector: CustodyVector, asset: str) -> int:
    return sum(row.amount_atoms for row in _expected_balances(vector) if row.asset == asset) + sum(
        row.amount_atoms for row in vector.module_input.custody if row.asset == asset
    )


def _effect_rows_expected(vector: CustodyVector) -> list[list[str]]:
    policy = _policy(vector)
    command = vector.module_input.command
    deltas: dict[str, int] = {}
    for owner, delta in (
        (command.sender, -command.amount_atoms - policy.transfer_fee_atoms),
        (command.recipient, command.amount_atoms),
        (policy.fee_owner, policy.transfer_fee_atoms),
    ):
        deltas[owner] = deltas.get(owner, 0) + delta
    rows = [
        [EconomicEffectKindV1.ACCOUNT_MOVEMENT.value, owner, command.asset,
         "accounts", str(delta)]
        for owner, delta in deltas.items() if delta
    ]
    if policy.transfer_fee_atoms:
        rows.append([
            EconomicEffectKindV1.FEE_ALLOCATION.value, policy.fee_owner,
            command.asset, "accounts", str(policy.transfer_fee_atoms),
        ])
    rows.sort(key=lambda row: (row[0], row[2], row[1], row[3], row[4]))
    return rows


def _policy_view(policies: tuple[AssetTransferPolicyV1, ...]) -> list[list[str]]:
    return [
        [policy.asset, policy.fee_owner, str(policy.transfer_fee_atoms), str(policy.enabled).lower()]
        for policy in policies
    ]


def _amount_view(rows: tuple[EconomicAmountV1, ...]) -> list[list[str]]:
    return [
        [row.owner, row.asset, row.custody_domain, str(row.amount_atoms)]
        for row in rows
    ]


def _supply_view(supplies: tuple[AssetSupplyV1, ...]) -> list[list[str]]:
    return [[row.asset, str(row.amount_atoms)] for row in supplies]


def _expected_model_view(vector: CustodyVector) -> list[list[str]]:
    module_input = vector.module_input
    pre = module_input.pre_state
    if vector.expected_error is not None:
        post_balances = pre.balances
        rows: list[list[str]] = []
        conservation: list[list[str]] = []
        fee_rows: list[list[str]] = []
        lane_writes: list[list[str]] = []
        occurrences: list[list[str]] = []
        outbox: list[list[str]] = []
        verdict = vector.expected_error
    else:
        policy = _policy(vector)
        post_balances = _expected_balances(vector)
        rows = _effect_rows_expected(vector)
        asset = module_input.command.asset
        supply = next(row.amount_atoms for row in pre.supplies if row.asset == asset)
        conservation = [[
            asset, str(_physical_from_input(vector, asset)),
            str(_physical_from_expected_post(vector, asset)), str(supply), str(supply), "0", "0",
        ]]
        fee_rows = (
            [[asset, str(policy.transfer_fee_atoms), str(policy.transfer_fee_atoms), "0"]]
            if policy.transfer_fee_atoms else []
        )
        lane_writes = [["ASSET_TRANSFER", OPAQUE_PRE, OPAQUE_POST]]
        occurrences = [[OPAQUE_OCCURRENCE]]
        outbox = []
        verdict = "ACCEPTED"
    return [
        ["VERDICT", verdict],
        ["POLICIES"], *_policy_view(pre.policies),
        ["SUPPLIES"], *_supply_view(pre.supplies),
        ["BALANCES"], *_amount_view(post_balances),
        ["CUSTODY"], *_amount_view(module_input.custody),
        ["LIABILITIES"], *_amount_view(vector.liabilities),
        ["RESERVES"],
        ["ROWS"], *rows,
        ["ASSET_CONSERVATION"], *conservation,
        ["FEE_CONSERVATION"], *fee_rows,
        ["LANE_WRITES"], *lane_writes,
        ["OCCURRENCE_CONSUMPTIONS"], *occurrences,
        ["EXTERNAL_OUTBOX_ENQUEUE"], *outbox,
    ]


def _runtime_global_state(
    vector: CustodyVector,
    balances: tuple[EconomicAmountV1, ...],
    *,
    asset_lane_root: str,
    supplies: tuple[AssetSupplyV1, ...] | None = None,
) -> GlobalEconomicStateV1:
    module_input = vector.module_input
    lane_roots = tuple(
        LaneStateRootV1(
            lane,
            module_input.context.module_release_id,
            True,
            asset_lane_root if lane is LaneIdV1.ASSET_TRANSFER else OTHER_LANE_ROOT,
        )
        for lane in ALL_LANE_IDS_V1
    )
    return GlobalEconomicStateV1(
        chain_id=module_input.context.chain_id,
        deployment_root=module_input.context.deployment_root,
        writer_epoch=module_input.context.writer_epoch,
        height=1,
        profile_root=module_input.context.profile_root,
        lane_roots=lane_roots,
        balances=balances,
        supplies=module_input.pre_state.supplies if supplies is None else supplies,
        custody=module_input.custody,
        liabilities=vector.liabilities,
        reserves=(),
    )


def _accepted_result(
    vector: CustodyVector,
) -> AssetTransferLaneModuleAcceptedV1:
    result = transition_asset_transfer_lane_module_custody_v1(vector.module_input)
    assert isinstance(result, AssetTransferLaneModuleAcceptedV1)
    return result


def _assert_rejected_noop(vector: CustodyVector) -> None:
    module_input = vector.module_input
    before = canonical_global_bytes_v1(module_input.to_canonical())
    legacy = transition_asset_transfer_lane_module_v1(module_input)
    result = transition_asset_transfer_lane_module_custody_v1(module_input)
    after = canonical_global_bytes_v1(module_input.to_canonical())
    assert before == after
    assert isinstance(result, AssetTransferRejectedV1)
    assert result == legacy
    assert result.code.value == vector.expected_error
    assert result.pre_state_root == result.post_state_root == module_input.pre_state.state_root
    assert result.effects.rows == ()
    assert result.effects.asset_conservation == ()
    assert result.effects.fee_conservation == ()
    assert result.effects.lane_writes == ()
    assert result.effects.occurrence_consumptions == ()
    assert result.effects.external_outbox_enqueue == ()


def _assert_accepted_observation(vector: CustodyVector) -> AssetTransferLaneModuleAcceptedV1:
    module_input = vector.module_input
    before = canonical_global_bytes_v1(module_input.to_canonical())
    legacy = transition_asset_transfer_lane_module_v1(module_input)
    result = _accepted_result(vector)
    after = canonical_global_bytes_v1(module_input.to_canonical())
    assert before == after
    assert isinstance(legacy, AssetTransferLaneModuleAcceptedV1)
    assert result.post_state.balances == _expected_balances(vector)
    assert result.post_state.policies == module_input.pre_state.policies
    assert result.post_state.supplies == module_input.pre_state.supplies
    assert result.post_state == legacy.post_state
    assert result.effects.rows == legacy.effects.rows
    assert result.effects.fee_conservation == legacy.effects.fee_conservation
    assert result.effects.lane_writes == legacy.effects.lane_writes
    assert result.effects.occurrence_consumptions == legacy.effects.occurrence_consumptions
    assert result.effects.external_outbox_enqueue == legacy.effects.external_outbox_enqueue == ()
    assert result.private_port.pre_state.custody == module_input.custody
    assert result.private_port.post_state.custody == module_input.custody
    row = result.effects.asset_conservation[0]
    assert [
        row.asset, str(row.owned_and_custodied_pre_atoms),
        str(row.owned_and_custodied_post_atoms), str(row.supply_pre_atoms),
        str(row.supply_post_atoms), str(row.authorized_issue_atoms),
        str(row.authorized_burn_atoms),
    ] == _expected_model_view(vector)[
        _expected_model_view(vector).index(["ASSET_CONSERVATION"]) + 1
    ]
    assert row.owned_and_custodied_pre_atoms == _physical_from_input(vector, row.asset)
    assert row.owned_and_custodied_post_atoms == _physical_from_expected_post(vector, row.asset)
    assert row.authorized_issue_atoms == row.authorized_burn_atoms == 0
    expected_rows = _effect_rows_expected(vector)
    assert [
        [item.kind.value, item.principal, item.asset, item.custody_domain, str(item.delta_atoms)]
        for item in result.effects.rows
    ] == expected_rows
    if not module_input.custody:
        assert result == legacy
    return result


OBSERVERS = r'''
def verdictCode : T.Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def policyView (rows : List T.Policy) : List (List String) :=
  rows.map fun policy =>
    [policy.asset, policy.feeOwner, toString policy.transferFeeAtoms,
      toString policy.enabled]

def amountView (rows : List G.AmountRow) : List (List String) :=
  rows.map fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]

def supplyView (rows : List G.SupplyRow) : List (List String) :=
  rows.map fun row => [row.asset, toString row.amountAtoms]

def effectRowsView (rows : List EconomicEffectRow) : List (List String) :=
  rows.map fun row =>
    [row.kind.code, row.principal, row.asset, row.custodyDomain, toString row.deltaAtoms]

def conservationView (rows : List AssetConservationRow) : List (List String) :=
  rows.map fun row =>
    [row.asset, toString row.ownedAndCustodiedPreAtoms,
      toString row.ownedAndCustodiedPostAtoms, toString row.supplyPreAtoms,
      toString row.supplyPostAtoms, toString row.authorizedIssueAtoms,
      toString row.authorizedBurnAtoms]

def feeView (rows : List FeeConservationRow) : List (List String) :=
  rows.map fun row => [row.asset, toString row.feeChargedAtoms,
    toString row.currentAllocationsAtoms, toString row.carriedResidueAtoms]

def laneView (rows : List LaneWrite) : List (List String) :=
  rows.map fun row => [row.laneId.code, row.preRoot, row.postRoot]

def occurrenceView (rows : List RootId) : List (List String) := rows.map fun row => [row]

def outboxView (rows : List ExternalOutboxEnqueue) : List (List String) :=
  rows.map fun row => [row.effectId, row.destinationId, row.payloadHash, row.adapterProfileRoot]

def observe (fields : CommitmentFields) (input : K.Input) : List (List String) :=
  let out := Proofs.AssetTransferCustodyEffectPlanV1.complete fields input
  [["VERDICT", verdictCode out.verdict], ["POLICIES"]] ++
    policyView out.post.policies ++ [["SUPPLIES"]] ++
    supplyView out.post.economic.supplies ++ [["BALANCES"]] ++
    amountView out.post.economic.balances ++ [["CUSTODY"]] ++
    amountView out.post.economic.custody ++ [["LIABILITIES"]] ++
    amountView out.post.economic.liabilities ++ [["RESERVES"]] ++
    amountView out.post.economic.reserves ++ [["ROWS"]] ++
    effectRowsView out.plan.rows ++ [["ASSET_CONSERVATION"]] ++
    conservationView out.plan.assetConservation ++ [["FEE_CONSERVATION"]] ++
    feeView out.plan.feeConservation ++ [["LANE_WRITES"]] ++
    laneView out.plan.laneWrites ++ [["OCCURRENCE_CONSUMPTIONS"]] ++
    occurrenceView out.plan.occurrenceConsumptions ++ [["EXTERNAL_OUTBOX_ENQUEUE"]]
    ++ outboxView out.plan.externalOutboxEnqueue
'''


def _policy_term(policy: AssetTransferPolicyV1) -> str:
    return "⟨" + ",".join(
        (
            json.dumps(policy.asset),
            json.dumps(policy.fee_owner),
            f"({policy.transfer_fee_atoms} : Int)",
            str(policy.enabled).lower(),
        )
    ) + "⟩"


def _policies_term(policies: tuple[AssetTransferPolicyV1, ...]) -> str:
    return "[" + ",".join(_policy_term(policy) for policy in policies) + "]"


def _supplies_term(supplies: tuple[AssetSupplyV1, ...]) -> str:
    return "[" + ",".join(
        f"⟨{json.dumps(supply.asset)},({supply.amount_atoms} : Int)⟩"
        for supply in supplies
    ) + "]"


def _lean_state_term(vector: CustodyVector) -> str:
    module_input = vector.module_input
    pre = module_input.pre_state
    economic = (
        "{ staticGlobalState with balances := " + _amounts_term(pre.balances)
        + ", custody := " + _amounts_term(module_input.custody)
        + ", liabilities := " + _amounts_term(vector.liabilities)
        + ", reserves := []"
        + ", supplies := " + _supplies_term(pre.supplies) + " }"
    )
    return (
        "{ moduleReleaseId := " + json.dumps(pre.module_release_id)
        + ", policies := " + _policies_term(pre.policies)
        + ", economic := " + economic + " }"
    )


def _lean_input_term(vector: CustodyVector) -> str:
    module_input = vector.module_input
    command = module_input.command
    return (
        "{ context := ⟨" + json.dumps(module_input.context.module_release_id) + ","
        + json.dumps(module_input.context.subject_id) + "⟩, command := ⟨"
        + ",".join(
            (
                json.dumps(command.command_kind),
                json.dumps(command.asset),
                json.dumps(command.sender),
                json.dumps(command.recipient),
                f"({command.amount_atoms} : Int)",
                f"({command.max_fee_atoms} : Int)",
            )
        ) + "⟩, pre := " + _lean_state_term(vector) + " }"
    )


def _fields_term() -> str:
    return "⟨" + ",".join(json.dumps(value) for value in (OPAQUE_PRE, OPAQUE_POST, OPAQUE_OCCURRENCE)) + "⟩"


def _corpus() -> tuple[CustodyVector, ...]:
    return (
        _vector("multi_asset_positive_distinct_fee"),
        _vector("zero_fee_custody", asset="EUR", amount=4, max_fee=0),
        _vector(
            "zero_custody_legacy_equality",
            balances=(("alice", "EUR", 100), ("alice", "USD", 100)),
            custody=(),
            supplies=(("EUR", 100), ("USD", 100)),
        ),
        _vector(
            "fee_owner_sender",
            policies=(("EUR", "eur_treasury", 0, True), ("USD", "alice", 1, True)),
        ),
        _vector(
            "fee_owner_recipient",
            policies=(("EUR", "eur_treasury", 0, True), ("USD", "bob", 1, True)),
        ),
        _vector(
            "disabled_policy",
            policies=(("EUR", "eur_treasury", 0, True), ("USD", "usd-treasury", 1, False)),
            expected_error="DISABLED_ASSET",
        ),
        _vector("unknown_asset", asset="GBP", max_fee=0, expected_error="UNKNOWN_ASSET"),
        _vector("command_precedes_unknown_asset", command_kind="other", asset="GBP",
                max_fee=0, expected_error="UNKNOWN_COMMAND"),
        _vector("release_precedes_command_and_asset", context_release=DEPLOYMENT_ROOT,
                command_kind="other", asset="GBP", max_fee=0, expected_error="RELEASE_MISMATCH"),
        _vector("zero_amount", amount=0, expected_error="ZERO_AMOUNT"),
        _vector("fee_limit", max_fee=0, expected_error="FEE_LIMIT_EXCEEDED"),
        _vector("insufficient_balance", amount=60, expected_error="INSUFFICIENT_BALANCE"),
        _vector(
            "u128_total_max_with_custody",
            balances=(("alice", "EUR", 45), ("alice", "USD", MAX_ATOMS_V1 - 1)),
            custody=(("eur-vault", "EUR", "escrow", 55), ("usd-vault", "USD", "escrow", 1)),
            supplies=(("EUR", 100), ("USD", MAX_ATOMS_V1)),
            policies=(("EUR", "eur_treasury", 0, True), ("USD", "usd_treasury", 0, True)),
            amount=1,
            max_fee=0,
        ),
    )


def test_public_custody_transition_matches_input_derived_complete_model(
    lean: LeanSubject,
) -> None:
    cases = _corpus()
    expected = [_expected_model_view(vector) for vector in cases]
    for vector in cases:
        if vector.expected_error is None:
            _assert_accepted_observation(vector)
        else:
            _assert_rejected_noop(vector)
    probes = "\n".join(
        f"#eval IO.println (reprStr (reprStr (observe ({_fields_term()}) "
        f"({_lean_input_term(vector)} : K.Input))))"
        for vector in cases
    )
    assert _decode(_probe(lean, "CustodyEffectRuntimeCorpus", OBSERVERS + probes)) == expected


def test_global_checker_uses_physical_custody_totals_and_excludes_liabilities() -> None:
    vector = _vector("global_physical_totals")
    result = _assert_accepted_observation(vector)
    policy = _policy(vector)
    assert policy.transfer_fee_atoms > 0
    _require_fee_mirror_v1(result.effects)
    pre_projection = project_asset_transfer_state_v1(
        vector.module_input.pre_state,
        asset_policy_registry_root=ASSET_REGISTRY_ROOT,
        fee_policy_registry_root=FEE_REGISTRY_ROOT,
        custody=vector.module_input.custody,
    )
    post_projection = project_asset_transfer_state_v1(
        result.post_state,
        asset_policy_registry_root=ASSET_REGISTRY_ROOT,
        fee_policy_registry_root=FEE_REGISTRY_ROOT,
        custody=vector.module_input.custody,
    )
    # The legacy effect plan's lane write keeps the account-state roots.  The
    # private port separately carries the custody projection roots.
    assert result.effects.lane_writes[0].pre_root == vector.module_input.pre_state.state_root
    assert result.effects.lane_writes[0].post_root == result.post_state.state_root
    assert result.private_port.pre_state.state_root == pre_projection.state_root
    assert result.private_port.post_state.state_root == post_projection.state_root
    pre_global = _runtime_global_state(
        vector, vector.module_input.pre_state.balances,
        asset_lane_root=result.effects.lane_writes[0].pre_root,
    )
    post_global = _runtime_global_state(
        vector, result.post_state.balances,
        asset_lane_root=result.effects.lane_writes[0].post_root,
    )
    delta = _derive_global_economic_state_delta_v1(pre_global, post_global, result.effects, ())
    _require_conservation_refinement_v1(pre_global, post_global, result.effects, delta)
    assert pre_global.custody == post_global.custody == vector.module_input.custody
    assert pre_global.liabilities == post_global.liabilities == vector.liabilities
    assert pre_global.reserves == post_global.reserves == ()
    for asset, declared in (("EUR", 100), ("USD", 100)):
        physical = _physical_from_input(vector, asset)
        assert physical == declared
        liability = sum(row.amount_atoms for row in vector.liabilities if row.asset == asset)
        assert liability > 0
        assert physical + liability > physical
    assert {row.asset for row in result.effects.asset_conservation} == {"USD"}
    assert {row.asset for row in pre_global.supplies} == {"EUR", "USD"}


def test_actual_global_checker_rejects_physical_conservation_row_mutants() -> None:
    """Each mutation reaches the actual conservation guard after exact delta derivation."""
    vector = _vector("physical_conservation_guard_mutants")
    result = _assert_accepted_observation(vector)
    row = result.effects.asset_conservation[0]
    asset = row.asset
    pre_global = _runtime_global_state(
        vector, vector.module_input.pre_state.balances,
        asset_lane_root=result.effects.lane_writes[0].pre_root,
    )
    post_global = _runtime_global_state(
        vector, result.post_state.balances,
        asset_lane_root=result.effects.lane_writes[0].post_root,
    )
    pre_before = asdict(pre_global)
    post_before = asdict(post_global)
    effects_before = asdict(result.effects)
    account_total = sum(
        amount.amount_atoms for amount in vector.module_input.pre_state.balances
        if amount.asset == asset
    )
    custody_total = sum(
        amount.amount_atoms for amount in vector.module_input.custody
        if amount.asset == asset
    )
    liability_total = sum(
        amount.amount_atoms for amount in vector.liabilities if amount.asset == asset
    )
    assert custody_total > 0
    assert liability_total > 0
    assert row.owned_and_custodied_pre_atoms == account_total + custody_total
    assert row.owned_and_custodied_post_atoms == account_total + custody_total

    balances_only = replace(
        row,
        owned_and_custodied_pre_atoms=account_total,
        owned_and_custodied_post_atoms=account_total,
    )
    liabilities_included = replace(
        row,
        owned_and_custodied_pre_atoms=account_total + custody_total + liability_total,
        owned_and_custodied_post_atoms=account_total + custody_total + liability_total,
    )
    unrelated = replace(row, asset="EUR")
    mutants = (
        ("omitted_custody", replace(result.effects, asset_conservation=(balances_only,)),
         "economic refinement conservation state mismatch"),
        ("liabilities_included", replace(result.effects, asset_conservation=(liabilities_included,)),
         "economic refinement conservation state mismatch"),
        ("missing_conservation", replace(result.effects, asset_conservation=()),
         "economic refinement conservation asset set mismatch"),
        ("unrelated_conservation", replace(result.effects, asset_conservation=(unrelated,)),
         "economic refinement conservation asset set mismatch"),
    )
    for name, plan, message in mutants:
        delta = _derive_global_economic_state_delta_v1(pre_global, post_global, plan, ())
        with pytest.raises(ValueError, match=f"^{re.escape(message)}$"):
            _require_conservation_refinement_v1(pre_global, post_global, plan, delta)
        assert plan != result.effects, name
    assert asdict(pre_global) == pre_before
    assert asdict(post_global) == post_before
    assert asdict(result.effects) == effects_before


def test_untouched_asset_supply_mismatch_is_rejected_by_actual_global_checker() -> None:
    vector = _vector("untouched_supply_mismatch")
    result = _assert_accepted_observation(vector)
    mismatched_supplies = _supplies((("EUR", 101), ("USD", 100)))
    pre_global = _runtime_global_state(
        vector, vector.module_input.pre_state.balances,
        asset_lane_root=result.effects.lane_writes[0].pre_root,
        supplies=mismatched_supplies,
    )
    post_global = _runtime_global_state(
        vector, result.post_state.balances,
        asset_lane_root=result.effects.lane_writes[0].post_root,
        supplies=mismatched_supplies,
    )
    delta = _derive_global_economic_state_delta_v1(pre_global, post_global, result.effects, ())
    assert sum(row.amount_atoms for row in pre_global.balances if row.asset == "EUR") + sum(
        row.amount_atoms for row in pre_global.custody if row.asset == "EUR"
    ) == 100
    assert next(row.amount_atoms for row in pre_global.supplies if row.asset == "EUR") == 101
    with pytest.raises(ValueError, match="^economic refinement owned total does not equal supply$"):
        _require_conservation_refinement_v1(pre_global, post_global, result.effects, delta)


def test_positive_sender_fee_remains_refused_by_global_mirror() -> None:
    vector = _vector(
        "sender_fee_global_refusal",
        policies=(("EUR", "eur_treasury", 0, True), ("USD", "alice", 1, True)),
    )
    result = _assert_accepted_observation(vector)
    before = asdict(result.effects)
    with pytest.raises(ValueError, match="^economic refinement fee allocation is not mirrored$"):
        _require_fee_mirror_v1(result.effects)
    assert asdict(result.effects) == before


def test_u128_total_neighbor_is_rejected_at_input_boundary() -> None:
    state = AssetTransferStateV1(
        ROOT,
        _policies((("EUR", "eur_treasury", 0, True), ("USD", "usd_treasury", 0, True))),
        _accounts((("alice", "EUR", 45), ("alice", "USD", MAX_ATOMS_V1))),
        _supplies((("EUR", 100), ("USD", MAX_ATOMS_V1))),
    )
    context = AssetTransferContextV1(
        "custody-test", DEPLOYMENT_ROOT, PROFILE_ROOT, 1, ROOT,
        OCCURRENCE_ROOT, "alice", GRANT_ROOT,
    )
    command = AssetTransferCommandV1("asset_transfer", "USD", "alice", "bob", 1, 0)
    with pytest.raises(ValueError, match="^owned and custodied total must equal supply$"):
        AssetTransferLaneModuleInputV1(
            context, state, command, ASSET_REGISTRY_ROOT, FEE_REGISTRY_ROOT,
            _amounts((("usd-vault", "USD", "escrow", 1), ("eur-vault", "EUR", "escrow", 55))),
        )


def test_nonempty_lean_witness_proves_physical_admission_and_exact_relations(
    lean: LeanSubject,
) -> None:
    body = r'''
namespace NonemptyCustodyWitness

def eurPolicy : T.Policy := ⟨"EUR", "eur-treasury", 0, true⟩
def usdPolicy : T.Policy := ⟨"USD", "usd-treasury", 1, true⟩

def initial : State :=
  { moduleReleaseId := "release"
    policies := [eurPolicy, usdPolicy]
    economic := { staticGlobalState with
      balances := [
        ⟨"alice", "EUR", "accounts", 45⟩,
        ⟨"alice", "USD", "accounts", 57⟩]
      custody := [
        ⟨"eur-vault", "EUR", "escrow", 55⟩,
        ⟨"usd-vault", "USD", "escrow", 43⟩]
      liabilities := [
        ⟨"claimant-eur", "EUR", "escrow", 7⟩,
        ⟨"claimant-usd", "USD", "escrow", 5⟩]
      reserves := []
      supplies := [⟨"EUR", 100⟩, ⟨"USD", 100⟩] } }

def input : K.Input :=
  { context := ⟨"release", "alice"⟩
    command := ⟨"asset_transfer", "USD", "alice", "bob", 4, 1⟩
    pre := initial }

def fields : E.CommitmentFields := ⟨"opaque-pre", "opaque-post", "opaque-occurrence"⟩
def output := Proofs.AssetTransferCustodyEffectPlanV1.complete fields input

theorem initial_admitted : K.StateAdmitted initial := by
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
    intro policy member
    simp [initial] at member
    rcases member with rfl | rfl <;> decide
  · unfold SuppliesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro supply member
    simp [initial] at member
    rcases member with rfl | rfl <;> decide
  · intro asset
    by_cases eur : "EUR" = asset
    · subst asset
      decide
    · by_cases usd : "USD" = asset
      · subst asset
        decide
      · simp [initial, amountForAsset, supplyFor, eur, usd]

theorem initial_quantities : G.StateQuantitiesAdmitted initial.economic := by
  unfold G.StateQuantitiesAdmitted
  refine ⟨by simp [FitsU64, maxU64, initial, staticGlobalState],
    by simp [FitsU64, maxU64, initial, staticGlobalState], ?_, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SparseAmountRowsAdmitted, FitsU128, maxU128, initial, staticGlobalState]
  · simp [SparseSupplyRowsAdmitted, FitsU128, maxU128, initial, staticGlobalState]
  · simp [SparseAmountRowsAdmitted, FitsU128, maxU128, initial, staticGlobalState]
  · simp [SparseAmountRowsAdmitted, FitsU128, maxU128, initial, staticGlobalState]
  · simp [SparseAmountRowsAdmitted, FitsU128, maxU128, initial, staticGlobalState]
  · intro asset
    by_cases eur : "EUR" = asset
    · subst asset
      simp [G.ownedFor, liabilityFor, G.amountForAsset, G.supplyFor, FitsU128, maxU128,
        initial, staticGlobalState]
    · by_cases usd : "USD" = asset
      · subst asset
        simp [G.ownedFor, liabilityFor, G.amountForAsset, G.supplyFor, FitsU128, maxU128,
          initial, staticGlobalState]
      · simp [G.ownedFor, liabilityFor, G.amountForAsset, G.supplyFor, FitsU128, maxU128,
          initial, staticGlobalState, eur, usd]
  · simp [initial, staticGlobalState]
  · simp [initial, staticGlobalState]
  · simp [initial, staticGlobalState, ReplayOccurrenceIdsInjective]
  · simp [initial, staticGlobalState, OracleRegistryAdmitted,
      OracleRegistryWithinGlobalHeight, OracleRegistryKeysMatch]

theorem initial_owned_supply : G.OwnedMatchesSupply initial.economic := by
  intro asset
  by_cases eur : "EUR" = asset
  · subst asset
    simp [G.ownedFor, G.amountForAsset, G.supplyFor, initial, staticGlobalState]
  · by_cases usd : "USD" = asset
    · subst asset
      simp [G.ownedFor, G.amountForAsset, G.supplyFor, initial, staticGlobalState]
    · simp [G.ownedFor, G.amountForAsset, G.supplyFor, initial, staticGlobalState,
        eur, usd]

theorem reserves_empty : initial.economic.reserves = [] := by rfl
example : T.CommandWellFormed input.command := by exact ⟨by decide, by decide⟩
example : (K.step input).verdict = .accepted := by decide
example : EffectPlanAdmitted output.plan :=
  Proofs.AssetTransferCustodyEffectPlanV1.complete_effect_plan_admitted fields input initial_admitted initial_quantities
example :
    ExactEconomicTables initial.economic output.post.economic output.plan ∧
      ExactSupplyEffects initial.economic output.post.economic output.plan :=
  Proofs.AssetTransferCustodyEffectPlanV1.complete_accepted_exact_relations initial_admitted (by decide)
example :
  ExactConservationCoverage initial.economic output.post.economic output.plan ∧
      ConservationRowsMatchState initial.economic output.post.economic output.plan :=
  Proofs.AssetTransferCustodyEffectPlanV1.complete_accepted_conservation initial_admitted reserves_empty
    (by exact ⟨by decide, by decide⟩) (by decide)
example : G.OwnedMatchesSupply output.post.economic :=
  Proofs.AssetTransferCustodyEffectPlanV1.complete_accepted_preserves_owned_supply initial_admitted initial_owned_supply (by decide)
example : AnnotationMirrors output.plan ↔
    ∃ policy, K.policyFor input.pre.policies input.command.asset = some policy ∧
      (policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender) :=
  Proofs.AssetTransferCustodyEffectPlanV1.complete_annotation_mirrors_iff fields initial_admitted (by exact ⟨by decide, by decide⟩)
    (by decide)
#eval IO.println (reprStr (reprStr (
  [["USD_PRE", toString (physicalFor initial.economic "USD")],
   ["USD_POST", toString (physicalFor output.post.economic "USD")],
   ["EUR_PRE", toString (physicalFor initial.economic "EUR")],
   ["PLAN_ROWS", toString output.plan.rows.length],
   ["OPAQUE_PRE", fields.preLaneRoot], ["OPAQUE_POST", fields.postLaneRoot]])))

end NonemptyCustodyWitness
'''
    observed = _probe(lean, "NonemptyCustodyWitness", body)
    assert _decode(observed) == [[
        ["USD_PRE", "100"], ["USD_POST", "100"], ["EUR_PRE", "100"],
        ["PLAN_ROWS", "4"], ["OPAQUE_PRE", "opaque-pre"], ["OPAQUE_POST", "opaque-post"],
    ]]


def test_independent_contract_axioms_registration_and_source_pins(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(THEOREM_TYPES)
    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n"
        f"#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    report = " ".join(_probe(lean, "CustodyIndependentConsumers", consumers).split())
    for name in THEOREM_TYPES:
        found = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
            report,
        )
        assert found, (name, report)
        axioms = {entry.strip() for entry in (found.group(1) or "").split(",") if entry.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)
    assert (PROJECT / "Proofs.lean").read_text().splitlines().count(f"import {NAMESPACE}") == 1
    for path, digest in SOURCE_PINS.items():
        actual = hashlib.sha256((PROJECT.parent / path).read_bytes()).hexdigest()
        assert digest
        assert actual == digest, path


def test_reserve_premise_is_necessary_for_physical_conservation_theorem(
    lean: LeanSubject,
) -> None:
    body = r'''
namespace ReservePremiseCounterexample

def pre : G.GlobalState := { staticGlobalState with
  balances := [⟨"alice", "USD", "accounts", 4⟩]
  custody := [⟨"vault", "USD", "escrow", 5⟩]
  reserves := [⟨"reserve", "USD", "reserve", 1⟩]
  supplies := [⟨"USD", 10⟩] }

def physical : Int := physicalFor pre "USD"
def globalOwned : Int := G.ownedFor pre "USD"

example : physical = 9 := by decide
example : globalOwned = 10 := by decide
example : physical ≠ globalOwned := by decide
example : pre.reserves ≠ [] := by decide

end ReservePremiseCounterexample
'''
    assert _probe(lean, "ReservePremiseCounterexample", body) == ""


def test_negative_command_requires_runtime_constructor_premise(
    lean: LeanSubject,
) -> None:
    """Control the model-only negative-amount path against the runtime constructor."""
    body = r'''
namespace NegativeCommandBoundary

def policy : T.Policy := ⟨"USD", "bob", 1, true⟩

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
    command := ⟨"asset_transfer", "USD", "alice", "bob", -1, 1⟩
    pre := initial }

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

theorem model_accepts : (K.step input).verdict = .accepted := by decide

theorem all_selected_leaf_physical_deltas_zero (owner : String) :
    Proofs.AssetTransferRefinementV1.delta
      (Proofs.AssetTransferSparseTablesV1.localState (selectedInput input policy))
      input.command owner = 0 := by
  by_cases alice : owner = "alice" <;> by_cases bob : owner = "bob" <;>
    simp [Proofs.AssetTransferRefinementV1.delta,
      Proofs.AssetTransferRefinementV1.indicator,
      Proofs.AssetTransferSparseTablesV1.localState, selectedInput,
      input, initial, policy, alice, bob]

theorem command_constructor_premise_fails : ¬ T.CommandWellFormed input.command := by
  intro bound
  have lower := bound.amount.1
  change (0 : Int) ≤ -1 at lower
  omega

end NegativeCommandBoundary
'''
    assert _legacy_effect_plan_probe(lean, "NegativeCommandBoundary", body) == ""
    with pytest.raises(
        ValueError,
        match="^asset transfer command amount must be a non-negative integer$",
    ):
        AssetTransferCommandV1("asset_transfer", "USD", "alice", "bob", -1, 1)


def test_paired_balances_only_source_mutant_is_killed_at_conservation_obligation(
    lean: LeanSubject,
) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    start = source.index("def physicalFor ")
    end = source.index("\ndef completeConservationRow", start)
    original = source[start:end]
    old = "G.amountForAsset state.balances asset + G.amountForAsset state.custody asset"
    new = "G.amountForAsset state.balances asset"
    assert original.count(old) == 1
    mutant = original.replace(
        old,
        new,
        1,
    )
    assert mutant != original
    # Keep the private source clone to the constructor definitions.  The
    # unchanged downstream proof is tested in a separate file so an unrelated
    # bound proof cannot mask the semantic obligation under test.
    first_theorem = source.index("\ntheorem ", end)
    mutated_prefix = source[:start] + mutant + source[end:first_theorem]
    assert mutated_prefix.count("namespace AssetTransferCustodyEffectPlanV1") == 1
    mutated_prefix = mutated_prefix.replace(
        "namespace AssetTransferCustodyEffectPlanV1",
        "namespace AssetTransferCustodyEffectPlanV1Mutant",
        1,
    )
    mutant_definitions = r'''
def mutantState : G.GlobalState := { staticGlobalState with
  balances := [⟨"alice", "USD", "accounts", 57⟩]
  custody := [⟨"vault", "USD", "escrow", 43⟩]
  supplies := [⟨"USD", 100⟩] }

def mutantRow : AssetConservationRow :=
  { asset := "USD"
    ownedAndCustodiedPreAtoms := physicalFor mutantState "USD"
    ownedAndCustodiedPostAtoms := physicalFor mutantState "USD"
    supplyPreAtoms := 100
    supplyPostAtoms := 100
    authorizedIssueAtoms := 0
    authorizedBurnAtoms := 0 }

def mutantPlan : EffectPlan :=
  { EffectPlan.empty with
    assetConservation := [mutantRow] }

example : physicalFor mutantState "USD" = 57 := by decide
example : G.ownedFor mutantState "USD" = 100 := by decide
example : physicalFor mutantState "USD" ≠ G.ownedFor mutantState "USD" := by decide
'''
    mutant_false_relation = r'''
example : ¬ ConservationRowsMatchState mutantState mutantState mutantPlan := by
  intro hmatch
  have mismatch := (hmatch mutantRow (by simp [mutantPlan])).1
  simp [mutantRow, mutantState, physicalFor, G.ownedFor, G.amountForAsset,
    staticGlobalState] at mismatch
'''
    positive_path = lean.source / "PhysicalProjectionMutantPrefix.lean"
    original_control = r'''

namespace OriginalProjectionControl

open Proofs.AssetTransferCustodyEffectPlanV1
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2

def originalState : G.GlobalState := { staticGlobalState with
  balances := [⟨"alice", "USD", "accounts", 57⟩]
  custody := [⟨"vault", "USD", "escrow", 43⟩]
  supplies := [⟨"USD", 100⟩] }

def originalPlan : EffectPlan :=
  { EffectPlan.empty with
    assetConservation := [
      { asset := "USD"
        ownedAndCustodiedPreAtoms := physicalFor originalState "USD"
        ownedAndCustodiedPostAtoms := physicalFor originalState "USD"
        supplyPreAtoms := 100
        supplyPostAtoms := 100
        authorizedIssueAtoms := 0
        authorizedBurnAtoms := 0 } ] }

example : physicalFor originalState "USD" = 100 := by decide
example : ConservationRowsMatchState originalState originalState originalPlan := by
  intro row member
  simp [originalPlan] at member
  subst row
  decide

    end OriginalProjectionControl
'''
    positive_path.write_text(
        f"import {NAMESPACE}\n" + mutated_prefix + mutant_definitions + mutant_false_relation
        + "\nend AssetTransferCustodyEffectPlanV1Mutant\nend Proofs\n"
        + original_control
    )
    result = _compile(lean, positive_path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    # Requiring the unchanged conservation relation on the same mutant fails
    # at the physical-row equality: 57 is exposed while global ownedFor is 100.
    bad_claim = r'''
example : ConservationRowsMatchState mutantState mutantState mutantPlan := by
  intro row member
  simp [mutantPlan] at member
  subst row
  decide
'''
    killed_path = lean.source / "PhysicalProjectionMutantKilled.lean"
    killed_path.write_text(
        mutated_prefix + mutant_definitions + bad_claim
        + "\nend AssetTransferCustodyEffectPlanV1Mutant\nend Proofs\n"
    )
    failure = _compile(lean, killed_path)
    assert failure.returncode != 0
    diagnostic = failure.stdout + failure.stderr
    assert "Tactic `decide` proved that the proposition" in diagnostic
    assert "mutantRow.ownedAndCustodiedPreAtoms = ownedFor mutantState mutantRow.asset" in diagnostic
    assert "is false" in diagnostic
