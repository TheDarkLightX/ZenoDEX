"""Restricted single-occurrence global successor: theorem consumers and runtime controls.

Obligation: the successor of one accepted custody-complete ASSET_TRANSFER transfer, built
from the actual completed result, the admitted occurrence and the private-port commitments,
satisfies all nineteen fields of the existing ``GlobalEconomicStateRefinementV2.Verified``
record from input admission and the actual leaf verdict; a rejected leaf is the exact
global no-op.  The Lean lane compiles the fresh Std-only closure, restates every public
theorem independently, checks axioms, and applies the actual theorems to a nonempty admitted
witness with nonzero custody, a backed liability, a prior replay row and an initial oracle
observation (grade 4).  The runtime lane calls the actual
``transition_asset_transfer_lane_module_custody_v1`` and
``compose_asset_lane_single_v1`` and ``project_single_occurrence_global_effects_v1`` with
synthetic adjacent global metadata and computed private-port roots; expected height,
replay table and balances are input-derived with supplied root commitments (grade 2).
The same opaque roots are fed to the Lean constructor and every modeled field is observed,
with finite registry queries and empty terminal/outbox lists (grade 3).  Independent
guard controls cover a stale occurrence pre-root, replay-key reuse, wrong height,
wrong pre lane root and the fee-owner-sender restriction,
plus the u64 height maximum neighbour and its overflow refusal.  Two constructor mutants,
missing replay insertion and omitted height advance, are killed by the replay relation.

Nonclaims: no whole formal core, no universal Python/Rust/compiler/byte-encoding refinement,
no cryptographic receipt, authenticated snapshot, store head, publication, durability, writer
authorization or production promotion, and no completion of disabled lanes.  The occurrence
identity is opaque in Lean.  The runtime occurrence-ID alias fixture reaches an earlier
context mismatch and does not independently exercise the occurrence-ID reuse guard.
The Lean dual-freshness control covers the model; the independent runtime guard test
remains an evidence gap.  No cryptographic unreachability claim follows from this fixture.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass, replace
from typing import cast

import pytest

from src.core.asset_lane_coordinator_v1 import _normalized_effects, compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
    project_asset_transfer_state_v1,
)
from src.core.asset_transfer_global_allocation_v1 import _global_allocation_binding_reject_v1
from src.core.asset_transfer_lane_module_custody_v1 import (
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
)
from src.core.asset_transfer_types_v1 import (
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_economic_effect_projector_v1 import (
    project_single_occurrence_global_effects_v1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_economic_state_effect_refinement_v1 import _require_fee_mirror_v1
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_U64_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    OracleOccurrenceStateV1,
    ReplayStateV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_annotation_mirrors_v1 import (
    lean as annotation_subject,  # noqa: F401 -- fresh predecessor closure with annotations.
)
from tests.formal.test_lean_asset_transfer_effect_plan_v1 import (
    lean as effect_plan_subject,  # noqa: F401 -- predecessor fixture chain.
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

MODULE = "AssetTransferGlobalSuccessorV1"
NAMESPACE = f"Proofs.{MODULE}"
CUSTODY_MODULE = "AssetTransferCustodyEffectPlanV1"
CUSTODY_NAMESPACE = f"Proofs.{CUSTODY_MODULE}"
POLICY_NAMESPACE = "Proofs.AssetTransferPolicySelectionV1"
GLOBAL_NAMESPACE = "Proofs.GlobalEconomicStateRefinementV2"
CONTEXT_MISMATCH = "economic effect projection occurrence context mismatch"
REPLAY_CONSUMED = "economic effect projection replay identity is already consumed"
LANE_ROOT_MISMATCH = "economic effect projection lane pre-root mismatch"
NOT_MIRRORED = "economic refinement fee allocation is not mirrored"
HEIGHT_OVERFLOW = "occurrence height must fit an unsigned 64-bit integer"
LANE_CODES = {
    LaneIdV1.ASSET_TRANSFER: "assetTransfer", LaneIdV1.SPOT_LIQUIDITY: "spotLiquidity",
    LaneIdV1.FARM_INCENTIVES: "farmIncentives", LaneIdV1.ZDEX_TOKENOMICS: "zdexTokenomics",
    LaneIdV1.ZUSD_MONETARY: "zusdMonetary", LaneIdV1.PERPS_MARKET: "perpsMarket",
    LaneIdV1.ORACLE_MARKET: "oracleMarket", LaneIdV1.SEALED_AUCTION: "sealedAuction",
    LaneIdV1.STRATEGY_ESCROW: "strategyEscrow", LaneIdV1.PROOF_REWARDS: "proofRewards",
    LaneIdV1.EXTERNAL_CUSTODY: "externalCustody",
    LaneIdV1.GOVERNANCE_MIGRATION: "governanceMigration",
}

OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open {POLICY_NAMESPACE}
open {NAMESPACE} (Admitted FeeEligible SingleEnabledLane pre fields result successor
  acceptedWitness successor_verified step_accepted step_rejected_exact successor_metadata
  insertReplay successorRoots)
attribute [local instance] lexOrd
"""

# Public signatures restated independently of the proof source.  The contract test fails if
# the proof surface changes without a matching consumer update.
GLOBAL_INPUT = f"{NAMESPACE}.Input"
THEOREM_TYPES = {
    "successorRoots_self":
        "∀ (state : GlobalState) (root : RootId), successorRoots state root .assetTransfer = root",
    "successorRoots_other":
        "∀ (state : GlobalState) (root : RootId) {lane : LaneId}, lane ≠ .assetTransfer → successorRoots state root lane = state.laneRoots lane",
    "insertReplay_self":
        "∀ (registry : ReplayRegistry) (occurrence : CommandOccurrence), insertReplay registry occurrence occurrence.replayId = some occurrence.occurrenceId",
    "insertReplay_other":
        "∀ (registry : ReplayRegistry) (occurrence : CommandOccurrence) {replayId : Identifier}, replayId ≠ occurrence.replayId → insertReplay registry occurrence replayId = registry replayId",
    "insertReplay_injective":
        "∀ {registry : ReplayRegistry} {occurrence : CommandOccurrence}, (∀ left right occurrenceId, registry left = some occurrenceId → registry right = some occurrenceId → left = right) → (∀ replayId prior, registry replayId = some prior → prior ≠ occurrence.occurrenceId) → ∀ left right occurrenceId, insertReplay registry occurrence left = some occurrenceId → insertReplay registry occurrence right = some occurrenceId → left = right",
    "oracle_within_incremented_height":
        "∀ {state : GlobalState}, OracleRegistryWithinGlobalHeight state → ∀ oracleId occurrence, state.oracleOccurrences oracleId = some occurrence → OracleOccurrenceWithinHeight (state.height + 1) occurrence",
    "quantities_transport":
        "∀ {state : GlobalState}, StateQuantitiesAdmitted state → ∀ (root : RootId) {height : Nat} (roots : LaneId → RootId) {replay : ReplayRegistry}, FitsU64 height → state.height ≤ height → (∀ left right occurrenceId, replay left = some occurrenceId → replay right = some occurrenceId → left = right) → StateQuantitiesAdmitted { state with stateRoot := root, height := height, laneRoots := roots, replayState := replay }",
    "result_verdict":
        f"∀ (input : {GLOBAL_INPUT}), (result input).verdict = (step input.transfer).verdict",
    "result_post":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post = (step input.transfer).post",
    "result_post_frame":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic = {{ pre input with balances := (result input).post.economic.balances }}",
    "result_supplies":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic.supplies = (pre input).supplies",
    "result_custody":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic.custody = (pre input).custody",
    "result_liabilities":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic.liabilities = (pre input).liabilities",
    "result_reserves":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic.reserves = (pre input).reserves",
    "result_terminal":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic.terminalObligations = (pre input).terminalObligations",
    "result_oracle":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic.oracleOccurrences = (pre input).oracleOccurrences",
    "result_height":
        f"∀ (input : {GLOBAL_INPUT}), (result input).post.economic.height = (pre input).height",
    "result_accepted_plan_fields":
        f"∀ {{input : {GLOBAL_INPUT}}}, (step input.transfer).verdict = .accepted → (result input).plan.laneWrites = [⟨.assetTransfer, input.privatePortPreRoot, input.postLaneRoot⟩] ∧ (result input).plan.occurrenceConsumptions = [input.occurrence.occurrenceId] ∧ (result input).plan.externalOutboxEnqueue = []",
    "successor_metadata":
        f"∀ (input : {GLOBAL_INPUT}), (successor input).stateRoot = input.postStateRoot ∧ (successor input).height = (pre input).height + 1 ∧ (successor input).laneRoots .assetTransfer = input.postLaneRoot ∧ (∀ lane, lane ≠ .assetTransfer → (successor input).laneRoots lane = (pre input).laneRoots lane) ∧ (successor input).replayState input.occurrence.replayId = some input.occurrence.occurrenceId ∧ ∀ replayId, replayId ≠ input.occurrence.replayId → (successor input).replayState replayId = (pre input).replayState replayId",
    "successor_fixed_context":
        f"∀ (input : {GLOBAL_INPUT}), FixedContext (pre input) (successor input)",
    "successor_lane_writes":
        f"∀ {{input : {GLOBAL_INPUT}}}, Admitted input → (step input.transfer).verdict = .accepted → ExactLaneWrites (pre input) (successor input) (result input).plan",
    "successor_quantities":
        f"∀ {{input : {GLOBAL_INPUT}}}, Admitted input → StateQuantitiesAdmitted (successor input)",
    "successor_liabilities_backed":
        f"∀ {{input : {GLOBAL_INPUT}}}, Admitted input → ClaimantLiabilitiesBacked (successor input)",
    "successor_annotations":
        f"∀ {{input : {GLOBAL_INPUT}}}, Admitted input → (step input.transfer).verdict = .accepted → AnnotationMirrors (result input).plan",
    "successor_replay":
        f"∀ {{input : {GLOBAL_INPUT}}}, Admitted input → (step input.transfer).verdict = .accepted → ExactReplayRefinement (pre input) (successor input) (result input).plan [input.occurrence]",
    "successor_terminal":
        f"∀ {{input : {GLOBAL_INPUT}}}, Admitted input → (step input.transfer).verdict = .accepted → ExactTerminalRefinement (pre input) (successor input) (result input).plan ⟨[]⟩",
    "successor_oracle":
        f"∀ (input : {GLOBAL_INPUT}), ExactOracleRefinement (pre input) (successor input) (result input).plan ⟨[]⟩",
    "successor_verified":
        f"∀ {{input : {GLOBAL_INPUT}}}, Admitted input → (step input.transfer).verdict = .accepted → Verified (pre input) (result input).plan ⟨[]⟩ ⟨[]⟩ [input.occurrence] (successor input)",
    "step_accepted":
        f"∀ {{input : {GLOBAL_INPUT}}}, (step input.transfer).verdict = .accepted → {NAMESPACE}.step input = ⟨.accepted, successor input, (result input).plan, [input.occurrence]⟩",
    "step_rejected_exact":
        f"∀ {{input : {GLOBAL_INPUT}}} {{code : T.RejectCode}}, (step input.transfer).verdict = .rejected code → {NAMESPACE}.step input = ⟨.rejected code, pre input, EffectPlan.empty, []⟩",
}

# The eighteen input-admission clauses and the nineteen existing witness fields, pinned by
# name so that neither surface can be silently narrowed or widened.
ADMISSION_CLAUSES = (
    "state", "quantities", "owned", "backed", "reservesEmpty", "terminalEmpty", "outboxEmpty",
    "singleLane", "release", "context", "height", "heightFits", "freshReplay",
    "freshOccurrence", "preLaneRoot", "laneRootChanged", "commandWellFormed", "feeEligible",
)
VERIFIED_FIELDS = (
    "fixedContext", "preQuantities", "postQuantities", "effectPlan", "laneWrites",
    "economicTables", "supplyEffects", "conservationCoverage", "conservationRows",
    "annotations", "ownedSupplyPre", "ownedSupplyPost", "liabilitiesPre", "liabilitiesPost",
    "terminal", "oracle", "replay", "outboxClosed", "zeroOccurrence",
)

SOURCE_PINS = {
    "lean-mathlib/Proofs/AssetTransferGlobalSuccessorV1.lean":
        "8375d3cbd6bf4bd4c911527a03de5d12b7bb21df0b0135cd1dd0d1951e60dc56",
    "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean":
        "2ce254367dc8e8299f82f8a93e09c1d470f3a218ed01af7efb766946a34255a4",
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean":
        "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    "lean-mathlib/Proofs/AssetTransferRefinementV1.lean":
        "2d9ed7beb6feb47b67afa63a40d1203bcca9004b49ba978b9927edded6a04932",
    "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean":
        "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "lean-mathlib/Proofs/AssetTransferSparseStateAdmissionV1.lean":
        "82f54f4d5a5ba5e28a2ed2a96cd6b4155e70458c05d104b31eea0717aaae8649",
    "lean-mathlib/Proofs/AssetTransferPolicySelectionV1.lean":
        "6c330fb920885223089d774eaf6110a3007bd2790a3c69dc947f80255edff321",
    "lean-mathlib/Proofs/AssetTransferEffectPlanV1.lean":
        "14cea53d90e1fdc6f068e581dcc8e737526475b323100c5d6c27b9354f769de9",
    "lean-mathlib/Proofs/AssetTransferAnnotationMirrorsV1.lean":
        "81e0fae0addd597b509f7890e4fa8cb1206f6b650414a5db948fcb75633afc30",
    "lean-mathlib/Proofs/AssetTransferCustodyEffectPlanV1.lean":
        "77364c36dbd2f8730ec9683167915b914e2ad9a4aa5a7d9c726e69bf89f8fa23",
    "src/core/asset_transfer_module_v1.py":
        "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py":
        "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/asset_transfer_lane_module_v1.py":
        "7c043b222d4e8aa3d54477ad7508ff65afd716f1b720f76f63995afc4daa7c1a",
    "src/core/asset_transfer_lane_module_custody_v1.py":
        "0d2118f275f6aa5bd308125b83b7c4528dbfc086749c8cb744bacea15983b45e",
    "src/core/asset_lane_projection_v1.py":
        "5420112e2dd321ce7f74604e66c13933ca714fc93467150f5cb6358f403b6839",
    "src/core/asset_lane_coordinator_v1.py":
        "6047468214d835ff9d6d9823d845df4ef0c4a1cd6d94f098911377daaf4996ae",
    "src/core/global_economic_effect_projector_v1.py":
        "35793c70229dd872a5d85d5823b49c3e753384ef5d1200aa3765b50fe132d848",
    "src/core/asset_transfer_global_allocation_v1.py":
        "a4099cb3e53c26ef981e384e92cbdc5c04b80d5bdf7c14cd3b2d296a8830f028",
    "src/core/global_economic_proof_v1.py":
        "f9ff27f3d346c2099ab3678ae87961cbc09653b6c641650ea0db0bf3bac23a50",
    "src/core/global_settlement_types_v1.py":
        "854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4",
    "src/core/global_economic_state_effect_refinement_v1.py":
        "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
}


@pytest.fixture(scope="module")
def lean(annotation_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Compile the frozen custody completion and the successor proof in the fresh closure."""
    for name in (CUSTODY_MODULE, MODULE):
        captured = annotation_subject.source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        imports = re.findall(r"^import (\S+)", captured.read_text(), re.MULTILINE)
        assert all(item.startswith("Proofs.") for item in imports), imports
        result = _compile(
            annotation_subject, captured, annotation_subject.library / "Proofs" / f"{name}.olean",
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return annotation_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _decode(output: str) -> list[list[list[str]]]:
    return [json.loads(json.loads(line)) for line in output.splitlines()]


def _structure_fields(source: str, name: str) -> tuple[str, ...]:
    block = re.search(rf"^structure {name}\b.*?(?=^\S)", source, flags=re.MULTILINE | re.DOTALL)
    assert block is not None, name
    return tuple(re.findall(r"^  (\w+) :", block.group(0), flags=re.MULTILINE))


def test_contract_axioms_placeholders_admission_shape_and_source_pins(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    registrations = (PROJECT / "Proofs.lean").read_text().splitlines()
    assert registrations.count(f"import {NAMESPACE}") == 1
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(THEOREM_TYPES)
    assert _structure_fields(code, "Admitted") == ADMISSION_CLAUSES
    global_source = (PROJECT / "Proofs" / "GlobalEconomicStateRefinementV2.lean").read_text()
    assert _structure_fields(global_source, "Verified") == VERIFIED_FIELDS
    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n"
        f"#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    consumers += (
        f"\nexample : ∀ {{input : {GLOBAL_INPUT}}}, Admitted input → "
        "(step input.transfer).verdict = .accepted → Accepted (pre input) := @acceptedWitness\n"
    )
    report = " ".join(_probe(lean, "GlobalSuccessorConsumers", consumers).split())
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


# ---------------------------------------------------------------------------------------
# Runtime witness: one custody-complete transfer projected into a true adjacent global state.


def _root(value: int) -> str:
    return f"0x{value:064x}"


RELEASE, ASSET_REGISTRY, FEE_REGISTRY = _root(0x11), _root(0x22), _root(0x33)
CHAIN, DEPLOYMENT, PROFILE, HISTORY = "chain", _root(0x44), _root(0x55), _root(0x66)
PRIOR_REPLAY = ReplayStateV1("replay-prior", _root(0x88))
INITIAL_ORACLE = OracleOccurrenceStateV1("oracle-1", _root(0x99), 3, True)
WRITER_EPOCH = 4


@dataclass(frozen=True)
class RuntimeWitness:
    """Everything the runtime lane submits; nothing here is read from runtime output."""

    module_input: AssetTransferLaneModuleInputV1
    pre_global: GlobalEconomicStateV1
    occurrence: EconomicCommandOccurrenceV1
    port_pre_root: str
    liabilities: tuple[EconomicAmountV1, ...]


def _runtime_witness(*, fee_owner: str = "treasury", height: int = 7,
                     amount: int = 4) -> RuntimeWitness:
    policies = (
        AssetTransferPolicyV1("EUR", "eur_treasury", 2, True),
        AssetTransferPolicyV1("USD", fee_owner, 1, True),
    )
    balances = tuple(sorted((
        EconomicAmountV1("alice", "EUR", "accounts", 9),
        EconomicAmountV1("alice", "USD", "accounts", 40),
        EconomicAmountV1("bob", "USD", "accounts", 5),
    ), key=lambda row: row.key))
    supplies = (AssetSupplyV1("EUR", 9), AssetSupplyV1("USD", 55))
    custody = (EconomicAmountV1("vault", "USD", "vault", 10),)
    liabilities = (EconomicAmountV1("claimant", "USD", "vault", 6),)
    pre_state = AssetTransferStateV1(RELEASE, policies, balances, supplies)
    projection = project_asset_transfer_state_v1(
        pre_state, asset_policy_registry_root=ASSET_REGISTRY,
        fee_policy_registry_root=FEE_REGISTRY, custody=custody,
    )
    lane_roots = tuple(
        LaneStateRootV1(
            lane, RELEASE, lane is LaneIdV1.ASSET_TRANSFER,
            projection.state_root if lane is LaneIdV1.ASSET_TRANSFER else _root(0x70 + index),
        )
        for index, lane in enumerate(ALL_LANE_IDS_V1)
    )
    pre_global = GlobalEconomicStateV1(
        chain_id=CHAIN, deployment_root=DEPLOYMENT, writer_epoch=WRITER_EPOCH, height=height,
        profile_root=PROFILE, lane_roots=lane_roots, balances=balances, supplies=supplies,
        custody=custody, liabilities=liabilities, oracle_occurrences=(INITIAL_ORACLE,),
        replay_state=(PRIOR_REPLAY,), history_root=HISTORY,
    )
    command = AssetTransferCommandV1("asset_transfer", "USD", "alice", "bob", amount, 1)
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=CHAIN, deployment_root=DEPLOYMENT, height=height + 1, tx_index=0, op_index=0,
        command_kind="asset_transfer", command_body_hash=command.command_body_hash,
        route_release_id=_root(0xAA), subject_id="alice", grant_root=_root(0xBB), nonce=5,
        profile_root=PROFILE, pre_state_root=pre_global.state_root, consumed_object_ids=(),
    )
    context = AssetTransferContextV1(
        CHAIN, DEPLOYMENT, PROFILE, WRITER_EPOCH, RELEASE, occurrence.occurrence_id, "alice",
        _root(0xBB),
    )
    module_input = AssetTransferLaneModuleInputV1(
        context, pre_state, command, ASSET_REGISTRY, FEE_REGISTRY, custody,
    )
    return RuntimeWitness(module_input, pre_global, occurrence, projection.state_root, liabilities)


def _expected_balances(witness: RuntimeWitness) -> tuple[EconomicAmountV1, ...]:
    command = witness.module_input.command
    policy = next(p for p in witness.module_input.pre_state.policies if p.asset == command.asset)
    values = {row.key: row.amount_atoms for row in witness.module_input.pre_state.balances}
    for owner, delta in (
        (command.sender, -command.amount_atoms - policy.transfer_fee_atoms),
        (command.recipient, command.amount_atoms),
        (policy.fee_owner, policy.transfer_fee_atoms),
    ):
        key = (command.asset, owner, "accounts")
        values[key] = values.get(key, 0) + delta
    return tuple(
        EconomicAmountV1(owner, asset, domain, amount)
        for (asset, owner, domain), amount in sorted(values.items()) if amount
    )


def _run_custody_module(witness: RuntimeWitness) -> AssetTransferLaneModuleAcceptedV1:
    before = canonical_global_bytes_v1(witness.module_input.to_canonical())
    accepted = transition_asset_transfer_lane_module_custody_v1(witness.module_input)
    assert canonical_global_bytes_v1(witness.module_input.to_canonical()) == before
    assert type(accepted) is AssetTransferLaneModuleAcceptedV1
    return accepted


def _normalise(witness: RuntimeWitness,
               accepted: AssetTransferLaneModuleAcceptedV1) -> GlobalEconomicEffectPlanV1:
    """Public composition checks bindings/economics and derives private-port lane roots."""
    port = accepted.private_port
    assert port.pre_state.state_root == witness.port_pre_root
    assert port.pre_state.custody == port.post_state.custody == witness.module_input.custody
    assert port.post_state.balances == _expected_balances(witness)
    normalised = _normalized_effects(port, accepted.effects)
    assert len(normalised.lane_writes) == 1
    write = normalised.lane_writes[0]
    assert write.lane_id is LaneIdV1.ASSET_TRANSFER
    assert write.pre_root == port.pre_state.state_root
    assert write.post_root == port.post_state.state_root
    assert normalised.lane_writes[0].pre_root != accepted.effects.lane_writes[0].pre_root
    assert normalised.occurrence_consumptions == (witness.occurrence.occurrence_id,)
    assert normalised.external_outbox_enqueue == ()
    assert normalised.rows == accepted.effects.rows
    context = AssetLaneCoordinatorContextV1(
        chain_id=witness.pre_global.chain_id,
        deployment_root=witness.pre_global.deployment_root,
        profile_root=witness.pre_global.profile_root,
        writer_epoch=witness.pre_global.writer_epoch,
        coordinator_release_id=RELEASE,
        command_occurrence_id=witness.occurrence.occurrence_id,
        asset_policy_registry_root=ASSET_REGISTRY,
        fee_policy_registry_root=FEE_REGISTRY,
        compatible_modules=(AssetLaneModuleCompatibilityV1(
            accepted.module_journal.module_release_id, port.producer_module_schema,
        ),),
    )
    before = canonical_global_bytes_v1(asdict(accepted))
    composed = compose_asset_lane_single_v1(context, accepted.module_journal, port, accepted.effects)
    assert canonical_global_bytes_v1(asdict(accepted)) == before
    assert type(composed) is AssetLaneCompositionAcceptedV1
    assert composed.effects == normalised
    assert composed.post_state == port.post_state
    assert composed.lane_journal.pre_lane_root == port.pre_state.state_root
    assert composed.lane_journal.post_lane_root == port.post_state.state_root
    assert composed.lane_journal.ordered_module_journal_roots == (accepted.module_journal.journal_root,)
    return composed.effects


def _project(witness: RuntimeWitness, effects: GlobalEconomicEffectPlanV1,
             occurrence: EconomicCommandOccurrenceV1) -> GlobalEconomicStateV1:
    before = canonical_global_bytes_v1(witness.pre_global.to_canonical())
    post = project_single_occurrence_global_effects_v1(witness.pre_global, effects, occurrence)
    assert canonical_global_bytes_v1(witness.pre_global.to_canonical()) == before
    return post


def _expected_post_global(witness: RuntimeWitness, port_post_root: str) -> GlobalEconomicStateV1:
    """Derive tables/metadata from inputs and an explicitly supplied post-root commitment."""
    pre = witness.pre_global
    inserted = ReplayStateV1(witness.occurrence.replay_id, witness.occurrence.occurrence_id)
    return replace(
        pre,
        height=pre.height + 1,
        lane_roots=tuple(
            replace(row, state_root=port_post_root)
            if row.lane_id is LaneIdV1.ASSET_TRANSFER else row for row in pre.lane_roots
        ),
        balances=_expected_balances(witness),
        replay_state=tuple(sorted((*pre.replay_state, inserted), key=lambda row: row.replay_id)),
    )


def _lean_rows(rows: tuple[EconomicAmountV1, ...]) -> str:
    return "[" + ", ".join(
        "⟨" + ", ".join(json.dumps(v) for v in (r.owner, r.asset, r.custody_domain))
        + f", ({r.amount_atoms} : Int)⟩" for r in rows
    ) + "]"


def _lean_supplies(rows: tuple[AssetSupplyV1, ...]) -> str:
    return "[" + ", ".join(f"⟨{json.dumps(r.asset)}, ({r.amount_atoms} : Int)⟩" for r in rows) + "]"


def _lean_policies(rows: tuple[AssetTransferPolicyV1, ...]) -> str:
    return "[" + ", ".join(
        f"⟨{json.dumps(p.asset)}, {json.dumps(p.fee_owner)}, ({p.transfer_fee_atoms} : Int), "
        f"{str(p.enabled).lower()}⟩" for p in rows
    ) + "]"


def _lean_lane_function(values: dict[LaneIdV1, str], name: str, kind: str) -> str:
    arms = "\n".join(f"  | .{LANE_CODES[lane]} => {value}" for lane, value in values.items())
    return f"def {name} : LaneId → {kind}\n{arms}\n"


def _lean_mirror(witness: RuntimeWitness, post_lane_root: str, post_state_root: str,
                 tag: str) -> str:
    """Definitions mirroring the runtime witness with its actual opaque roots."""
    pre, module_input, occurrence = witness.pre_global, witness.module_input, witness.occurrence
    replay_arms = " else ".join(
        f"if replayId = {json.dumps(row.replay_id)} then some {json.dumps(row.occurrence_id)}"
        for row in pre.replay_state
    )
    oracle_arms = " else ".join(
        f"if oracleId = {json.dumps(row.oracle_id)} then some ⟨{json.dumps(row.oracle_id)}, "
        f"{json.dumps(row.occurrence_root)}, {row.observed_height}, "
        f"{'.finalized' if row.finalized else '.pending'}⟩"
        for row in pre.oracle_occurrences
    )
    context = module_input.context
    command = module_input.command
    return (
        _lean_lane_function({row.lane_id: json.dumps(row.state_root) for row in pre.lane_roots},
                            f"{tag}LaneRoots", "RootId")
        + _lean_lane_function({row.lane_id: str(row.enabled).lower() for row in pre.lane_roots},
                              f"{tag}LaneEnabled", "Bool")
        + f"def {tag}Replay : ReplayRegistry := fun replayId => {replay_arms} else none\n"
        + f"def {tag}Oracle : OracleRegistry := fun oracleId => {oracle_arms} else none\n"
        + f"def {tag}Economic : GlobalState :=\n"
        + f"  {{ stateRoot := {json.dumps(pre.state_root)}\n"
        + f"    chainId := {json.dumps(pre.chain_id)}\n"
        + f"    deploymentRoot := {json.dumps(pre.deployment_root)}\n"
        + f"    writerEpoch := {pre.writer_epoch}\n"
        + f"    height := {pre.height}\n"
        + f"    profileRoot := {json.dumps(pre.profile_root)}\n"
        + f"    laneRoots := {tag}LaneRoots\n"
        + f"    laneReleaseIds := fun _ => {json.dumps(RELEASE)}\n"
        + f"    laneEnabled := {tag}LaneEnabled\n"
        + f"    balances := {_lean_rows(pre.balances)}\n"
        + f"    supplies := {_lean_supplies(pre.supplies)}\n"
        + f"    custody := {_lean_rows(pre.custody)}\n"
        + f"    liabilities := {_lean_rows(pre.liabilities)}\n"
        + f"    reserves := {_lean_rows(pre.reserves)}\n"
        + f"    oracleOccurrences := {tag}Oracle\n"
        + f"    replayState := {tag}Replay\n"
        + "    terminalObligations := []\n"
        + f"    historyRoot := {json.dumps(pre.history_root)}\n"
        + "    outbox := [] }\n"
        + f"def {tag}Transfer : Input :=\n"
        + f"  {{ context := ⟨{json.dumps(context.module_release_id)}, "
        + f"{json.dumps(context.subject_id)}⟩\n"
        + f"    command := ⟨{json.dumps(command.command_kind)}, {json.dumps(command.asset)}, "
        + f"{json.dumps(command.sender)}, {json.dumps(command.recipient)}, "
        + f"({command.amount_atoms} : Int), ({command.max_fee_atoms} : Int)⟩\n"
        + f"    pre := {{ moduleReleaseId := {json.dumps(module_input.pre_state.module_release_id)}"
        + f", policies := {_lean_policies(module_input.pre_state.policies)}"
        + f", economic := {tag}Economic }} }}\n"
        + f"def {tag}Occurrence : CommandOccurrence :=\n"
        + f"  ⟨{json.dumps(occurrence.occurrence_id)}, {json.dumps(occurrence.replay_id)}, "
        + f"{json.dumps(occurrence.chain_id)}, {json.dumps(occurrence.deployment_root)}, "
        + f"{json.dumps(occurrence.profile_root)}, {json.dumps(occurrence.pre_state_root)}, "
        + f"{occurrence.height}⟩\n"
        + f"def {tag}Global : {GLOBAL_INPUT} :=\n"
        + f"  ⟨{tag}Transfer, {tag}Occurrence, {json.dumps(witness.port_pre_root)}, "
        + f"{json.dumps(post_lane_root)}, {json.dumps(post_state_root)}⟩\n"
    )


def _lean_admission(tag: str) -> str:
    """Proof text for the fixed three-balance, two-policy, one-custody, one-liability shape."""
    return f"""
theorem {tag}_state_admitted : StateAdmitted {tag}Transfer.pre := by
  refine ⟨?_, ?_, ?_, by decide, ?_⟩
  · unfold S.CanonicalBalances
    refine ⟨?_, ?_, by decide, ?_⟩
    · unfold S.Unique
      decide
    · intro row member
      simp [{tag}Transfer, {tag}Economic] at member
      rcases member with rfl | rfl | rfl <;> decide
    · decide
  · unfold PoliciesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro candidate member
    simp [{tag}Transfer] at member
    rcases member with rfl | rfl <;> decide
  · unfold SuppliesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro supply member
    simp [{tag}Transfer, {tag}Economic] at member
    rcases member with rfl | rfl <;> decide
  · intro queried
    by_cases eur : "EUR" = queried
    · subst queried
      decide
    · by_cases usd : "USD" = queried
      · subst queried
        decide
      · simp [{tag}Transfer, {tag}Economic, amountForAsset, supplyFor, eur, usd]

theorem {tag}_quantities : StateQuantitiesAdmitted {tag}Economic := by
  unfold StateQuantitiesAdmitted
  refine ⟨by simp [{tag}Economic, FitsU64, maxU64], by simp [{tag}Economic, FitsU64, maxU64],
    ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, ?_, by decide,
    by simp [{tag}Economic], ?_, ⟨?_, ?_⟩⟩
  · simp [SparseAmountRowsAdmitted, {tag}Economic, FitsU128, maxU128]
  · simp [SparseSupplyRowsAdmitted, {tag}Economic, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, {tag}Economic, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, {tag}Economic, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, {tag}Economic, FitsU128, maxU128]
  · intro asset
    by_cases eur : "EUR" = asset
    · subst asset
      simp [ownedFor, liabilityFor, amountForAsset, supplyFor, {tag}Economic, FitsU128, maxU128]
    · by_cases usd : "USD" = asset
      · subst asset
        simp [ownedFor, liabilityFor, amountForAsset, supplyFor, {tag}Economic, FitsU128,
          maxU128]
      · simp [ownedFor, liabilityFor, amountForAsset, supplyFor, {tag}Economic, eur, usd,
          FitsU128, maxU128] <;> omega
  · intro left right occurrenceId leftLookup rightLookup
    simp only [{tag}Economic, {tag}Replay] at leftLookup rightLookup
    split at leftLookup <;> split at rightLookup <;> simp_all
  · intro oracleId occurrence lookup
    simp only [{tag}Economic, {tag}Oracle] at lookup
    split at lookup
    · cases lookup
      exact ⟨by simp [FitsU64, maxU64], by decide⟩
    · cases lookup
  · intro oracleId occurrence lookup
    simp only [{tag}Economic, {tag}Oracle] at lookup
    split at lookup
    · rename_i same
      cases lookup
      exact same.symm
    · cases lookup

theorem {tag}_owned : OwnedMatchesSupply {tag}Economic := by
  intro asset
  by_cases eur : "EUR" = asset
  · subst asset
    decide
  · by_cases usd : "USD" = asset
    · subst asset
      decide
    · simp [ownedFor, amountForAsset, supplyFor, {tag}Economic, eur, usd]

theorem {tag}_backed : ClaimantLiabilitiesBacked {tag}Economic := by
  refine ⟨?_, ?_⟩
  · intro asset domain
    by_cases vault : "USD" = asset ∧ "vault" = domain
    · obtain ⟨rfl, rfl⟩ := vault
      decide
    · simp [amountForAssetDomain, {tag}Economic, vault]
  · intro owner asset domain
    simp [openTerminalAmountFor, amountAt, {tag}Economic]
    split <;> omega
"""


def _lean_fee_eligible(tag: str) -> str:
    return f"""
theorem {tag}_fee_eligible : FeeEligible {tag}Global := by
  intro policy selection
  simp [{tag}Global, {tag}Transfer, policyFor] at selection
  subst selection
  exact Or.inr (by decide)
"""


def _lean_fee_ineligible(tag: str) -> str:
    return f"""
theorem {tag}_fee_ineligible : ¬ FeeEligible {tag}Global := by
  intro eligible
  rcases eligible ⟨"USD", "alice", 1, true⟩ (by simp [{tag}Global, {tag}Transfer, policyFor])
    with zero | distinct
  · exact absurd zero (by decide)
  · exact distinct rfl
"""


def _lean_admitted_record(tag: str) -> str:
    return f"""
theorem {tag}_admitted : Admitted {tag}Global where
  state := {tag}_state_admitted
  quantities := {tag}_quantities
  owned := {tag}_owned
  backed := {tag}_backed
  reservesEmpty := rfl
  terminalEmpty := rfl
  outboxEmpty := rfl
  singleLane := by
    intro lane
    cases lane <;> decide
  release := rfl
  context := ⟨rfl, rfl, rfl, rfl⟩
  height := rfl
  heightFits := by simp [pre, {tag}Global, {tag}Transfer, {tag}Economic, FitsU64, maxU64]
  freshReplay := by decide
  freshOccurrence := by
    intro replayId prior lookup
    simp only [pre, {tag}Global, {tag}Transfer, {tag}Economic, {tag}Replay] at lookup
    split at lookup
    · cases lookup
      decide
    · cases lookup
  preLaneRoot := rfl
  laneRootChanged := by decide
  commandWellFormed := ⟨by decide, by decide⟩
  feeEligible := {tag}_fee_eligible
"""


OBSERVERS = f"""
def laneView (state : GlobalState) : List (List String) :=
  allLaneIds.map fun lane => [lane.code, state.laneRoots lane,
    state.laneReleaseIds lane, toString (state.laneEnabled lane)]

def rowsView (rows : List AmountRow) : List (List String) :=
  rows.map fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]

def suppliesView (rows : List SupplyRow) : List (List String) :=
  rows.map fun row => [row.asset, toString row.amountAtoms]

def optionView : Option String → String
  | some value => value
  | none => "NONE"

def oracleView (registry : OracleRegistry) (key : String) : List String :=
  match registry key with
  | none => [key, "NONE"]
  | some occurrence => [key, occurrence.oracleId, occurrence.occurrenceRoot,
      toString occurrence.observedHeight,
      match occurrence.finality with | .finalized => "finalized" | .pending => "pending"]

def occurrenceView (occurrence : CommandOccurrence) : List String :=
  [occurrence.occurrenceId, occurrence.replayId, occurrence.chainId,
   occurrence.deploymentRoot, occurrence.profileRoot, occurrence.preStateRoot,
   toString occurrence.height]

def observeSuccessor (input : {GLOBAL_INPUT}) (replayIds : List String) : List (List String) :=
  let post := successor input
  let out := {NAMESPACE}.step input
  [["HEIGHT", toString post.height], ["STATE_ROOT", post.stateRoot],
   ["WRITER_EPOCH", toString post.writerEpoch], ["CHAIN", post.chainId],
   ["DEPLOYMENT", post.deploymentRoot], ["PROFILE", post.profileRoot],
   ["HISTORY", post.historyRoot], ["OCCURRENCES", toString out.occurrences.length],
   ["TERMINALS", toString post.terminalObligations.length],
   ["OUTBOX", toString post.outbox.length]] ++
  out.occurrences.map occurrenceView ++
  [["ORACLES"], oracleView post.oracleOccurrences "oracle-1",
   oracleView post.oracleOccurrences "oracle-absent"] ++
  [["REPLAY"]] ++ replayIds.map (fun replayId => [replayId, optionView (post.replayState replayId)]) ++
  [["LANES"]] ++ laneView post ++
  [["BALANCES"]] ++ rowsView post.balances ++ [["SUPPLIES"]] ++ suppliesView post.supplies ++
  [["CUSTODY"]] ++ rowsView post.custody ++ [["LIABILITIES"]] ++ rowsView post.liabilities ++
  [["RESERVES"]] ++ rowsView post.reserves
"""


def _expected_observation(post: GlobalEconomicStateV1, replay_ids: list[str],
                          occurrences: tuple[EconomicCommandOccurrenceV1, ...]) -> list[list[str]]:
    replay = {row.replay_id: row.occurrence_id for row in post.replay_state}
    rows = [[r.owner, r.asset, r.custody_domain, str(r.amount_atoms)] for r in post.balances]
    return [
        ["HEIGHT", str(post.height)], ["STATE_ROOT", post.state_root],
        ["WRITER_EPOCH", str(post.writer_epoch)], ["CHAIN", post.chain_id],
        ["DEPLOYMENT", post.deployment_root], ["PROFILE", post.profile_root],
        ["HISTORY", post.history_root], ["OCCURRENCES", str(len(occurrences))],
        ["TERMINALS", str(len(post.terminal_obligations))], ["OUTBOX", str(len(post.outbox))],
        *[[r.occurrence_id, r.replay_id, r.chain_id, r.deployment_root, r.profile_root,
           r.pre_state_root, str(r.height)] for r in occurrences],
        ["ORACLES"],
        *[[r.oracle_id, r.oracle_id, r.occurrence_root, str(r.observed_height),
           "finalized" if r.finalized else "pending"] for r in post.oracle_occurrences],
        ["oracle-absent", "NONE"],
        ["REPLAY"], *[[replay_id, replay.get(replay_id, "NONE")] for replay_id in replay_ids],
        ["LANES"], *[[r.lane_id.value, r.state_root, r.module_release_id, str(r.enabled).lower()]
                     for r in post.lane_roots],
        ["BALANCES"], *rows,
        ["SUPPLIES"], *[[r.asset, str(r.amount_atoms)] for r in post.supplies],
        ["CUSTODY"], *[[r.owner, r.asset, r.custody_domain, str(r.amount_atoms)] for r in post.custody],
        ["LIABILITIES"],
        *[[r.owner, r.asset, r.custody_domain, str(r.amount_atoms)] for r in post.liabilities],
        ["RESERVES"], *[[r.owner, r.asset, r.custody_domain, str(r.amount_atoms)] for r in post.reserves],
    ]


def test_runtime_custody_transfer_projects_to_the_verified_lean_successor(lean: LeanSubject) -> None:
    witness = _runtime_witness()
    accepted = _run_custody_module(witness)
    normalised = _normalise(witness, accepted)
    post = _project(witness, normalised, witness.occurrence)
    expected = _expected_post_global(witness, accepted.private_port.post_state.state_root)
    assert asdict(post) == asdict(expected)
    assert post.height == witness.pre_global.height + 1 == witness.occurrence.height
    assert post.replay_state != witness.pre_global.replay_state
    assert (post.custody, post.liabilities, post.supplies, post.oracle_occurrences) == (
        witness.pre_global.custody, witness.liabilities, witness.pre_global.supplies,
        (INITIAL_ORACLE,),
    )
    assert post.lane_roots[0].state_root != witness.pre_global.lane_roots[0].state_root
    assert post.lane_roots[1:] == witness.pre_global.lane_roots[1:]
    # The restricted route relation accepts the actual adjacent pair.
    assert _global_allocation_binding_reject_v1(
        accepted, witness.occurrence, witness.pre_global, post,
    ) is None
    replay_ids = [witness.occurrence.replay_id, PRIOR_REPLAY.replay_id, "replay-absent"]
    body = (
        _lean_mirror(witness, accepted.private_port.post_state.state_root, post.state_root,
                     "witness")
        + _lean_admission("witness") + _lean_fee_eligible("witness")
        + _lean_admitted_record("witness")
        + f"""
theorem witness_accepted : (step witnessTransfer).verdict = .accepted := by decide

/-- The actual theorem on the mirrored runtime witness: all nineteen fields at once. -/
def witnessAccepted : Accepted (pre witnessGlobal) :=
  acceptedWitness witness_admitted witness_accepted

example : Verified (pre witnessGlobal) (result witnessGlobal).plan ⟨[]⟩ ⟨[]⟩
    [witnessOccurrence] (successor witnessGlobal) :=
  successor_verified witness_admitted witness_accepted

example : witnessAccepted.post = successor witnessGlobal := rfl
example : {NAMESPACE}.step witnessGlobal =
    ⟨.accepted, successor witnessGlobal, (result witnessGlobal).plan, [witnessOccurrence]⟩ :=
  step_accepted witness_accepted
"""
        + OBSERVERS
        + f"#eval IO.println (reprStr (reprStr (observeSuccessor witnessGlobal {json.dumps(replay_ids)})))\n"
    )
    decoded = _decode(_probe(lean, "GlobalSuccessorWitness", body))
    assert decoded == [_expected_observation(post, replay_ids, (witness.occurrence,))]


def test_leaf_rejection_is_the_exact_global_noop(lean: LeanSubject) -> None:
    witness = _runtime_witness(amount=0)
    before = canonical_global_bytes_v1(witness.module_input.to_canonical())
    rejected = transition_asset_transfer_lane_module_custody_v1(witness.module_input)
    assert canonical_global_bytes_v1(witness.module_input.to_canonical()) == before
    assert type(rejected) is AssetTransferRejectedV1
    assert rejected.code.value == "ZERO_AMOUNT"
    assert rejected.effects == GlobalEconomicEffectPlanV1.empty()
    assert rejected.pre_state_root == rejected.post_state_root == witness.module_input.pre_state.state_root
    # No private port, no normalised lane write and no occurrence reach the projector.
    body = _lean_mirror(witness, _root(0xCC), _root(0xDD), "rejected") + f"""
theorem rejected_leaf : (step rejectedTransfer).verdict = .rejected .zeroAmount := by decide

example : {NAMESPACE}.step rejectedGlobal =
    ⟨.rejected .zeroAmount, pre rejectedGlobal, EffectPlan.empty, []⟩ :=
  step_rejected_exact rejected_leaf

example : ({NAMESPACE}.step rejectedGlobal).post.replayState rejectedOccurrence.replayId = none := by
  rw [step_rejected_exact rejected_leaf]
  decide
example : ({NAMESPACE}.step rejectedGlobal).post.height = {witness.pre_global.height} := by
  rw [step_rejected_exact rejected_leaf]
  rfl
example : ({NAMESPACE}.step rejectedGlobal).post.laneRoots .assetTransfer =
    {json.dumps(witness.port_pre_root)} := by
  rw [step_rejected_exact rejected_leaf]
  rfl
example : ({NAMESPACE}.step rejectedGlobal).plan.IsEmpty := by
  rw [step_rejected_exact rejected_leaf]
  exact effectPlan_empty_has_six_empty_fields
"""
    assert _probe(lean, "GlobalSuccessorRejected", body) == ""


def _projection_refusal(witness: RuntimeWitness, effects: GlobalEconomicEffectPlanV1,
                        occurrence: EconomicCommandOccurrenceV1, message: str) -> None:
    pre = witness.pre_global
    before = tuple(canonical_global_bytes_v1(v.to_canonical()) for v in (pre, effects, occurrence))
    with pytest.raises(ValueError) as refusal:
        project_single_occurrence_global_effects_v1(pre, effects, occurrence)
    assert str(refusal.value) == message
    after = tuple(canonical_global_bytes_v1(v.to_canonical()) for v in (pre, effects, occurrence))
    assert after == before


def test_independent_guard_failures_refuse_and_fail_the_matching_admission_clause(
    lean: LeanSubject,
) -> None:
    witness = _runtime_witness()
    accepted = _run_custody_module(witness)
    normalised = _normalise(witness, accepted)
    port_post = accepted.private_port.post_state.state_root
    # Stale occurrence pre-root.
    stale = replace(witness.occurrence, pre_state_root=_root(0xDEAD))
    _projection_refusal(witness, replace(normalised, occurrence_consumptions=(stale.occurrence_id,)),
                        stale, CONTEXT_MISMATCH)
    # Replay-key reuse: the pre state already consumed this replay identity.
    reuse_rows = tuple(sorted(
        (*witness.pre_global.replay_state, ReplayStateV1(witness.occurrence.replay_id, _root(0x77))),
        key=lambda row: row.replay_id,
    ))
    reuse = replace(witness, pre_global=replace(witness.pre_global, replay_state=reuse_rows))
    reuse_occurrence = replace(witness.occurrence, pre_state_root=reuse.pre_global.state_root)
    _projection_refusal(reuse, replace(normalised, occurrence_consumptions=(reuse_occurrence.occurrence_id,)),
                        reuse_occurrence, REPLAY_CONSUMED)
    # Inserting this alias changes the pre root; this fixture reaches the context guard.
    # It supplies no independent runtime evidence for the occurrence-ID reuse guard.
    alias_rows = tuple(sorted(
        (*witness.pre_global.replay_state, ReplayStateV1("replay-zzz", witness.occurrence.occurrence_id)),
        key=lambda row: row.replay_id,
    ))
    alias = replace(witness, pre_global=replace(witness.pre_global, replay_state=alias_rows))
    _projection_refusal(alias, normalised, witness.occurrence, CONTEXT_MISMATCH)
    # Wrong height with a matching consumption so that only the height differs.
    wrong_height = replace(witness.occurrence, height=witness.pre_global.height + 2)
    _projection_refusal(witness, replace(normalised, occurrence_consumptions=(wrong_height.occurrence_id,)),
                        wrong_height, CONTEXT_MISMATCH)
    # Wrong pre lane root.
    wrong_write = replace(normalised.lane_writes[0], pre_root=_root(0xBEEF))
    _projection_refusal(witness, replace(normalised, lane_writes=(wrong_write,)), witness.occurrence,
                        LANE_ROOT_MISMATCH)
    # Fee owner equal to the sender with a positive fee: the leaf accepts, the mirror refuses.
    sender = _runtime_witness(fee_owner="alice")
    sender_accepted = _run_custody_module(sender)
    before_fee = canonical_global_bytes_v1(sender_accepted.effects.to_canonical())
    with pytest.raises(ValueError, match=f"^{NOT_MIRRORED}$"):
        _require_fee_mirror_v1(sender_accepted.effects)
    assert canonical_global_bytes_v1(sender_accepted.effects.to_canonical()) == before_fee
    body = (
        _lean_mirror(witness, port_post, _root(0xEE), "guard")
        + _lean_mirror(sender, sender_accepted.private_port.post_state.state_root, _root(0xEF), "sender")
        + _lean_admission("sender") + _lean_fee_ineligible("sender")
        + f"""
def staleGlobal : {GLOBAL_INPUT} :=
  {{ guardGlobal with occurrence := {{ guardOccurrence with preStateRoot := {json.dumps(_root(0xDEAD))} }} }}
def reuseReplay : ReplayRegistry := fun replayId =>
  if replayId = {json.dumps(witness.occurrence.replay_id)} then some {json.dumps(_root(0x77))}
  else guardReplay replayId
def reuseGlobal : {GLOBAL_INPUT} :=
  {{ guardGlobal with transfer := {{ guardTransfer with
      pre := {{ guardTransfer.pre with economic := {{ guardEconomic with replayState := reuseReplay }} }} }} }}
def aliasReplay : ReplayRegistry := fun replayId =>
  if replayId = "replay-zzz" then some {json.dumps(witness.occurrence.occurrence_id)}
  else guardReplay replayId
def aliasGlobal : {GLOBAL_INPUT} :=
  {{ guardGlobal with transfer := {{ guardTransfer with
      pre := {{ guardTransfer.pre with economic := {{ guardEconomic with replayState := aliasReplay }} }} }} }}
def wrongHeightGlobal : {GLOBAL_INPUT} :=
  {{ guardGlobal with occurrence := {{ guardOccurrence with height := {witness.pre_global.height + 2} }} }}
def wrongRootGlobal : {GLOBAL_INPUT} :=
  {{ guardGlobal with privatePortPreRoot := {json.dumps(_root(0xBEEF))} }}
def sameRootGlobal : {GLOBAL_INPUT} :=
  {{ guardGlobal with postLaneRoot := {json.dumps(witness.port_pre_root)} }}

/-- Each control refutes its named input-admission clause. -/
example : ¬ OccurrenceContextMatches (pre staleGlobal) staleGlobal.occurrence := by
  intro context
  exact absurd context.2.2.2 (by decide)
example : (pre reuseGlobal).replayState reuseGlobal.occurrence.replayId ≠ none := by decide
example : ¬ (∀ replayId prior, (pre aliasGlobal).replayState replayId = some prior →
    prior ≠ aliasGlobal.occurrence.occurrenceId) := by
  intro fresh
  exact fresh "replay-zzz" _ (by decide) rfl
/-- Without that clause the successor registry would alias two keys to one occurrence. -/
example : ¬ ReplayOccurrenceIdsInjective (successor aliasGlobal) := by
  intro injective
  have alias := injective "replay-zzz" aliasGlobal.occurrence.replayId
    aliasGlobal.occurrence.occurrenceId (by decide) (by decide)
  exact absurd alias (by decide)
example : wrongHeightGlobal.occurrence.height ≠ (pre wrongHeightGlobal).height + 1 := by decide
example : wrongRootGlobal.privatePortPreRoot ≠ (pre wrongRootGlobal).laneRoots .assetTransfer := by
  decide
example : ¬ (sameRootGlobal.postLaneRoot ≠ (pre sameRootGlobal).laneRoots .assetTransfer) := by
  decide
/-- The sender-owner fee: the leaf accepts, admission fails, the annotation relation fails. -/
example : (step senderTransfer).verdict = .accepted := by decide
example : ¬ AnnotationMirrors (result senderGlobal).plan := by
  intro mirrors
  obtain ⟨policy, selection, eligible⟩ :=
    ({CUSTODY_NAMESPACE}.complete_annotation_mirrors_iff (fields senderGlobal)
      sender_state_admitted ⟨by decide, by decide⟩ (by decide)).mp mirrors
  simp [senderTransfer, policyFor] at selection
  subst selection
  rcases eligible with zero | distinct
  · exact absurd zero (by decide)
  · exact distinct rfl
"""
    )
    assert _probe(lean, "GlobalSuccessorGuards", body) == ""


def test_malformed_occurrence_is_refused_without_changing_state_or_effects() -> None:
    witness = _runtime_witness()
    accepted = _run_custody_module(witness)
    effects = _normalise(witness, accepted)
    inputs = (witness.pre_global, effects)
    before = tuple(canonical_global_bytes_v1(v.to_canonical()) for v in inputs)
    with pytest.raises(TypeError) as refusal:
        project_single_occurrence_global_effects_v1(
            witness.pre_global, effects, cast(EconomicCommandOccurrenceV1, object()),
        )
    assert str(refusal.value) == "economic effect projection occurrence must be exact typed data"
    assert tuple(canonical_global_bytes_v1(v.to_canonical()) for v in inputs) == before


def test_height_maximum_neighbour_accepts_and_overflow_input_is_refused(lean: LeanSubject) -> None:
    top = _runtime_witness(height=MAX_U64_V1 - 1)
    accepted = _run_custody_module(top)
    normalised = _normalise(top, accepted)
    post = _project(top, normalised, top.occurrence)
    assert post.height == top.occurrence.height == MAX_U64_V1
    assert asdict(post) == asdict(_expected_post_global(top, accepted.private_port.post_state.state_root))
    overflow_pre = replace(top.pre_global, height=MAX_U64_V1)
    with pytest.raises(ValueError, match=f"^{HEIGHT_OVERFLOW}$"):
        replace(top.occurrence, height=MAX_U64_V1 + 1, pre_state_root=overflow_pre.state_root)
    with pytest.raises(ValueError, match="^global state height must fit an unsigned 64-bit integer$"):
        replace(top.pre_global, height=MAX_U64_V1 + 1)
    body = _lean_mirror(top, accepted.private_port.post_state.state_root, _root(0xEE), "top") + f"""
example : (pre topGlobal).height = maxU64 - 1 := by decide
example : FitsU64 ((pre topGlobal).height + 1) := by
  simp [pre, topGlobal, topTransfer, topEconomic, FitsU64, maxU64]
example : (successor topGlobal).height = maxU64 := by
  rw [(successor_metadata topGlobal).2.1]
  decide
def overflowGlobal : {GLOBAL_INPUT} :=
  {{ topGlobal with transfer := {{ topTransfer with
      pre := {{ topTransfer.pre with economic := {{ topEconomic with height := maxU64 }} }} }} }}
/-- The next height leaves u64: the `heightFits` admission clause is refuted. -/
example : ¬ FitsU64 ((pre overflowGlobal).height + 1) := by
  simp [pre, overflowGlobal, topTransfer, topEconomic, FitsU64, maxU64]
"""
    assert _probe(lean, "GlobalSuccessorHeights", body) == ""


MUTANTS = (
    (
        "missing_replay_insertion",
        "    replayState := insertReplay (pre input).replayState input.occurrence }",
        "    replayState := (pre input).replayState }",
        "optionView ((successor probeInput).replayState probeOccurrence.replayId)",
        "NONE",
    ),
    (
        "omitted_height_advance",
        "    height := (pre input).height + 1\n",
        "    height := (pre input).height\n",
        "toString (successor probeInput).height",
        "7",
    ),
)


@pytest.mark.parametrize(("name", "old", "new", "observation", "bad_value"), MUTANTS)
def test_paired_constructor_mutants_are_killed_by_the_replay_relation(
    lean: LeanSubject, name: str, old: str, new: str, observation: str, bad_value: str,
) -> None:
    captured_path = lean.source / "Proofs" / f"{MODULE}.lean"
    original_path = PROJECT / "Proofs" / f"{MODULE}.lean"
    original_bytes = original_path.read_bytes()
    assert captured_path.read_bytes() == original_bytes
    source = captured_path.read_text()
    assert source.count(old) == 1
    mutated = source.replace(old, new, 1)
    theorem_blocks = list(re.finditer(
        r"^theorem (\w+).*?(?=^theorem \w+|^/-- |^def |^end AssetTransferGlobalSuccessorV1$)",
        mutated, flags=re.MULTILINE | re.DOTALL,
    ))
    replay_block = next(block for block in theorem_blocks if block.group(1) == "successor_replay")
    first_theorem = theorem_blocks[0]
    prefix = mutated[:first_theorem.start()] + f"""
def probeOccurrence : G.CommandOccurrence :=
  ⟨"occurrence-new", "replay-new", "chain", "deployment-root", "profile-root", "state-pre", 8⟩
def probeInput : Input :=
  ⟨⟨⟨"release", "alice"⟩, ⟨"asset_transfer", "USD", "alice", "bob", 4, 1⟩,
    ⟨"release", [], {{ staticGlobalState with height := 7 }}⟩⟩,
   probeOccurrence, "lane-pre", "lane-post", "state-post"⟩
def optionView : Option String → String
  | some value => value
  | none => "NONE"
#eval IO.println (reprStr (reprStr [{observation}]))

end AssetTransferGlobalSuccessorV1
end Proofs
"""
    prefix_path = lean.source / f"Mutant_{name}_prefix.lean"
    prefix_path.write_text(prefix)
    prefix_result = _compile(lean, prefix_path)
    assert prefix_result.returncode == 0, prefix_result.stdout + prefix_result.stderr
    assert json.loads(json.loads(prefix_result.stdout.strip())) == [bad_value]

    full_path = lean.source / f"Mutant_{name}.lean"
    full_path.write_text(mutated)
    full_result = _compile(lean, full_path)
    output = full_result.stdout + full_result.stderr
    assert full_result.returncode != 0
    assert "unexpected token" not in output
    assert "unknown identifier" not in output.lower()
    error_lines = {
        int(line) for line in re.findall(rf"{re.escape(str(full_path))}:(\d+):\d+: error:", output)
    }
    first = mutated.count("\n", 0, replay_block.start()) + 1
    following = mutated.count("\n", 0, replay_block.end()) + 1
    assert any(first <= line < following for line in error_lines), output
    assert captured_path.read_bytes() == original_bytes
    assert original_path.read_bytes() == original_bytes
