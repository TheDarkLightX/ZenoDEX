"""Fresh coordinator proofs and exact finite runtime correspondence.

The ten frozen vectors and a mixed accepted/rejected history compare complete
post-state bytes, all fourteen journal fields, all six effect collections, both
source roots, and the domain plus nine-field receipt body. Source observations
are serialized from the actual runtime leaf, independently of the Lean step.

Uninterpreted commitments are instantiated by finite maps keyed by complete
runtime inputs. An unknown key returns a distinct sentinel. This checks exact
values on these vectors; it does not prove arbitrary hashing, parsing, source
authentication, publication, or recovery. Semantic controls use a separate cheap
observer and reuse the existing constructor-admission witness.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from pathlib import Path

import pytest

from src.core.asset_lane_coordinator_values_v2 import (
    AssetLaneCommandV2,
    AssetLaneRejectedV2,
)
from src.core.asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_input_v2 import _decode_context
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_origin_registry_v2 import (
    asset_transfer_policy_root_v2,
    managed_asset_policy_root_v2,
)
from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    AssetTransferAcceptedV2,
    AssetTransferCommandV2,
    AssetTransferRejectedV2,
)
from src.core.global_economic_proof_v2 import LaneModuleTransitionJournalV2
from src.core.global_settlement_abi_v2_codec import (
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
from src.core.global_settlement_types_v2 import (
    LaneIdV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_result_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleRejectedV2,
)
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _root,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_v2 import custody_state
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    WITNESS,
    WITNESS_SHA256,
    _compile_module,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    admission_lean as admission_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    complete_state_lean as complete_state_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    custody_effect_plan_lean as custody_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    custody_structural_lean as custody_structural_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    effect_plan_lean as effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    finite_trace_lean as finite_trace_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    lean as lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    transfer_consumer_lean as transfer_consumer_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    transfer_effect_plan_lean as transfer_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_admission_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    _full_state,
    _managed_context,
)
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    GOLDEN_CASES,
    GOLDEN_FIXTURE,
    GOLDEN_FIXTURE_SHA256,
)
from tests.formal.test_lean_asset_lane_effect_encoding_v2 import _lean_plan
from tests.formal.test_lean_asset_origin_registry_refinement_v2 import (
    CompiledPacket,
    _compile_lean_file,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    _lean_command as _transfer_command_value,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    _lean_context as _transfer_context_value,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    _lean_policy as _transfer_policy_value,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import _lean_string, _wire
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    _lean_command as _managed_command_value,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    _lean_policy as _managed_policy_value,
)

REPO = Path(__file__).resolve().parents[2]
MODULE = "AssetLaneCustodyCoordinatorOutcomeV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = REPO / "lean-mathlib/Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "fb3afba8139d5dce37712cd02d2f21a739d5e01d467689a44a19824b5d88f061"
TRACE = REPO / "lean-mathlib/Proofs/AssetLaneCustodyCoordinatorTraceV2.lean"
TRACE_SHA256 = "db237f62c260b102ed0eb3544a61f35153295a16d065e554702b25a7628c378e"
TRACE_NAMESPACE = "Proofs.AssetLaneCustodyCoordinatorTraceV2"
CONTROLS = REPO / "tests/formal/asset_lane_custody_coordinator_outcome_v2_controls.lean"
CONTROLS_SHA256 = "a263183581797a671103fcedc903f9db9dd84e800b423d1a207dac4e7de1d58d"
CONTROLS_MODULE = "CoordinatorOutcomeSemanticControls"
CONTROLS_NAMESPACE = "CoordinatorOutcomeControls"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b"
RECEIPT_DOMAIN = "asset-lane-custody-coordinator-receipt-v2"

THEOREMS = (
    "completed_accepted_bindings",
    "rejected_is_exact_no_op",
    "rejection_codes_are_route_closed",
    "registry_binding_mismatch_precedes_leaf",
    "leaf_rejection_preserves_route_and_code",
    "missing_occurrence_leaf_verdict",
    "accepted_leaf_has_occurrence",
    "missing_occurrence_is_leaf_rejection",
    "staged_rejection_order",
    "accepted_outcome_is_internally_derived",
    "completed_effects_retain_source_fields",
    "receipt_body_binds_source_and_aggregate_frame",
    "accepted_transfer_outcome",
    "accepted_managed_outcome",
)
TRACE_THEOREMS = (
    "accepted_exposes_checked_frame",
    "transition_preserves_complete_admission",
    "every_prefix_preserves_complete_admission",
)

CONTRACTS = {
    "rejected_is_exact_no_op": """∀ (pre : D.FullState) (code : RejectCode),
      (Outcome.rejected code : Outcome pre).postState = pre ∧
        (Outcome.rejected code : Outcome pre).effects = EffectPlan.empty ∧
        (Outcome.rejected code : Outcome pre).effects.IsEmpty ∧
        (Outcome.rejected code : Outcome pre).route = code.route""",
    "registry_binding_mismatch_precedes_leaf": """∀ (roots : Roots) (commits : Commitments)
      (pre : D.FullState) (action : Input) (source : SourceCandidate)
      (_mismatch : ¬ A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre),
      transition roots commits pre action source =
        .rejected (.coordinator .registryBindingMismatch)""",
    "leaf_rejection_preserves_route_and_code": """∀ (roots : Roots) (commits : Commitments)
      (pre : D.FullState) (action : Input) (source : SourceCandidate) (code : RejectCode)
      (_bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
      (_verdict : leafVerdict roots.digest pre action.leaf = some code),
      transition roots commits pre action source = .rejected code ∧
        code.route = routeOf action.leaf""",
    "completed_effects_retain_source_fields": """∀ (digest : B.Bytes → RootId)
      (pre : D.FullState) (action : F.Action) (source : SourceCandidate),
      (completedEffects digest pre action source).rows = source.effects.rows ∧
        (completedEffects digest pre action source).feeConservation =
          source.effects.feeConservation ∧
        (completedEffects digest pre action source).occurrenceConsumptions =
          source.effects.occurrenceConsumptions ∧
        (completedEffects digest pre action source).externalOutboxEnqueue =
          source.effects.externalOutboxEnqueue ∧
        (completedEffects digest pre action source).assetConservation =
          source.effects.assetConservation.map
            (E.completeConservationRow (D.erase pre) (D.erase (D.step digest pre action))) ∧
        (completedEffects digest pre action source).laneWrites =
          [⟨LaneId.assetTransfer, completeRoot digest pre,
            completeRoot digest (D.step digest pre action)⟩]""",
    "receipt_body_binds_source_and_aggregate_frame": """∀ (route : Route)
      (sourceLeafJournalRoot sourceLeafReceiptRoot leafRoot : RootId) (journal : Journal),
      (sourceLeafJournalRoot ≠ sourceLeafReceiptRoot →
          receiptBody route sourceLeafJournalRoot sourceLeafReceiptRoot journal ≠
            receiptBody route sourceLeafReceiptRoot sourceLeafReceiptRoot journal) ∧
        (journal.preLaneRoot ≠ leafRoot →
          receiptBody route sourceLeafJournalRoot sourceLeafReceiptRoot journal ≠
            receiptBody route sourceLeafJournalRoot sourceLeafReceiptRoot
              { journal with preLaneRoot := leafRoot })""",
}

AUDITED_CONTROLS = (
    "transferLeafAccepted",
    "issueLeafAccepted",
    "burnLeafAccepted",
    "transferPostResources",
    "issuePostResources",
    "burnPostResources",
    "transferRelation",
    "issueRelation",
    "burnRelation",
    "transfer_accepted_controls",
    "issue_accepted_controls",
    "burn_accepted_controls",
    "two_conservation_rows_fail_the_exact_projection",
    "wrong_asset_row_fails_the_exact_projection",
    "stale_source_fields_are_source_mismatches",
    "added_external_outbox_is_a_source_mismatch",
    "source_mismatch_precedes_the_projection_failure",
    "completed_lane_write_is_not_the_leaf_frame",
    "receipt_mutant_body_differs",
    "dropped_managed_row_is_not_the_reprojection",
    "registry_binding_precedes_an_accepting_leaf",
    "zero_state_transfer_is_an_exact_leaf_rejection",
    "mixed_prefix_admission_control",
)


@pytest.fixture(scope="module")
def coordinator_lean(admission_lean: CompiledPacket) -> CompiledPacket:
    _compile_module(admission_lean, SOURCE, f"Proofs/{MODULE}", SOURCE_SHA256)
    _compile_module(admission_lean, TRACE, f"Proofs/{TRACE.stem}", TRACE_SHA256)
    return admission_lean


@pytest.fixture(scope="module")
def coordinator_controls(coordinator_lean: CompiledPacket) -> CompiledPacket:
    _compile_module(coordinator_lean, WITNESS, "AdmissionPositiveWitness", WITNESS_SHA256)
    _compile_module(coordinator_lean, CONTROLS, CONTROLS_MODULE, CONTROLS_SHA256)
    return coordinator_lean


def _consumer(
    packet: CompiledPacket, name: str, code: str, *, extra_import: str | None = None
) -> str:
    path = packet.root / f"{name}.lean"
    path.write_text(
        f"import {TRACE_NAMESPACE}\nimport Lean.Data.Json\n"
        + (f"import {extra_import}\n" if extra_import else "")
        + f"open {NAMESPACE}\nopen Proofs.GlobalSettlementCoreV2\n"
        + "set_option warningAsError true\nset_option maxRecDepth 100000\n"
        + code
    )
    result = _compile_lean_file(packet, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _audit_axioms(output: str, count: int) -> None:
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    assert {a.strip() for g in groups for a in g.split(",") if a.strip()} <= STANDARD_AXIOMS
    assert len(groups) + output.count("does not depend on any axioms") == count


def test_coordinator_and_trace_contracts(coordinator_lean: CompiledPacket) -> None:
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}" for name, signature in CONTRACTS.items()
    )
    for path, names, namespace in (
        (SOURCE, THEOREMS, NAMESPACE),
        (TRACE, TRACE_THEOREMS, TRACE_NAMESPACE),
    ):
        source = path.read_text()
        assert tuple(re.findall(r"^theorem\s+(\w+)", source, re.MULTILINE)) == names
        assert re.search(FORBIDDEN, re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)) is None
        body += "\n" + "\n".join(f"#print axioms {namespace}.{name}" for name in names)
    output = _consumer(coordinator_lean, "CoordinatorContracts", body)
    _audit_axioms(output, len(THEOREMS) + len(TRACE_THEOREMS))


def test_semantic_controls_use_only_standard_axioms(coordinator_controls: CompiledPacket) -> None:
    source = CONTROLS.read_text()
    assert re.search(FORBIDDEN, re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)) is None
    output = _consumer(
        coordinator_controls,
        "CoordinatorControlAxioms",
        "\n".join(f"#print axioms {CONTROLS_NAMESPACE}.{name}" for name in AUDITED_CONTROLS),
        extra_import=CONTROLS_MODULE,
    )
    _audit_axioms(output, len(AUDITED_CONTROLS))


@dataclass(frozen=True)
class RuntimeCase:
    context: AssetLaneContextV2
    pre: AssetLaneCustodyStateV2
    command: AssetLaneCommandV2
    leaf: (
        AssetTransferAcceptedV2
        | AssetTransferRejectedV2
        | ManagedAssetLifecycleAcceptedV2
        | ManagedAssetLifecycleRejectedV2
    )
    outcome: AssetLaneCustodyAcceptedV2 | AssetLaneRejectedV2

    @property
    def post(self) -> AssetLaneCustodyStateV2:
        return (
            self.outcome.post_state
            if type(self.outcome) is AssetLaneCustodyAcceptedV2
            else self.pre
        )


def _run_case(context, pre, command) -> RuntimeCase:
    original = canonical_global_bytes_v2(pre.to_canonical())
    leaf = (
        transition_asset_transfer_v2(context.transfer_context(), pre.transfer_state, command)
        if type(command) is AssetTransferCommandV2
        else transition_managed_asset_lifecycle_v2(
            context.managed_context(), pre.managed_leaf_state(), command
        )
    )
    outcome = transition_asset_lane_custody_v2(context, pre, command)
    assert canonical_global_bytes_v2(pre.to_canonical()) == original
    return RuntimeCase(context, pre, command, leaf, outcome)


def _output(case: RuntimeCase) -> dict:
    outcome = case.outcome
    shared = {"route": outcome.route.value, "effects": outcome.effects.to_canonical()}
    if type(outcome) is AssetLaneCustodyAcceptedV2:
        return shared | {
            "status": "ACCEPTED",
            "post_state": outcome.post_state.to_canonical(),
            "module_journal": outcome.module_journal.to_canonical(),
            "source_leaf_journal_root": outcome.source_leaf_journal_root,
            "source_leaf_receipt_root": outcome.source_leaf_receipt_root,
        }
    assert type(outcome) is AssetLaneRejectedV2
    return shared | {
        "status": "REJECTED",
        "code": outcome.code.value,
        "pre_state_root": outcome.pre_state_root,
        "post_state_root": outcome.post_state_root,
    }


def _journal(journal: LaneModuleTransitionJournalV2) -> str:
    assert journal.lane_id is LaneIdV2.ASSET_TRANSFER
    fields = (
        _lean_string(journal.chain_id),
        _lean_string(journal.deployment_root),
        _lean_string(journal.profile_root),
        str(journal.writer_epoch),
        "LaneId.assetTransfer",
        *map(
            _lean_string,
            (
                journal.module_release_id,
                journal.command_occurrence_id,
                journal.pre_lane_root,
                journal.post_lane_root,
                journal.effect_plan_root,
                journal.private_port_root,
                journal.receipt_root,
                journal.terminal_obligations_root,
                journal.oracle_occurrence_plan_root,
            ),
        ),
    )
    assert len(fields) == 14
    return "⟨" + ", ".join(fields) + "⟩"


def _receipt_body(outcome: AssetLaneCustodyAcceptedV2) -> str:
    journal = outcome.module_journal
    fields = (
        outcome.route.value,
        outcome.source_leaf_journal_root,
        outcome.source_leaf_receipt_root,
        journal.pre_lane_root,
        journal.post_lane_root,
        journal.effect_plan_root,
        journal.private_port_root,
        journal.terminal_obligations_root,
        journal.oracle_occurrence_plan_root,
    )
    assert len(fields) == 9
    return "⟨" + ", ".join(map(_lean_string, fields)) + "⟩"


def _lookup(name: str, typ: str, entries: list[tuple[str, str]]) -> str:
    """Bind complete input literals, detecting conflicting bindings and misses."""
    unique: dict[str, str] = {}
    for key, value in entries:
        assert key not in unique or unique[key] == value, f"conflicting {name} binding"
        unique[key] = value
    expression = _lean_string(f"UNMAPPED:{name}")
    for key, value in reversed(tuple(unique.items())):
        expression = f"if value = ({key} : {typ}) then {_lean_string(value)} else {expression}"
    return f"def {name} (value : {typ}) : String := {expression}"


def _commitments(cases: list[RuntimeCase]) -> str:
    states: list[tuple[str, str]] = []
    plans: list[tuple[str, str]] = []
    journals: list[tuple[str, str]] = []
    receipts: list[tuple[str, str]] = []
    transfers: list[tuple[str, str]] = []
    managed: list[tuple[str, str]] = []
    for case in cases:
        leaf_pre = (
            case.pre.transfer_state
            if type(case.command) is AssetTransferCommandV2
            else case.pre.managed_leaf_state()
        )
        values = [case.pre, case.post, leaf_pre]
        leaf = case.leaf
        if type(leaf) in (AssetTransferAcceptedV2, ManagedAssetLifecycleAcceptedV2):
            values.append(leaf.post_state)
            plans.append((_lean_plan(leaf.effects), leaf.effects.effect_plan_root))
            journals.append((_journal(leaf.module_journal), leaf.module_journal.journal_root))
        for state in values:
            literal = "Proofs.AssetLaneFiniteByteAccountingV2.raw " + _lean_string(
                canonical_global_bytes_v2(state.to_canonical()).decode("ascii")
            )
            states.append((literal, state.state_root))
        outcome = case.outcome
        plans.append((_lean_plan(outcome.effects), outcome.effects.effect_plan_root))
        if type(outcome) is AssetLaneCustodyAcceptedV2:
            journals.append((_journal(outcome.module_journal), outcome.module_journal.journal_root))
            receipts.append(
                (
                    f"({_lean_string(RECEIPT_DOMAIN)}, {_receipt_body(outcome)})",
                    outcome.receipt_root,
                )
            )
        transfers.extend(
            (_transfer_policy_value(_wire(p)), asset_transfer_policy_root_v2(p))
            for p in case.pre.transfer_state.policies
        )
        managed.extend(
            (_managed_policy_value(p), managed_asset_policy_root_v2(p))
            for p in case.pre.managed_policies
        )
    definitions = [
        _lookup("digest", "B.Bytes", states),
        _lookup("planCommit", "EffectPlan", plans),
        _lookup("journalCommit", "Journal", journals),
        _lookup("receiptCommit", "String × ReceiptBody", receipts),
        _lookup("transferCommit", "T.Policy", transfers),
        _lookup("managedCommit", "M.Policy", managed),
        'def roots : Roots := ⟨digest, ⟨fun _ => "unused-scalar-root"⟩, '
        "Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots⟩",
        "def commits : Commitments := ⟨planCommit, journalCommit, "
        "(fun domain body => receiptCommit (domain, body)), transferCommit, managedCommit⟩",
        '#eval IO.println (decide (digest [] = "UNMAPPED:digest"))',
    ]
    return "\n".join(definitions)


def _case_definitions(case: RuntimeCase, index: int) -> str:
    context, command = case.context, case.command
    transfer = type(command) is AssetTransferCommandV2
    occurrence = context.occurrence
    assert occurrence is not None
    action = (
        f".transfer ({_transfer_context_value(context.transfer_context())}) ({_transfer_command_value(command)})"
        if transfer
        else f".managed ({_managed_context(context)}) ({_managed_command_value(command)})"
    )
    definitions = [
        f"def pre{index} : D.FullState := {_full_state(case.pre)}",
        f"def action{index} : F.Action := {action}",
        f"def input{index} : Input := ⟨{_lean_string(occurrence.chain_id)}, "
        f"{_lean_string(occurrence.deployment_root)}, {_lean_string(occurrence.profile_root)}, "
        f"{context.writer_epoch}, action{index}⟩",
    ]
    leaf = case.leaf
    if type(leaf) in (AssetTransferAcceptedV2, ManagedAssetLifecycleAcceptedV2):
        source = f"⟨{_journal(leaf.module_journal)}, {_lean_plan(leaf.effects)}⟩"
    else:
        # A rejected leaf never reads the source. Deliberately supply unrelated bytes.
        source = '⟨⟨"absent", "absent", "absent", 0, .assetTransfer, "absent", "absent", '
        source += '"absent", "absent", "absent", "absent", "absent", "absent", "absent"⟩, EffectPlan.empty⟩'
    definitions.extend(
        (
            f"def source{index} : SourceCandidate := {source}",
            f"def outcome{index} := transition roots commits pre{index} input{index} source{index}",
            f"#eval IO.println (decide (finitePlan digest pre{index} action{index} = ({_lean_plan(leaf.effects)} : EffectPlan)))",
            f"#eval IO.println (decide (outcome{index}.effects = ({_lean_plan(case.outcome.effects)} : EffectPlan)))",
            f"#eval IO.println (decide (D.stateBytes outcome{index}.postState = "
            f"Proofs.AssetLaneFiniteByteAccountingV2.raw {_lean_string(canonical_global_bytes_v2(case.post.to_canonical()).decode('ascii'))}))",
        )
    )
    outcome = case.outcome
    if type(outcome) is AssetLaneCustodyAcceptedV2:
        expected = (
            f"⟨Route.{'transfer' if transfer else 'managedLifecycle'}, "
            f"{_lean_string(outcome.source_leaf_journal_root)}, {_lean_string(outcome.source_leaf_receipt_root)}, "
            f"{_full_state(outcome.post_state)}, {_lean_plan(outcome.effects)}, {_journal(outcome.module_journal)}⟩"
        )
        definitions.extend(
            (
                f"#eval IO.println (decide (outcome{index} = .accepted ({expected} : Accepted)))",
                f"#eval IO.println (decide (completedReceiptBody roots commits pre{index} action{index} source{index} = "
                f"({_receipt_body(outcome)} : ReceiptBody)))",
                f"#eval IO.println (decide (commits.receiptRoot receiptDomain "
                f"(completedReceiptBody roots commits pre{index} action{index} source{index}) = {_lean_string(outcome.receipt_root)}))",
            )
        )
    else:
        assert type(outcome) is AssetLaneRejectedV2
        definitions.append(
            f"#eval IO.println (match outcome{index} with\n"
            f"| .rejected code => decide (code.code = {_lean_string(outcome.code.value)} ∧ "
            f"code.route.code = {_lean_string(outcome.route.value)})\n| .accepted _ => false)"
        )
        definitions.append(f"#eval IO.println (decide (outcome{index}.effects = EffectPlan.empty))")
    return "\n".join(definitions)


def _check_runtime_cases(
    packet: CompiledPacket, name: str, cases: list[RuntimeCase], *, history=False
) -> None:
    body = [_commitments(cases)]
    for index, case in enumerate(cases):
        body.append(_case_definitions(case, index))
    if history:
        attempts = ", ".join(f"(input{i}, source{i})" for i in range(len(cases)))
        body.append(f"def attempts := [{attempts}]")
        for length, state in enumerate([cases[0].pre, *(case.post for case in cases)]):
            body.append(
                f"#eval IO.println (decide ({TRACE_NAMESPACE}.execute roots commits pre0 "
                f"(attempts.take {length}) = ({_full_state(state)} : D.FullState)))"
            )
    output = _consumer(packet, name, "\n".join(body))
    expected_count = 1 + sum(
        6 if type(c.outcome) is AssetLaneCustodyAcceptedV2 else 5 for c in cases
    )
    if history:
        expected_count += len(cases) + 1
    assert output.splitlines() == ["true"] * expected_count


def test_frozen_runtime_outcomes_and_complete_lean_correspondence(
    coordinator_lean: CompiledPacket,
) -> None:
    assert hashlib.sha256(GOLDEN_FIXTURE.read_bytes()).hexdigest() == GOLDEN_FIXTURE_SHA256
    assert len(GOLDEN_CASES) == 10
    cases = []
    for golden in GOLDEN_CASES:
        context = _decode_context(canonical_global_bytes_v2(golden["context"]))
        pre = decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(golden["pre_state"]))
        decoder = (
            decode_asset_transfer_command_v2
            if golden["command_type"] == "TRANSFER"
            else decode_managed_asset_lifecycle_command_v2
        )
        case = _run_case(context, pre, decoder(canonical_global_bytes_v2(golden["command"])))
        assert canonical_global_bytes_v2(_output(case)) == canonical_global_bytes_v2(
            golden["output"]
        ), golden["name"]
        cases.append(case)
    assert sum(type(case.outcome) is AssetLaneCustodyAcceptedV2 for case in cases) == 7
    _check_runtime_cases(coordinator_lean, "CoordinatorGoldenOutcomes", cases)


def test_mixed_history_matches_every_complete_runtime_prefix(
    coordinator_lean: CompiledPacket,
) -> None:
    """Alice transfers, a wrong signer is rejected, then authorized issue/burn succeed."""
    commands = [
        _transfer_command(amount_atoms=10),
        _managed_command(amount_atoms=5),
        _managed_command(amount_atoms=5),
        _managed_command(kind="managed_asset_burn", amount_atoms=7),
    ]
    cases = []
    state = custody_state()
    for index, command in enumerate(commands):
        context = _context(command, nonce=index + 1, subject="mallory" if index == 1 else None)
        case = _run_case(context, state, command)
        if index == 1:
            assert type(case.outcome) is AssetLaneRejectedV2
            assert case.outcome.code.value == "UNAUTHORIZED_SUBJECT"
            assert case.outcome.effects.is_empty
            assert case.outcome.pre_state_root == case.outcome.post_state_root == state.state_root
        else:
            assert type(case.outcome) is AssetLaneCustodyAcceptedV2
        cases.append(case)
        state = case.post
    assert [(r.owner, r.amount_atoms) for r in state.transfer_state.balances] == [
        ("alice", 66),
        ("bob", 10),
        ("treasury", 2),
    ]
    assert state.transfer_state.supply_atoms("USD") == 98
    assert state.custody == custody_state().custody
    _check_runtime_cases(coordinator_lean, "CoordinatorMixedHistory", cases, history=True)


def test_compiling_completion_mutants_fail_the_runtime_oracle(coordinator_lean: CompiledPacket) -> None:
    """Both mutants elaborate and preserve state; exact journal/receipt checks fail."""
    command = _transfer_command(amount_atoms=10)
    case = _run_case(_context(command), custody_state(), command)
    assert type(case.outcome) is AssetLaneCustodyAcceptedV2
    prefix = SOURCE.read_text().split("/-- The completed result satisfies", 1)[0]
    assert "def transition " in prefix and "\ntheorem " not in prefix
    mutations = (
        (None, None),
        (
            "preLaneRoot := completeRoot roots.digest pre\n",
            "preLaneRoot := leafPreRoot roots.digest pre action\n",
        ),
        (
            "receiptBody (routeOf action) (commits.journalRoot source.journal)",
            "receiptBody (routeOf action) source.journal.receiptRoot",
        ),
    )
    for index, (old, new) in enumerate(mutations):
        candidate = prefix
        if old is not None:
            assert candidate.count(old) == 1 and new is not None
            candidate = candidate.replace(old, new)
        namespace = f"Proofs.CoordinatorCompletionMutant{index}"
        candidate = candidate.replace(f"namespace {NAMESPACE}", f"namespace {namespace}", 1)
        path = coordinator_lean.root / f"CoordinatorCompletionMutant{index}.lean"
        path.write_text(
            candidate + f"\nend {namespace}\nopen {namespace}\n"
            + "open Proofs.GlobalSettlementCoreV2\nset_option warningAsError true\n"
            + "set_option maxRecDepth 100000\n"
            + _commitments([case]) + "\n" + _case_definitions(case, 0)
        )
        result = _compile_lean_file(coordinator_lean, path)
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stderr == ""
        expected = ["true"] * 7 if index == 0 else ["true"] * 4 + ["false"] * 3
        assert result.stdout.splitlines() == expected


def test_control_fixture_matches_runtime_serializers(
    coordinator_controls: CompiledPacket,
) -> None:
    """The controls fixture is the actual runtime state, contexts and commands."""

    state = custody_state()
    transfer = _transfer_command(amount_atoms=10)
    transfer_context = _context(transfer)
    issue = _managed_command(amount_atoms=2)
    issue_context = _context(issue)
    burn = _managed_command(kind="managed_asset_burn", amount_atoms=2)
    burn_context = _context(burn, nonce=2)
    occurrence = transfer_context.occurrence
    assert occurrence is not None
    body = [
        f"example : AdmissionWitness.pre = ({_full_state(state)}) := by rfl",
        f"example : {CONTROLS_NAMESPACE}.zeroPre = ({_full_state(custody_state(0, 0))}) := by rfl",
        f"example : AdmissionWitness.transferContext = "
        f"({_transfer_context_value(transfer_context.transfer_context())}) := by rfl",
        f"example : AdmissionWitness.transferCommand = "
        f"({_transfer_command_value(transfer)}) := by rfl",
        f"example : AdmissionWitness.issueContext = ({_managed_context(issue_context)}) := by rfl",
        f"example : AdmissionWitness.issueCommand = ({_managed_command_value(issue)}) := by rfl",
        f"example : AdmissionWitness.burnContext = ({_managed_context(burn_context)}) := by rfl",
        f"example : AdmissionWitness.burnCommand = ({_managed_command_value(burn)}) := by rfl",
        f"example : {CONTROLS_NAMESPACE}.chainId = {_lean_string(occurrence.chain_id)} := by rfl",
        f"example : {CONTROLS_NAMESPACE}.writerEpoch = {transfer_context.writer_epoch} := by rfl",
        f"example : {CONTROLS_NAMESPACE}.transferOccurrenceId = "
        f"{_lean_string(occurrence.occurrence_id)} := by rfl",
    ]
    for name, context in (("issue", issue_context), ("burn", burn_context)):
        leaf_occurrence = context.occurrence
        assert leaf_occurrence is not None
        body.append(
            f"example : {CONTROLS_NAMESPACE}.{name}OccurrenceId = "
            f"{_lean_string(leaf_occurrence.occurrence_id)} := by rfl"
        )
    _consumer(
        coordinator_controls,
        "CoordinatorControlFixture",
        "\n".join(body),
        extra_import=CONTROLS_MODULE,
    )
    # The two abstract coordinates are not claimed to be the runtime roots; the
    # golden gate below binds the actual occurrence values instead.
    assert occurrence.deployment_root == _root("deployment")
    assert occurrence.profile_root == _root("profile")
