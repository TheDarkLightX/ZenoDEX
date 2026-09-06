"""Bounded consumers for the two-step global transfer state closure.

The Lean subject carries the actual custody-complete result and the actual global
successor through one accepted transfer, then uses that carried state as the
pre-state of a second fresh transfer.  The second admission is obtained from
``continuedState_invariant`` and ``continuation_admitted``.  A rejected next leaf
is checked as an exact no-op with the same carried state.

The Python witness calls the custody module, public lane coordinator, and global
projector for both accepted transfers.  It compares their rows, lane roots,
height, and replay entries with a small Lean observer.  The fixture keeps roots
opaque and records only selected source pins.  It does not claim executable
admission, universal Python/Rust refinement, cryptographic root security,
publisher authority, or a nonempty terminal/reserve/outbox profile.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict

import pytest

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
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_settlement_types_v1 import (
    MAX_U64_V1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_annotation_mirrors_v1 import (
    lean as annotation_subject,  # noqa: F401 -- predecessor fixture chain.
)
from tests.formal.test_lean_asset_transfer_effect_plan_v1 import (
    lean as effect_plan_subject,  # noqa: F401 -- predecessor fixture chain.
)
from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
    GLOBAL_INPUT,
    PROJECT,
    RuntimeWitness,
    _compile,
    _decode,
    _expected_post_global,
    _lean_admission,
    _lean_admitted_record,
    _lean_fee_eligible,
    _lean_mirror,
    _normalise,
    _project,
    _root,
    _run_custody_module,
    _runtime_witness,
    _structure_fields,
)
from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
    OPENS as SUCCESSOR_OPENS,
)
from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
    SOURCE_PINS as SUCCESSOR_SOURCE_PINS,
)
from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
    lean as successor_subject,  # noqa: F401 -- predecessor fresh-source fixture.
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
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import LeanSubject

MODULE = "AssetTransferGlobalStateClosureV1"
NAMESPACE = f"Proofs.{MODULE}"
SUCCESSOR_NAMESPACE = "Proofs.AssetTransferGlobalSuccessorV1"
GLOBAL_NAMESPACE = "Proofs.GlobalEconomicStateRefinementV2"

# The predecessor fixture supplies the complete Lean dependency closure.  Keep
# these as literal selected pins so a changed dependency cannot silently alter
# the subject consumed by this test.
SOURCE_PINS = {
    "lean-mathlib/Proofs/AssetTransferGlobalStateClosureV1.lean":
        "4569ef906325cf08a0f02cca8932f07735a7dc94a5250f6e612c54e1ef7e0ddb",
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
    "lean-mathlib/Proofs/AssetTransferFeeMirrorEligibilityV1.lean":
        "03ae7a9c1db3b8355fb2cd3f09206565cee524c3c735855a0af6c5287ecc5a10",
    "lean-mathlib/Proofs/AssetTransferSparseAuthorizationV1.lean":
        "91d41486e814f80a876746a1d8a542daeda77599415792b0915f4a2fccc495fa",
    "lean-mathlib/Proofs/AssetTransferCustodyCompositionV1.lean":
        "37375e914576993767eae7484e620e54be300798785b2a57a9953e86be2f34d2",
    "lean-mathlib/Proofs/CanonicalEpochEconomicRowsV1.lean":
        "5ff80f22fde38729468dc237dd5b40a28bacc57302a483bf42b3e9f90122fe64",
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
    "src/core/global_economic_proof_v1.py":
        "f9ff27f3d346c2099ab3678ae87961cbc09653b6c641650ea0db0bf3bac23a50",
    "src/core/global_settlement_types_v1.py":
        "854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4",
}

assert SOURCE_PINS["lean-mathlib/Proofs/AssetTransferGlobalSuccessorV1.lean"] == (
    SUCCESSOR_SOURCE_PINS["lean-mathlib/Proofs/AssetTransferGlobalSuccessorV1.lean"]
)

# Keep the predecessor's selected pins visible for review, while rejecting an
# accidental disagreement if that unchanged fixture map is later edited.
STATE_INVARIANT_FIELDS = (
    "state", "quantities", "owned", "backed", "reservesEmpty", "terminalEmpty",
    "outboxEmpty", "singleLane", "release",
)
CONTINUATION_REQUIREMENT_FIELDS = (
    "pre", "context", "height", "heightFits", "freshReplay", "freshOccurrence",
    "preLaneRoot", "laneRootChanged", "commandWellFormed", "feeEligible",
)

CLOSURE_THEOREM_TYPES = {
    "continuedState_static_frame": (
        f"∀ (input : {NAMESPACE}.X.Input), "
        f"({NAMESPACE}.continuedState input).moduleReleaseId = "
        f"input.transfer.pre.moduleReleaseId ∧ "
        f"({NAMESPACE}.continuedState input).policies = input.transfer.pre.policies"
    ),
    "continuedState_accepted": (
        f"∀ {{input : {NAMESPACE}.X.Input}}, "
        f"({NAMESPACE}.K.step input.transfer).verdict = .accepted → "
        f"{NAMESPACE}.continuedState input = "
        f"{{ ({NAMESPACE}.X.result input).post with "
        f"economic := {NAMESPACE}.X.successor input }}"
    ),
    "continuedState_rejected": (
        f"∀ {{input : {NAMESPACE}.X.Input}} {{code : {NAMESPACE}.T.RejectCode}}, "
        f"({NAMESPACE}.K.step input.transfer).verdict = .rejected code → "
        f"{NAMESPACE}.continuedState input = input.transfer.pre"
    ),
    "invariant_of_admitted": (
        f"∀ {{input : {NAMESPACE}.X.Input}}, {NAMESPACE}.X.Admitted input → "
        f"{NAMESPACE}.StateInvariant input.transfer.pre"
    ),
    "continuedState_invariant": (
        f"∀ {{input : {NAMESPACE}.X.Input}}, {NAMESPACE}.X.Admitted input → "
        f"{NAMESPACE}.StateInvariant ({NAMESPACE}.continuedState input)"
    ),
    "admitted_of_invariant": (
        f"∀ {{carried : {NAMESPACE}.K.State}} {{next : {NAMESPACE}.X.Input}}, "
        f"{NAMESPACE}.StateInvariant carried → "
        f"{NAMESPACE}.ContinuationRequirements carried next → "
        f"{NAMESPACE}.X.Admitted next"
    ),
    "continuation_admitted": (
        f"∀ {{input next : {NAMESPACE}.X.Input}}, "
        f"{NAMESPACE}.X.Admitted input → "
        f"{NAMESPACE}.ContinuationRequirements ({NAMESPACE}.continuedState input) next → "
        f"{NAMESPACE}.X.Admitted next"
    ),
    "continuation_verified": (
        f"∀ {{input next : {NAMESPACE}.X.Input}}, "
        f"{NAMESPACE}.X.Admitted input → "
        f"{NAMESPACE}.ContinuationRequirements ({NAMESPACE}.continuedState input) next → "
        f"({NAMESPACE}.K.step next.transfer).verdict = .accepted → "
        f"{GLOBAL_NAMESPACE}.Verified ({NAMESPACE}.X.pre next) "
        f"({NAMESPACE}.X.result next).plan ⟨[]⟩ ⟨[]⟩ [next.occurrence] "
        f"({NAMESPACE}.X.successor next)"
    ),
    "continuation_preserves_invariant": (
        f"∀ {{input next : {NAMESPACE}.X.Input}}, "
        f"{NAMESPACE}.X.Admitted input → "
        f"{NAMESPACE}.ContinuationRequirements ({NAMESPACE}.continuedState input) next → "
        f"{NAMESPACE}.StateInvariant ({NAMESPACE}.continuedState next)"
    ),
}

LEAN_OPENS = SUCCESSOR_OPENS + f"\nopen {NAMESPACE}\n"


@pytest.fixture(scope="module")
def lean(successor_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Compile only the new closure after the predecessor's fresh closure."""
    captured = successor_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes((PROJECT / "Proofs" / f"{MODULE}.lean").read_bytes())
    imports = re.findall(r"^import (\S+)", captured.read_text(), re.MULTILINE)
    assert imports == ["Proofs.AssetTransferGlobalSuccessorV1"], imports
    result = _compile(
        successor_subject, captured, successor_subject.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return successor_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{LEAN_OPENS}\n{body}")
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _lean_mirror_carried(
    witness: RuntimeWitness,
    post_lane_root: str,
    post_state_root: str,
    tag: str,
    carried_state: str,
) -> str:
    """Bind a next transfer's pre-state directly to the preceding Lean state."""
    mirror = _lean_mirror(witness, post_lane_root, post_state_root, tag)
    lines = mirror.splitlines(keepends=True)
    transfer_start = next(
        index for index, line in enumerate(lines) if line.startswith(f"def {tag}Transfer : Input")
    )
    pre_line = next(
        index for index in range(transfer_start + 1, len(lines))
        if lines[index].startswith("    pre := {")
    )
    lines[pre_line] = f"    pre := {carried_state} }}\n"
    return "".join(lines)


def test_contract_sources_fields_signatures_and_axioms(lean: LeanSubject) -> None:
    source_path = lean.source / "Proofs" / f"{MODULE}.lean"
    source = source_path.read_text()
    code = re.sub(r"/-.*?-", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(
        CLOSURE_THEOREM_TYPES
    )
    assert _structure_fields(code, "StateInvariant") == STATE_INVARIANT_FIELDS
    assert _structure_fields(code, "ContinuationRequirements") == (
        CONTINUATION_REQUIREMENT_FIELDS
    )
    registrations = (PROJECT / "Proofs.lean").read_text().splitlines()
    assert registrations.count(f"import {NAMESPACE}") == 1

    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in CLOSURE_THEOREM_TYPES.items()
    )
    report = " ".join(_probe(lean, "GlobalStateClosureTheoremConsumers", consumers).split())
    for name in CLOSURE_THEOREM_TYPES:
        found = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
            report,
        )
        assert found, (name, report)
        axioms = {entry.strip() for entry in (found.group(1) or "").split(",") if entry.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)

    for path, digest in SOURCE_PINS.items():
        assert hashlib.sha256((PROJECT.parent / path).read_bytes()).hexdigest() == digest, path


def _next_witness(
    previous: RuntimeWitness,
    previous_accepted: AssetTransferLaneModuleAcceptedV1,
    previous_post: GlobalEconomicStateV1,
    *,
    amount: int,
    nonce: int,
    op_index: int,
) -> RuntimeWitness:
    """Build a fresh request from the exact preceding module and global post values."""
    command = AssetTransferCommandV1(
        "asset_transfer", "USD", "alice", "bob", amount, 1,
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=previous_post.chain_id,
        deployment_root=previous_post.deployment_root,
        height=previous_post.height + 1,
        tx_index=0,
        op_index=op_index,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=previous.occurrence.route_release_id,
        subject_id=command.sender,
        grant_root=previous.occurrence.grant_root,
        nonce=nonce,
        profile_root=previous_post.profile_root,
        pre_state_root=previous_post.state_root,
        consumed_object_ids=(),
    )
    context = AssetTransferContextV1(
        previous_post.chain_id,
        previous_post.deployment_root,
        previous_post.profile_root,
        previous.module_input.context.writer_epoch,
        previous.module_input.context.module_release_id,
        occurrence.occurrence_id,
        command.sender,
        previous.occurrence.grant_root,
    )
    module_input = AssetTransferLaneModuleInputV1(
        context,
        previous_accepted.post_state,
        command,
        previous.module_input.asset_policy_registry_root,
        previous.module_input.fee_policy_registry_root,
        previous_accepted.private_port.post_state.custody,
    )
    return RuntimeWitness(
        module_input,
        previous_post,
        occurrence,
        previous_accepted.private_port.post_state.state_root,
        previous.liabilities,
    )


def _accepted_pair() -> tuple[
    RuntimeWitness,
    AssetTransferLaneModuleAcceptedV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    RuntimeWitness,
    AssetTransferLaneModuleAcceptedV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
]:
    """Run the actual coordinator/projector twice over a nonempty custody chain."""
    first = _runtime_witness(fee_owner="bob", amount=4)
    first_accepted = _run_custody_module(first)
    first_effects = _normalise(first, first_accepted)
    first_post = _project(first, first_effects, first.occurrence)
    second = _next_witness(first, first_accepted, first_post, amount=2, nonce=6, op_index=1)
    second_accepted = _run_custody_module(second)
    second_effects = _normalise(second, second_accepted)
    second_post = _project(second, second_effects, second.occurrence)
    return (
        first, first_accepted, first_effects, first_post,
        second, second_accepted, second_effects, second_post,
    )


def _rows_view(rows: tuple[EconomicAmountV1, ...]) -> list[list[str]]:
    return [[row.owner, row.asset, row.custody_domain, str(row.amount_atoms)] for row in rows]


def _expected_closure_observation(
    post: GlobalEconomicStateV1,
    replay_ids: list[str],
) -> list[list[str]]:
    replay = {row.replay_id: row.occurrence_id for row in post.replay_state}
    return [
        ["STATE_ROOT", post.state_root],
        ["ASSET_LANE_ROOT", next(row.state_root for row in post.lane_roots if row.lane_id is LaneIdV1.ASSET_TRANSFER)],
        ["HEIGHT", str(post.height)],
        *[["REPLAY", key, replay.get(key, "NONE")] for key in replay_ids],
        ["BALANCES"],
        *_rows_view(post.balances),
    ]


OBSERVERS = """
def closureOptionView : Option String → String
  | some value => value
  | none => "NONE"

def closureRowsView (rows : List AmountRow) : List (List String) :=
  rows.map fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]

def closureObserve (input : Proofs.AssetTransferGlobalStateClosureV1.X.Input)
    (replayIds : List String) : List (List String) :=
  let state := Proofs.AssetTransferGlobalStateClosureV1.continuedState input
  [["STATE_ROOT", state.economic.stateRoot],
   ["ASSET_LANE_ROOT", state.economic.laneRoots .assetTransfer],
   ["HEIGHT", toString state.economic.height]] ++
   (replayIds.map fun key => ["REPLAY", key, closureOptionView (state.economic.replayState key)]) ++
   [["BALANCES"]] ++ closureRowsView state.economic.balances
"""


def _requirements(tag: str, next_tag: str) -> str:
    """Spell all ten continuation fields so the consumer exercises each premise."""
    return f"""
theorem {tag}_requirements :
    {NAMESPACE}.ContinuationRequirements
      ({NAMESPACE}.continuedState {tag}Global) {next_tag}Global := by
  refine {{
    pre := ?_,
    context := ?_,
    height := ?_,
    heightFits := ?_,
    freshReplay := ?_,
    freshOccurrence := ?_,
    preLaneRoot := ?_,
    laneRootChanged := ?_,
    commandWellFormed := ?_,
    feeEligible := ?_ }}
  · rfl
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · rfl
  · unfold FitsU64
    decide
  · decide
  · intro replayId prior lookup
    change (if replayId = {tag}Occurrence.replayId then some {tag}Occurrence.occurrenceId
      else {tag}Replay replayId) = some prior at lookup
    split at lookup
    · cases lookup
      decide
    · simp only [{tag}Replay] at lookup
      split at lookup
      · cases lookup
        decide
      · cases lookup
  · rfl
  · decide
  · exact ⟨by decide, by decide⟩
  · exact {next_tag}_fee_eligible
"""


def _lean_fee_eligible_carried(tag: str) -> str:
    """Prove fee eligibility after carrying the preceding policy rows."""
    return f"""
theorem {tag}_fee_eligible : FeeEligible {tag}Global := by
  intro policy selection
  change policyFor ({NAMESPACE}.continuedState firstGlobal).policies
    "USD" = some policy at selection
  rw [({NAMESPACE}.continuedState_static_frame firstGlobal).2] at selection
  change policyFor firstTransfer.pre.policies "USD" = some policy at selection
  simp [firstTransfer, policyFor] at selection
  subst policy
  exact Or.inr (by decide)
"""


def _freshness_controls() -> str:
    return f"""
def staleNext : {GLOBAL_INPUT} :=
  {{ secondGlobal with transfer := {{ secondTransfer with pre := firstTransfer.pre }} }}
def reusedReplayOccurrence : {GLOBAL_NAMESPACE}.CommandOccurrence :=
  {{ secondOccurrence with replayId := firstOccurrence.replayId }}
def reusedReplayGlobal : {GLOBAL_INPUT} :=
  {{ secondGlobal with occurrence := reusedReplayOccurrence }}
def reusedOccurrenceId : {GLOBAL_NAMESPACE}.CommandOccurrence :=
  {{ secondOccurrence with occurrenceId := firstOccurrence.occurrenceId }}
def reusedOccurrenceIdGlobal : {GLOBAL_INPUT} :=
  {{ secondGlobal with occurrence := reusedOccurrenceId }}

example : staleNext.transfer.pre.economic.height ≠
    ({NAMESPACE}.continuedState firstGlobal).economic.height := by decide
example : ¬ {NAMESPACE}.ContinuationRequirements
    ({NAMESPACE}.continuedState firstGlobal) staleNext := by
  intro requirements
  have mismatch := congrArg (fun state : {NAMESPACE}.K.State => state.economic.height)
    requirements.pre
  exact (by decide : staleNext.transfer.pre.economic.height ≠
    ({NAMESPACE}.continuedState firstGlobal).economic.height) mismatch

example : ({NAMESPACE}.continuedState firstGlobal).economic.replayState
    reusedReplayGlobal.occurrence.replayId ≠ none := by decide
example : ¬ {NAMESPACE}.ContinuationRequirements
    ({NAMESPACE}.continuedState firstGlobal) reusedReplayGlobal := by
  intro requirements
  exact (by decide :
    ({NAMESPACE}.continuedState firstGlobal).economic.replayState
      reusedReplayGlobal.occurrence.replayId ≠ none) requirements.freshReplay

example : ¬ {NAMESPACE}.ContinuationRequirements
    ({NAMESPACE}.continuedState firstGlobal) reusedOccurrenceIdGlobal := by
  intro requirements
  have collision := requirements.freshOccurrence firstOccurrence.replayId
    firstOccurrence.occurrenceId (by decide)
  exact collision rfl
"""


def test_two_actual_transfers_close_and_preserve_global_metadata(lean: LeanSubject) -> None:
    (
        first, first_accepted, first_effects, first_post,
        second, second_accepted, second_effects, second_post,
    ) = _accepted_pair()
    assert first.module_input.command.amount_atoms == 4
    assert second.module_input.command.amount_atoms == 2
    assert first_effects.rows and second_effects.rows
    assert second.pre_global == first_post
    assert second.module_input.pre_state.balances == second_accepted.private_port.pre_state.balances
    assert second.module_input.pre_state.supplies == second_accepted.private_port.pre_state.supplies
    assert first_post.balances == first_accepted.post_state.balances
    assert second_post.balances == second_accepted.post_state.balances
    assert first_post.height == first.occurrence.height
    assert second_post.height == second.occurrence.height == first_post.height + 1
    assert first_post.balances != second_post.balances
    assert first_post.replay_state != second_post.replay_state
    assert all(row in second_post.replay_state for row in first_post.replay_state)
    assert any(row.replay_id == second.occurrence.replay_id for row in second_post.replay_state)
    assert first_post.custody == second_post.custody == first.module_input.custody
    assert first_post.liabilities == second_post.liabilities == first.liabilities
    assert first_post.supplies == second_post.supplies
    assert first_post.lane_roots[1:] == second_post.lane_roots[1:]
    assert first_post.lane_roots[0].state_root != second_post.lane_roots[0].state_root
    assert asdict(first_post) == asdict(_expected_post_global(
        first, first_accepted.private_port.post_state.state_root,
    ))
    assert asdict(second_post) == asdict(_expected_post_global(
        second, second_accepted.private_port.post_state.state_root,
    ))

    body = (
        _lean_mirror(
            first, first_accepted.private_port.post_state.state_root, first_post.state_root, "first",
        )
        + _lean_mirror_carried(
            second,
            second_accepted.private_port.post_state.state_root,
            second_post.state_root,
            "second",
            f"{NAMESPACE}.continuedState firstGlobal",
        )
        + _lean_admission("first")
        + _lean_fee_eligible("first")
        + _lean_admitted_record("first")
        + _lean_fee_eligible_carried("second")
        + """
theorem first_accepted : (step firstTransfer).verdict = .accepted := by decide
theorem second_accepted : (step secondTransfer).verdict = .accepted := by
  have carriedBalances :
      (continuedState firstGlobal).economic.balances = secondEconomic.balances := by
    rw [continuedState_accepted first_accepted]
    change Proofs.CanonicalEpochEconomicRowsV1.sortOn
      Proofs.AssetTransferSparseTablesV1.balanceWire
        [⟨"bob", "USD", "accounts", (10 : Int)⟩,
         ⟨"alice", "USD", "accounts", (35 : Int)⟩,
         ⟨"alice", "EUR", "accounts", (9 : Int)⟩] = _
    simp +decide [Proofs.CanonicalEpochEconomicRowsV1.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop,
      secondEconomic]
  unfold step
  simp only [secondTransfer, (continuedState_static_frame firstGlobal).1,
    (continuedState_static_frame firstGlobal).2]
  change (Proofs.AssetTransferSparseTablesV1.step
    (selectedInput secondTransfer ⟨"USD", "bob", (1 : Int), true⟩)).verdict = .accepted
  unfold Proofs.AssetTransferSparseTablesV1.step
  simp only [Proofs.AssetTransferSparseTablesV1.leaf,
    Proofs.AssetTransferSparseTablesV1.localState,
    Proofs.AssetTransferSparseTablesV1.checkedBalances,
    selectedInput, secondTransfer, carriedBalances,
    (continuedState_static_frame firstGlobal).1]
  decide
"""
        + _requirements("first", "second")
        + f"""

example : {NAMESPACE}.StateInvariant ({NAMESPACE}.continuedState firstGlobal) :=
  {NAMESPACE}.continuedState_invariant first_admitted
example : {SUCCESSOR_NAMESPACE}.Admitted secondGlobal :=
  {NAMESPACE}.continuation_admitted first_admitted first_requirements
example : {GLOBAL_NAMESPACE}.Verified (pre secondGlobal) (result secondGlobal).plan
    ⟨[]⟩ ⟨[]⟩ [secondOccurrence] (successor secondGlobal) :=
  {NAMESPACE}.continuation_verified first_admitted first_requirements second_accepted
example : {NAMESPACE}.StateInvariant ({NAMESPACE}.continuedState secondGlobal) :=
  {NAMESPACE}.continuation_preserves_invariant first_admitted first_requirements
"""
        + OBSERVERS
        + _freshness_controls()
    )
    replay_ids = [
        *(row.replay_id for row in first.pre_global.replay_state),
        first.occurrence.replay_id, second.occurrence.replay_id, "absent-replay",
    ]
    lean_ids = "[" + ", ".join(json.dumps(key) for key in replay_ids) + "]"
    body += f"#eval IO.println (reprStr (reprStr (closureObserve firstGlobal {lean_ids})))\n"
    body += f"#eval IO.println (reprStr (reprStr (closureObserve secondGlobal {lean_ids})))\n"
    decoded = _decode(_probe(lean, "GlobalStateClosureTwoTransfers", body))
    assert decoded == [
        _expected_closure_observation(first_post, replay_ids),
        _expected_closure_observation(second_post, replay_ids),
    ]


def test_rejected_continuation_is_exact_carried_state_noop(lean: LeanSubject) -> None:
    first, first_accepted, _, first_post, *_ = _accepted_pair()
    rejected = _next_witness(first, first_accepted, first_post, amount=0, nonce=7, op_index=2)
    before = canonical_global_bytes_v1(rejected.module_input.to_canonical())
    global_before = canonical_global_bytes_v1(rejected.pre_global.to_canonical())
    result = transition_asset_transfer_lane_module_custody_v1(rejected.module_input)
    assert canonical_global_bytes_v1(rejected.module_input.to_canonical()) == before
    assert canonical_global_bytes_v1(rejected.pre_global.to_canonical()) == global_before
    assert type(result) is AssetTransferRejectedV1
    assert result.code is AssetTransferRejectCodeV1.ZERO_AMOUNT
    assert result.effects == GlobalEconomicEffectPlanV1.empty()
    assert result.pre_state_root == result.post_state_root == rejected.module_input.pre_state.state_root
    assert result.pre_state_root != rejected.port_pre_root

    body = (
        _lean_mirror(
            first, first_accepted.private_port.post_state.state_root, first_post.state_root, "first",
        )
        + _lean_mirror_carried(
            rejected,
            _root(0xCC),
            _root(0xDD),
            "rejected",
            f"{NAMESPACE}.continuedState firstGlobal",
        )
        + _lean_admission("first")
        + _lean_fee_eligible("first")
        + _lean_admitted_record("first")
        + _lean_fee_eligible_carried("rejected")
        + """
theorem first_accepted : (step firstTransfer).verdict = .accepted := by decide
theorem rejected_leaf : (step rejectedTransfer).verdict = .rejected .zeroAmount := by decide
"""
        + _requirements("first", "rejected")
        + f"""
example : {SUCCESSOR_NAMESPACE}.Admitted rejectedGlobal :=
  {NAMESPACE}.continuation_admitted first_admitted first_requirements
example : {NAMESPACE}.StateInvariant ({NAMESPACE}.continuedState rejectedGlobal) :=
  {NAMESPACE}.continuation_preserves_invariant first_admitted first_requirements
example : {NAMESPACE}.continuedState rejectedGlobal = rejectedGlobal.transfer.pre :=
  {NAMESPACE}.continuedState_rejected rejected_leaf
example : ({NAMESPACE}.continuedState rejectedGlobal).economic.height =
    ({SUCCESSOR_NAMESPACE}.pre rejectedGlobal).height := by
  rw [{NAMESPACE}.continuedState_rejected rejected_leaf]
  rfl
"""
    )
    assert _probe(lean, "GlobalStateClosureRejectedContinuation", body) == ""


def test_maximum_height_blocks_the_next_continuation_requirements(lean: LeanSubject) -> None:
    top = _runtime_witness(fee_owner="bob", height=MAX_U64_V1 - 1, amount=4)
    accepted = _run_custody_module(top)
    effects = _normalise(top, accepted)
    post = _project(top, effects, top.occurrence)
    assert post.height == top.occurrence.height == MAX_U64_V1

    body = (
        _lean_mirror(top, accepted.private_port.post_state.state_root, post.state_root, "top")
        + _lean_admission("top")
        + _lean_fee_eligible("top")
        + _lean_admitted_record("top")
        + f"""
theorem top_accepted : (step topTransfer).verdict = .accepted := by decide
example : {NAMESPACE}.StateInvariant ({NAMESPACE}.continuedState topGlobal) :=
  {NAMESPACE}.continuedState_invariant top_admitted
def overflowNext : {GLOBAL_INPUT} :=
  {{ topGlobal with occurrence := {{ topOccurrence with height := maxU64 + 1 }} }}
example : ({NAMESPACE}.continuedState topGlobal).economic.height = maxU64 := by
  decide
example : ¬ FitsU64 (({NAMESPACE}.continuedState topGlobal).economic.height + 1) := by
  unfold FitsU64
  decide
example : ¬ {NAMESPACE}.ContinuationRequirements
    ({NAMESPACE}.continuedState topGlobal) overflowNext := by
  intro requirements
  exact (by unfold FitsU64; decide : ¬ FitsU64
    (({NAMESPACE}.continuedState topGlobal).economic.height + 1)) requirements.heightFits
"""
    )
    assert _probe(lean, "GlobalStateClosureMaximumHeight", body) == ""


def test_continued_state_leaf_economic_mutant_is_observable_and_rejected(
    lean: LeanSubject,
) -> None:
    first, first_accepted, _, first_post, *_ = _accepted_pair()
    captured_path = lean.source / "Proofs" / f"{MODULE}.lean"
    original_path = PROJECT / "Proofs" / f"{MODULE}.lean"
    original_bytes = original_path.read_bytes()
    assert captured_path.read_bytes() == original_bytes
    source = captured_path.read_text()
    old = "{ (X.result input).post with economic := (X.step input).post }"
    new = "{ (X.result input).post with economic := (X.result input).post.economic }"
    assert source.count(old) == 1
    mutated = source.replace(old, new, 1)
    first_theorem = re.search(r"^private theorem ", mutated, re.MULTILINE)
    assert first_theorem is not None
    prefix = (mutated[:first_theorem.start()]
              + "\nend AssetTransferGlobalStateClosureV1\nend Proofs\n"
              + LEAN_OPENS + (
        _lean_mirror(
            first, first_accepted.private_port.post_state.state_root, first_post.state_root, "first",
        )
        + """
def optionView : Option String → String
  | some value => value
  | none => "NONE"

def mutantObserve : List String :=
  [toString (continuedState firstGlobal).economic.height,
   optionView ((continuedState firstGlobal).economic.replayState firstOccurrence.replayId)]
#eval IO.println (reprStr (reprStr mutantObserve))

"""
    ))
    prefix_path = lean.source / "Mutant_continued_state_metadata_prefix.lean"
    prefix_path.write_text(prefix)
    prefix_result = _compile(lean, prefix_path)
    assert prefix_result.returncode == 0, prefix_result.stdout + prefix_result.stderr
    observed = json.loads(json.loads(prefix_result.stdout.strip()))
    assert observed == [str(first.pre_global.height), "NONE"]
    assert observed != [str(first_post.height), first.occurrence.occurrence_id]

    full_path = lean.source / f"Mutant_{MODULE}_continued_state_metadata.lean"
    full_path.write_text(mutated)
    full_result = _compile(lean, full_path)
    output = full_result.stdout + full_result.stderr
    assert full_result.returncode != 0
    assert "unexpected token" not in output
    assert "unknown identifier" not in output.lower()
    assert "unknown constant" not in output.lower()
    errors = [int(line) for line in re.findall(
        rf"{re.escape(str(full_path))}:(\d+):\d+: error(?:\([^)]*\))?:", output,
    )]
    assert errors, output
    lines = mutated.splitlines()
    start = next(i for i, line in enumerate(lines, 1) if line.startswith("theorem continuedState_accepted"))
    end = next(i for i, line in enumerate(lines, 1) if line.startswith("theorem continuedState_rejected"))
    assert any(start <= line < end for line in errors), output
    assert captured_path.read_bytes() == original_bytes
    assert original_path.read_bytes() == original_bytes
