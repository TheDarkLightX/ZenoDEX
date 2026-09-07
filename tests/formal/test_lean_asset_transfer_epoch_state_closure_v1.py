"""Shared-height epoch continuation: theorem consumers, runtime controls and mutants.

Obligation: an accepted custody-complete ASSET_TRANSFER attempt at a later epoch
position (predecessor already at the shared target height ``H + 1``) yields the
actual completed economic tables with only four metadata changes, the shared
height, the exact replay insertion and other-key frame, and the nine inherited
state obligations; a rejected attempt is the exact carried-state no-op; a finite
admitted prefix preserves the invariant by induction.  ``Verified`` is claimed
only at the first position, where the construction coincides with the standalone
successor.

Lean lane (grade 4): the fresh Std-only closure of the predecessor fixtures plus
the new module, every public theorem restated as an independent consumer, axiom
checks, field pins of the two admission/obligation records against the existing
``Verified`` field list, and the actual theorems applied to two accepted transfers
at one epoch height over a nonempty custody, backed-liability, prior-replay and
oracle witness, at height 7 and at the u64 maximum.

Runtime lane: the actual custody module ``transition_asset_transfer_lane_module_custody_v1``
and public coordinator ``compose_asset_lane_single_v1`` run both transfers.  The
first pair is projected by the standalone projector (adjacent ``H -> H + 1``); the
second prospective disclosure is built from the accepted private port by an
explicit input-derived builder (grade 2) because the standalone projector requires
``pre.height + 1`` on every call and is shown to refuse the shared height.  Both
pairs are checked by the actual epoch-position relation
``_epoch_allocation_binding_reject_v1`` (which selects ``EPOCH_POSITION`` mode of
``_global_allocation_binding_reject_v1``); the standalone adjacent relation is
shown to refuse the second pair.  As a supplementary aggregate control, the full
checker ``check_asset_transfer_epoch_allocation_v1`` (fragment receipt admission
and the certificate check) is driven by the legacy composition fixture of
``tests/core/test_asset_transfer_epoch_allocation_v1`` (mock receipt verifier,
empty custody): it accepts a two-command epoch at one height and rejects
height-double-increment and replay-omission disclosures at index 1 without
partial checks.  Lean observations of the carried states are compared with the
Python states (grade 3).  Two constructor mutants of the ordinary law are
executed: the double-increment mutant and the replay-omission mutant each expose
a bad value through definitions alone and fail the pinned theorems.

Nonclaims: no epoch-level ``Verified``, no aggregate authorization, no atomicity
of the runtime fold, no whole-epoch publication, certificate, receipt, snapshot
authenticity, store head or universal Python/Rust refinement.  Synthetic receipts
and mock verifiers grant no cryptographic authority.  The per-pair relation
evidence (lane A) and the aggregate checker evidence (lane B) are distinct
claims: lane A does not run receipt admission or the certificate, lane B does
not carry the nonempty custody witness.  The legacy composition fixture's
nonzero-custody disagreement is intentionally retained in tests/core and is not
a statement about the current custody pipeline, whose nonzero-custody epoch
admission is covered by
``tests/integration/test_isolated_custody_asset_receipt_pipeline_v1``.
Registration of the new module in ``lean-mathlib/Proofs.lean`` is a root
integration step; this module asserts only the import order relative to its
predecessor when that registration is present.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from dataclasses import asdict, replace

import pytest

from src.core import asset_transfer_epoch_allocation_v1 as epoch_consumer
from src.core.asset_transfer_epoch_position_v1 import AssetTransferEpochPositionV1
from src.core.asset_transfer_global_allocation_v1 import (
    AssetTransferGlobalAllocationCandidateV1,
    GlobalAllocationBindingRejectCodeV1,
    _epoch_allocation_binding_reject_v1,
    _global_allocation_binding_reject_v1,
)
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
from src.core.global_economic_effect_projector_v1 import (
    project_single_occurrence_global_effects_v1,
)
from src.core.global_economic_proof_v1 import MAX_EPOCH_COMMANDS_V1, EconomicCommandOccurrenceV1
from src.core.global_settlement_types_v1 import (
    MAX_U64_V1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    ReplayStateV1,
    canonical_global_bytes_v1,
)
from tests.core.test_asset_transfer_epoch_allocation_v1 import _check as _check_epoch
from tests.core.test_asset_transfer_epoch_allocation_v1 import _fixture as _epoch_fixture
from tests.formal.test_lean_asset_transfer_annotation_mirrors_v1 import (
    lean as annotation_subject,  # noqa: F401 -- predecessor fixture chain.
)
from tests.formal.test_lean_asset_transfer_effect_plan_v1 import (
    lean as effect_plan_subject,  # noqa: F401 -- predecessor fixture chain.
)
from tests.formal.test_lean_asset_transfer_global_state_closure_v1 import (
    SOURCE_PINS as CLOSURE_SOURCE_PINS,
)
from tests.formal.test_lean_asset_transfer_global_state_closure_v1 import (
    _lean_mirror_carried,
)
from tests.formal.test_lean_asset_transfer_global_state_closure_v1 import (
    lean as closure_subject,  # noqa: F401 -- predecessor fresh-source fixture.
)
from tests.formal.test_lean_asset_transfer_global_successor_v1 import (
    GLOBAL_INPUT,
    PROJECT,
    VERIFIED_FIELDS,
    RuntimeWitness,
    _compile,
    _decode,
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
    lean as successor_subject,  # noqa: F401 -- predecessor fixture chain.
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

MODULE = "AssetTransferEpochStateClosureV1"
NAMESPACE = f"Proofs.{MODULE}"
CLOSURE_NAMESPACE = "Proofs.AssetTransferGlobalStateClosureV1"
SUCCESSOR_NAMESPACE = "Proofs.AssetTransferGlobalSuccessorV1"
POLICY_NAMESPACE = "Proofs.AssetTransferPolicySelectionV1"
GLOBAL_NAMESPACE = "Proofs.GlobalEconomicStateRefinementV2"
MODULE_STATE = f"{POLICY_NAMESPACE}.State"
REJECT_CODE = "Proofs.AssetTransferRefinementV1.RejectCode"
PLACEHOLDER_SCANNER = PROJECT.parent / "tools" / "scan_lean_proof_placeholders_v1.py"

# The predecessor fixtures supply the Lean dependency closure; their selected pins are
# reused verbatim and the new module plus the retained epoch runtime sources are added.
SOURCE_PINS = {
    **CLOSURE_SOURCE_PINS,
    "lean-mathlib/Proofs/AssetTransferEpochStateClosureV1.lean":
        "1f1a3b68fc0f16755ea9abdcb07e4bff6d44492ef60ffa5d2710c7b22d617533",
    "lean-mathlib/lean-toolchain":
        "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb",
    "src/core/asset_transfer_epoch_position_v1.py":
        "87e04c3ea4bf0fc8889b978a691f3d644110dbf7406001d47e015b39da39bf78",
    "src/core/asset_transfer_global_allocation_v1.py":
        "a4099cb3e53c26ef981e384e92cbdc5c04b80d5bdf7c14cd3b2d296a8830f028",
    "src/core/asset_transfer_epoch_allocation_v1.py":
        "34a5012d84f130921ce80c87e367c56bfe92d6e6d7c59ccd6774d8fbc3bcb071",
    "src/core/asset_transfer_receipt_admission_v1.py":
        "3b94dbd2105aa6247e1423d80638a5c0fb7cce7017a504616021d4db5447a633",
}

POSITION_FIELDS = ("source", "index")
EPOCH_REQUIREMENT_FIELDS = (
    "pre", "indexBound", "targetFits", "priorHeight", "firstSource", "sourceContext",
    "context", "height", "freshReplay", "freshOccurrence", "preLaneRoot", "laneRootChanged",
    "commandWellFormed", "feeEligible",
)
SHARED_HEIGHT_FIELDS = (
    "fixedContext", "preQuantities", "postQuantities", "effectPlan", "laneWrites",
    "economicTables", "supplyEffects", "conservationCoverage", "conservationRows",
    "annotations", "ownedSupplyPre", "ownedSupplyPost", "liabilitiesPre", "liabilitiesPost",
    "terminal", "oracle", "orderedOccurrences", "occurrenceConsumptions", "occurrenceContext",
    "replayRegistry", "sharedHeight", "heightFits", "occurrenceHeight", "outboxClosed",
    "zeroOccurrence",
)
# The one `Verified` clause that a later epoch position cannot satisfy, and the clauses
# that replace it.  Pinned so the gap can neither be hidden nor silently widened.
REPLACED_VERIFIED_FIELD = "replay"
REPLACEMENT_FIELDS = (
    "orderedOccurrences", "occurrenceConsumptions", "occurrenceContext", "replayRegistry",
    "sharedHeight", "heightFits", "occurrenceHeight",
)

_INPUT_ADMISSION = (
    "StateInvariant input.transfer.pre → EpochRequirements position input.transfer.pre input"
)
_CARRIED_ADMISSION = "StateInvariant carried → EpochRequirements position carried next"
_ACCEPTED = "({POLICY}.step {name}.transfer).verdict = .accepted"
_PREFIX_BINDERS = (
    f"{{source : {MODULE_STATE}}} {{count : Nat}} {{occurrences : List CommandOccurrence}} "
    f"{{carried : {MODULE_STATE}}}"
)

THEOREM_TYPES = {
    "epochSuccessor_metadata": (
        f"∀ (input : {GLOBAL_INPUT}), (epochSuccessor input).stateRoot = input.postStateRoot ∧ "
        "(epochSuccessor input).height = input.occurrence.height ∧ "
        "(epochSuccessor input).laneRoots .assetTransfer = input.postLaneRoot ∧ "
        "(∀ lane, lane ≠ .assetTransfer → "
        "(epochSuccessor input).laneRoots lane = (pre input).laneRoots lane) ∧ "
        "(epochSuccessor input).replayState input.occurrence.replayId = "
        "some input.occurrence.occurrenceId ∧ "
        "∀ replayId, replayId ≠ input.occurrence.replayId → "
        "(epochSuccessor input).replayState replayId = (pre input).replayState replayId"
    ),
    "epochSuccessor_frame": (
        f"∀ (input : {GLOBAL_INPUT}), epochSuccessor input = "
        "{ pre input with balances := (result input).post.economic.balances, "
        "stateRoot := input.postStateRoot, height := input.occurrence.height, "
        "laneRoots := successorRoots (pre input) input.postLaneRoot, "
        "replayState := insertReplay (pre input).replayState input.occurrence }"
    ),
    "epochSuccessor_fixed_context": (
        f"∀ (input : {GLOBAL_INPUT}), FixedContext (pre input) (epochSuccessor input)"
    ),
    "epochStep_accepted": (
        f"∀ {{input : {GLOBAL_INPUT}}}, ({POLICY_NAMESPACE}.step input.transfer).verdict = "
        ".accepted → epochStep input = "
        "⟨.accepted, epochSuccessor input, (result input).plan, [input.occurrence]⟩"
    ),
    "epochStep_rejected_exact": (
        f"∀ {{input : {GLOBAL_INPUT}}} {{code : {REJECT_CODE}}}, "
        f"({POLICY_NAMESPACE}.step input.transfer).verdict = .rejected code → "
        "epochStep input = ⟨.rejected code, pre input, EffectPlan.empty, []⟩"
    ),
    "epochContinuedState_static_frame": (
        f"∀ (input : {GLOBAL_INPUT}), "
        "(epochContinuedState input).moduleReleaseId = input.transfer.pre.moduleReleaseId ∧ "
        "(epochContinuedState input).policies = input.transfer.pre.policies"
    ),
    "epochContinuedState_accepted": (
        f"∀ {{input : {GLOBAL_INPUT}}}, ({POLICY_NAMESPACE}.step input.transfer).verdict = "
        ".accepted → epochContinuedState input = "
        "{ (result input).post with economic := epochSuccessor input }"
    ),
    "epochContinuedState_rejected": (
        f"∀ {{input : {GLOBAL_INPUT}}} {{code : {REJECT_CODE}}}, "
        f"({POLICY_NAMESPACE}.step input.transfer).verdict = .rejected code → "
        "epochContinuedState input = input.transfer.pre"
    ),
    "epochSuccessor_quantities": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, {_INPUT_ADMISSION} → "
        "StateQuantitiesAdmitted (epochSuccessor input)"
    ),
    "epochSuccessor_owned_backed": (
        f"∀ {{input : {GLOBAL_INPUT}}}, StateInvariant input.transfer.pre → "
        "OwnedMatchesSupply (epochSuccessor input) ∧ ClaimantLiabilitiesBacked (epochSuccessor input)"
    ),
    "epochSuccessor_lane_writes": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, {_INPUT_ADMISSION} → "
        f"{_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='input')} → "
        "ExactLaneWrites (pre input) (epochSuccessor input) (result input).plan"
    ),
    "epochSuccessor_annotations": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, {_INPUT_ADMISSION} → "
        f"{_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='input')} → "
        "AnnotationMirrors (result input).plan"
    ),
    "epochSuccessor_terminal": (
        f"∀ {{input : {GLOBAL_INPUT}}}, StateAdmitted input.transfer.pre → "
        f"{_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='input')} → "
        "ExactTerminalRefinement (pre input) (epochSuccessor input) (result input).plan ⟨[]⟩"
    ),
    "epochSuccessor_replay_registry": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, "
        "EpochRequirements position input.transfer.pre input → "
        "ReplayRegistryRefines (pre input).replayState (epochSuccessor input).replayState "
        "[input.occurrence]"
    ),
    "sharedHeight_verified": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, {_INPUT_ADMISSION} → "
        f"{_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='input')} → "
        "SharedHeightVerified position input"
    ),
    "epochSuccessor_first": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, "
        "EpochRequirements position input.transfer.pre input → position.index = 0 → "
        "epochSuccessor input = successor input"
    ),
    "admitted_first": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, {_INPUT_ADMISSION} → "
        "position.index = 0 → Admitted input"
    ),
    "epochSuccessor_first_verified": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, {_INPUT_ADMISSION} → "
        f"position.index = 0 → {_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='input')} → "
        "Verified (pre input) (result input).plan ⟨[]⟩ ⟨[]⟩ [input.occurrence] "
        "(epochSuccessor input)"
    ),
    "epochContinuedState_invariant": (
        f"∀ {{position : Position}} {{input : {GLOBAL_INPUT}}}, {_INPUT_ADMISSION} → "
        "StateInvariant (epochContinuedState input)"
    ),
    "epochContinuation_invariant": (
        f"∀ {{position : Position}} {{carried : {MODULE_STATE}}} {{next : {GLOBAL_INPUT}}}, "
        f"{_CARRIED_ADMISSION} → StateInvariant (epochContinuedState next)"
    ),
    "epochContinuation_verified": (
        f"∀ {{position : Position}} {{carried : {MODULE_STATE}}} {{next : {GLOBAL_INPUT}}}, "
        f"{_CARRIED_ADMISSION} → {_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='next')} → "
        "SharedHeightVerified position next"
    ),
    "epochContinuation_first_verified": (
        f"∀ {{position : Position}} {{carried : {MODULE_STATE}}} {{next : {GLOBAL_INPUT}}}, "
        f"{_CARRIED_ADMISSION} → position.index = 0 → "
        f"{_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='next')} → "
        "Verified (pre next) (result next).plan ⟨[]⟩ ⟨[]⟩ [next.occurrence] (epochSuccessor next)"
    ),
    "epochPrefix_length": (
        f"∀ {_PREFIX_BINDERS}, EpochPrefix source count occurrences carried → "
        "occurrences.length = count ∧ count ≤ maxEpochCommands"
    ),
    "epochPrefix_invariant": (
        f"∀ {_PREFIX_BINDERS}, StateInvariant source → "
        "EpochPrefix source count occurrences carried → StateInvariant carried"
    ),
    "epochPrefix_metadata": (
        f"∀ {_PREFIX_BINDERS}, EpochPrefix source count occurrences carried → "
        "carried.moduleReleaseId = source.moduleReleaseId ∧ carried.policies = source.policies ∧ "
        "SameContext source.economic carried.economic ∧ "
        "carried.economic.height = expectedPriorHeight ⟨source.economic, count⟩ ∧ "
        "carried.economic.replayState = "
        "occurrences.foldl insertReplay source.economic.replayState"
    ),
    "epochPrefix_nonempty": (
        f"∀ {_PREFIX_BINDERS}, EpochPrefix source count occurrences carried → count ≠ 0 → "
        "1 ≤ count ∧ count ≤ maxEpochCommands ∧ "
        "carried.economic.height = source.economic.height + 1"
    ),
    "epochPrefix_next_verified": (
        f"∀ {_PREFIX_BINDERS} {{next : {GLOBAL_INPUT}}}, StateInvariant source → "
        "EpochPrefix source count occurrences carried → "
        "EpochRequirements ⟨source.economic, count⟩ carried next → "
        f"{_ACCEPTED.format(POLICY=POLICY_NAMESPACE, name='next')} → "
        "SharedHeightVerified ⟨source.economic, count⟩ next ∧ "
        "(count = 0 → Verified (pre next) (result next).plan ⟨[]⟩ ⟨[]⟩ [next.occurrence] "
        "(epochSuccessor next))"
    ),
}

LEAN_OPENS = SUCCESSOR_OPENS + (
    f"\nopen {CLOSURE_NAMESPACE} (StateInvariant ContinuationRequirements invariant_of_admitted)"
    f"\nopen {NAMESPACE}\n"
)


@pytest.fixture(scope="module")
def lean(closure_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Compile only the new epoch closure after the predecessor's fresh closure."""
    captured = closure_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes((PROJECT / "Proofs" / f"{MODULE}.lean").read_bytes())
    imports = re.findall(r"^import (\S+)", captured.read_text(), re.MULTILINE)
    assert imports == [CLOSURE_NAMESPACE], imports
    result = _compile(
        closure_subject, captured, closure_subject.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return closure_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{LEAN_OPENS}\n{body}")
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


# ---------------------------------------------------------------------------------------
# Contract: placeholders, theorem surface, record fields, consumers, axioms and pins.


def test_contract_placeholders_fields_signatures_axioms_and_source_pins(lean: LeanSubject) -> None:
    source_path = lean.source / "Proofs" / f"{MODULE}.lean"
    source = source_path.read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    scanned = subprocess.run(
        [sys.executable, str(PLACEHOLDER_SCANNER), str(source_path), "--json"],
        cwd=PROJECT.parent, capture_output=True, text=True, timeout=120, check=False,
    )
    assert scanned.returncode == 0, scanned.stdout + scanned.stderr
    payload = json.loads(scanned.stdout)
    assert payload["blocked"] is False and payload["match_count"] == 0
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(THEOREM_TYPES)
    assert _structure_fields(code, "Position") == POSITION_FIELDS
    assert _structure_fields(code, "EpochRequirements") == EPOCH_REQUIREMENT_FIELDS
    assert _structure_fields(code, "SharedHeightVerified") == SHARED_HEIGHT_FIELDS
    assert set(VERIFIED_FIELDS) - set(SHARED_HEIGHT_FIELDS) == {REPLACED_VERIFIED_FIELD}
    assert set(SHARED_HEIGHT_FIELDS) - set(VERIFIED_FIELDS) == set(REPLACEMENT_FIELDS)
    assert re.search(r"^inductive EpochPrefix\b", code, flags=re.MULTILINE)
    assert re.search(r"^def maxEpochCommands : Nat := 64$", code, flags=re.MULTILINE)
    assert MAX_EPOCH_COMMANDS_V1 == 64
    # Registration in Proofs.lean is a root integration step (an existing tracked file).  The
    # predecessor must be registered exactly once, and if the new module is registered it must
    # be registered exactly once, after its predecessor.
    registrations = (PROJECT / "Proofs.lean").read_text().splitlines()
    assert registrations.count(f"import {CLOSURE_NAMESPACE}") == 1
    assert registrations.count(f"import {NAMESPACE}") <= 1
    if f"import {NAMESPACE}" in registrations:
        assert registrations.index(f"import {NAMESPACE}") > registrations.index(
            f"import {CLOSURE_NAMESPACE}"
        )

    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    ) + f"\nexample : maxEpochCommands = {MAX_EPOCH_COMMANDS_V1} := rfl\n"
    report = " ".join(_probe(lean, "EpochStateClosureTheoremConsumers", consumers).split())
    for name in THEOREM_TYPES:
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


# ---------------------------------------------------------------------------------------
# Runtime witness: two custody-complete transfers whose prospective disclosures share one
# epoch height, checked by the actual epoch-position relation.


def _prospective_post(
    current: GlobalEconomicStateV1,
    occurrence: EconomicCommandOccurrenceV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> GlobalEconomicStateV1:
    """The disclosure the epoch checker expects: input-derived, never read from a checker.

    Height is the occurrence height (the shared epoch target), tables come from the
    accepted private port, only the asset lane root changes and one replay row is
    inserted.  The relation below validates it; nothing here confers authority.
    """
    projection = accepted.private_port.post_state
    added = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
    return replace(
        current,
        height=occurrence.height,
        balances=projection.balances,
        supplies=projection.supplies,
        lane_roots=(
            replace(current.lane_roots[0], state_root=projection.state_root),
            *current.lane_roots[1:],
        ),
        replay_state=tuple(sorted((*current.replay_state, added))),
    )


def _next_witness(
    previous: RuntimeWitness,
    previous_accepted: AssetTransferLaneModuleAcceptedV1,
    previous_post: GlobalEconomicStateV1,
    *,
    height: int,
    amount: int,
    nonce: int,
    op_index: int,
) -> RuntimeWitness:
    """A fresh request from the exact preceding module and global post values."""
    command = AssetTransferCommandV1("asset_transfer", "USD", "alice", "bob", amount, 1)
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=previous_post.chain_id,
        deployment_root=previous_post.deployment_root,
        height=height,
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


class SharedHeightPair:
    """Two accepted transfers at one epoch height over the nonempty witness."""

    def __init__(self, *, height: int) -> None:
        self.first = _runtime_witness(fee_owner="bob", height=height, amount=4)
        self.source = self.first.pre_global
        self.first_accepted = _run_custody_module(self.first)
        first_effects = _normalise(self.first, self.first_accepted)
        # The first pair is adjacent (H -> H + 1), so the standalone projector applies.
        self.first_post = _project(self.first, first_effects, self.first.occurrence)
        assert asdict(self.first_post) == asdict(
            _prospective_post(self.source, self.first.occurrence, self.first_accepted)
        )
        self.second = _next_witness(
            self.first, self.first_accepted, self.first_post,
            height=self.first_post.height, amount=2, nonce=6, op_index=1,
        )
        self.second_accepted = _run_custody_module(self.second)
        self.second_effects = _normalise(self.second, self.second_accepted)
        self.second_post = _prospective_post(
            self.first_post, self.second.occurrence, self.second_accepted,
        )

    def pair(self, index: int) -> AssetTransferGlobalAllocationCandidateV1:
        if index == 0:
            return AssetTransferGlobalAllocationCandidateV1(
                self.first_accepted, self.first.occurrence, self.source, self.first_post,
            )
        return AssetTransferGlobalAllocationCandidateV1(
            self.second_accepted, self.second.occurrence, self.first_post, self.second_post,
        )


def _relation(
    candidate: AssetTransferGlobalAllocationCandidateV1,
    source: GlobalEconomicStateV1,
    index: int,
):
    before = canonical_global_bytes_v1((candidate.predecessor, candidate.current, source))
    result = _epoch_allocation_binding_reject_v1(
        candidate, AssetTransferEpochPositionV1(source, index),
    )
    assert canonical_global_bytes_v1((candidate.predecessor, candidate.current, source)) == before
    return result


def _assert_shared_height_runtime(pair: SharedHeightPair) -> None:
    """The actual epoch-position relation accepts both pairs; standalone paths refuse."""
    source, first_post, second_post = pair.source, pair.first_post, pair.second_post
    assert first_post.height == second_post.height == source.height + 1
    assert pair.first.occurrence.height == pair.second.occurrence.height == source.height + 1
    assert first_post.balances != second_post.balances
    assert (
        [(row.owner, row.asset, row.amount_atoms) for row in first_post.balances]
        == [("alice", "EUR", 9), ("alice", "USD", 35), ("bob", "USD", 10)]
    )
    assert (
        [(row.owner, row.asset, row.amount_atoms) for row in second_post.balances]
        == [("alice", "EUR", 9), ("alice", "USD", 32), ("bob", "USD", 13)]
    )
    assert source.custody == first_post.custody == second_post.custody
    assert source.liabilities == first_post.liabilities == second_post.liabilities
    assert source.oracle_occurrences == first_post.oracle_occurrences == second_post.oracle_occurrences
    assert source.replay_state and first_post.custody and first_post.liabilities
    assert len({row.replay_id for row in second_post.replay_state}) == len(source.replay_state) + 2
    assert all(row in second_post.replay_state for row in first_post.replay_state)
    assert len({
        source.lane_roots[0].state_root, first_post.lane_roots[0].state_root,
        second_post.lane_roots[0].state_root,
    }) == 3
    assert source.lane_roots[1:] == first_post.lane_roots[1:] == second_post.lane_roots[1:]
    assert _relation(pair.pair(0), source, 0) is None
    assert _relation(pair.pair(1), source, 1) is None
    assert _relation(pair.pair(1), source, MAX_EPOCH_COMMANDS_V1 - 1) is None
    # The standalone adjacent relation refuses the shared-height second pair only.
    assert _global_allocation_binding_reject_v1(
        pair.first_accepted, pair.first.occurrence, source, first_post,
    ) is None
    standalone = _global_allocation_binding_reject_v1(
        pair.second_accepted, pair.second.occurrence, first_post, second_post,
    )
    assert standalone is not None
    assert standalone.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT
    # The standalone projector cannot stand in for the epoch path: it requires H + 1
    # relative to its own pre-state and refuses the shared-height occurrence unchanged.
    before = canonical_global_bytes_v1((first_post, pair.second.occurrence))
    with pytest.raises(ValueError, match="^economic effect projection occurrence context mismatch$"):
        project_single_occurrence_global_effects_v1(
            first_post, pair.second_effects, pair.second.occurrence,
        )
    assert canonical_global_bytes_v1((first_post, pair.second.occurrence)) == before


def _rows_view(rows: tuple[EconomicAmountV1, ...]) -> list[list[str]]:
    return [[row.owner, row.asset, row.custody_domain, str(row.amount_atoms)] for row in rows]


def _expected_epoch_observation(
    post: GlobalEconomicStateV1,
    replay_ids: list[str],
    verdict: str,
    occurrences: int,
) -> list[list[str]]:
    replay = {row.replay_id: row.occurrence_id for row in post.replay_state}
    asset_root = next(
        row.state_root for row in post.lane_roots if row.lane_id is LaneIdV1.ASSET_TRANSFER
    )
    return [
        ["STATE_ROOT", post.state_root],
        ["ASSET_LANE_ROOT", asset_root],
        ["HEIGHT", str(post.height)],
        ["WRITER_EPOCH", str(post.writer_epoch)],
        ["VERDICT", verdict],
        ["OCCURRENCES", str(occurrences)],
        *[["REPLAY", key, replay.get(key, "NONE")] for key in replay_ids],
        ["BALANCES"], *_rows_view(post.balances),
        ["CUSTODY"], *_rows_view(post.custody),
        ["LIABILITIES"], *_rows_view(post.liabilities),
        ["SUPPLIES"], *[[row.asset, str(row.amount_atoms)] for row in post.supplies],
    ]


OBSERVERS = f"""
def epochOptionView : Option String → String
  | some value => value
  | none => "NONE"

def epochRowsView (rows : List AmountRow) : List (List String) :=
  rows.map fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]

def epochVerdictView (input : {GLOBAL_INPUT}) : String :=
  match (epochStep input).verdict with
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def epochObserve (input : {GLOBAL_INPUT}) (replayIds : List String) : List (List String) :=
  let state := epochContinuedState input
  [["STATE_ROOT", state.economic.stateRoot],
   ["ASSET_LANE_ROOT", state.economic.laneRoots .assetTransfer],
   ["HEIGHT", toString state.economic.height],
   ["WRITER_EPOCH", toString state.economic.writerEpoch],
   ["VERDICT", epochVerdictView input],
   ["OCCURRENCES", toString (epochStep input).occurrences.length]] ++
   (replayIds.map fun key => ["REPLAY", key, epochOptionView (state.economic.replayState key)]) ++
   [["BALANCES"]] ++ epochRowsView state.economic.balances ++
   [["CUSTODY"]] ++ epochRowsView state.economic.custody ++
   [["LIABILITIES"]] ++ epochRowsView state.economic.liabilities ++
   [["SUPPLIES"]] ++ state.economic.supplies.map (fun row => [row.asset, toString row.amountAtoms])
"""


def _lean_fee_eligible_carried(tag: str, previous: str) -> str:
    """Fee eligibility after carrying the preceding policy rows through the epoch step."""
    return f"""
theorem {tag}_fee_eligible : FeeEligible {tag}Global := by
  intro policy selection
  change policyFor (epochContinuedState {previous}Global).policies "USD" = some policy at selection
  rw [(epochContinuedState_static_frame {previous}Global).2] at selection
  change policyFor {previous}Transfer.pre.policies "USD" = some policy at selection
  simp [{previous}Transfer, policyFor] at selection
  subst policy
  exact Or.inr (by decide)
"""


def _carried_accepted_proof(tag: str, previous: str) -> str:
    """Leaf acceptance of a transfer whose pre-state is the carried Lean state.

    The carried balance table is the sorted output of the first actual leaf; the
    literal rows are the first transfer's exact pre-sort result (4 atoms plus a
    1-atom fee from alice to bob), checked definitionally by `change`.
    """
    return f"""
theorem {tag}_accepted : (step {tag}Transfer).verdict = .accepted := by
  have carriedBalances :
      (epochContinuedState {previous}Global).economic.balances = {tag}Economic.balances := by
    rw [epochContinuedState_accepted {previous}_accepted]
    change Proofs.CanonicalEpochEconomicRowsV1.sortOn
      Proofs.AssetTransferSparseTablesV1.balanceWire
        [⟨"bob", "USD", "accounts", (10 : Int)⟩,
         ⟨"alice", "USD", "accounts", (35 : Int)⟩,
         ⟨"alice", "EUR", "accounts", (9 : Int)⟩] = _
    simp +decide [Proofs.CanonicalEpochEconomicRowsV1.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop,
      {tag}Economic]
  unfold step
  simp only [{tag}Transfer, (epochContinuedState_static_frame {previous}Global).1,
    (epochContinuedState_static_frame {previous}Global).2]
  change (Proofs.AssetTransferSparseTablesV1.step
    (selectedInput {tag}Transfer ⟨"USD", "bob", (1 : Int), true⟩)).verdict = .accepted
  unfold Proofs.AssetTransferSparseTablesV1.step
  simp only [Proofs.AssetTransferSparseTablesV1.leaf,
    Proofs.AssetTransferSparseTablesV1.localState,
    Proofs.AssetTransferSparseTablesV1.checkedBalances,
    selectedInput, {tag}Transfer, carriedBalances,
    (epochContinuedState_static_frame {previous}Global).1]
  decide
"""


def _first_requirements(tag: str) -> str:
    """All fourteen requirement fields at the first position, against the source itself."""
    return f"""
theorem {tag}_requirements :
    EpochRequirements ⟨{tag}Economic, 0⟩ {tag}Transfer.pre {tag}Global := by
  refine {{
    pre := rfl,
    indexBound := by decide,
    targetFits := by unfold FitsU64; decide,
    priorHeight := rfl,
    firstSource := fun _ => rfl,
    sourceContext := ⟨rfl, rfl, rfl, rfl⟩,
    context := ⟨rfl, rfl, rfl, rfl⟩,
    height := rfl,
    freshReplay := by decide,
    freshOccurrence := ?_,
    preLaneRoot := rfl,
    laneRootChanged := by decide,
    commandWellFormed := ⟨by decide, by decide⟩,
    feeEligible := {tag}_fee_eligible }}
  intro replayId prior lookup
  simp only [{tag}Transfer, {tag}Economic, {tag}Replay] at lookup
  split at lookup
  · cases lookup
    decide
  · cases lookup
"""


def _carried_requirements(name: str, tag: str, previous: str, source: str, index: int) -> str:
    """All fourteen requirement fields at a later position, against the carried Lean state."""
    return f"""
theorem {name} :
    EpochRequirements ⟨{source}Economic, {index}⟩
      (epochContinuedState {previous}Global) {tag}Global := by
  have carried := epochContinuedState_accepted (input := {previous}Global) {previous}_accepted
  refine {{
    pre := rfl,
    indexBound := by decide,
    targetFits := by unfold FitsU64; decide,
    priorHeight := ?_,
    firstSource := fun impossible => absurd impossible (by decide),
    sourceContext := ?_,
    context := ?_,
    height := rfl,
    freshReplay := ?_,
    freshOccurrence := ?_,
    preLaneRoot := ?_,
    laneRootChanged := ?_,
    commandWellFormed := ⟨by decide, by decide⟩,
    feeEligible := {tag}_fee_eligible }}
  · rw [carried]
    rfl
  · rw [carried]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [carried]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [carried]
    decide
  · rw [carried]
    intro replayId prior lookup
    change (if replayId = {previous}Occurrence.replayId then some {previous}Occurrence.occurrenceId
      else {previous}Replay replayId) = some prior at lookup
    split at lookup
    · cases lookup
      decide
    · simp only [{previous}Replay] at lookup
      split at lookup
      · cases lookup
        decide
      · cases lookup
  · rw [carried]
    rfl
  · rw [carried]
    decide
"""


def _shared_height_body(pair: SharedHeightPair) -> str:
    """Mirror both transfers, admit the source, chain the epoch attempts and apply the laws."""
    return (
        _lean_mirror(
            pair.first, pair.first_accepted.private_port.post_state.state_root,
            pair.first_post.state_root, "first",
        )
        + _lean_mirror_carried(
            pair.second, pair.second_accepted.private_port.post_state.state_root,
            pair.second_post.state_root, "second", f"{NAMESPACE}.epochContinuedState firstGlobal",
        )
        + _lean_admission("first") + _lean_fee_eligible("first") + _lean_admitted_record("first")
        + _lean_fee_eligible_carried("second", "first")
        + "\ntheorem first_accepted : (step firstTransfer).verdict = .accepted := by decide\n"
        + _carried_accepted_proof("second", "first")
        + _first_requirements("first")
        + _carried_requirements("second_requirements", "second", "first", "first", 1)
        + """
theorem first_invariant : StateInvariant firstTransfer.pre := invariant_of_admitted first_admitted
theorem carried_invariant : StateInvariant (epochContinuedState firstGlobal) :=
  epochContinuation_invariant first_invariant first_requirements

/-- First position: the shared-height bundle and the existing `Verified` record by reuse. -/
example : SharedHeightVerified ⟨firstEconomic, 0⟩ firstGlobal :=
  epochContinuation_verified first_invariant first_requirements first_accepted
example : Verified (pre firstGlobal) (result firstGlobal).plan ⟨[]⟩ ⟨[]⟩ [firstOccurrence]
    (epochSuccessor firstGlobal) :=
  epochContinuation_first_verified first_invariant first_requirements rfl first_accepted
example : epochSuccessor firstGlobal = successor firstGlobal :=
  epochSuccessor_first first_requirements rfl

/-- Later position at the shared height: the bundle and the nine inherited obligations. -/
example : SharedHeightVerified ⟨firstEconomic, 1⟩ secondGlobal :=
  epochContinuation_verified carried_invariant second_requirements second_accepted
example : StateInvariant (epochContinuedState secondGlobal) :=
  epochContinuation_invariant carried_invariant second_requirements
example : (epochSuccessor secondGlobal).height = (epochSuccessor firstGlobal).height :=
  (epochContinuation_verified carried_invariant second_requirements second_accepted).sharedHeight
example : (epochSuccessor secondGlobal).height ≠ (epochContinuedState firstGlobal).economic.height + 1 := by
  rw [epochContinuedState_accepted first_accepted]
  decide

/-- The finite prefix of both accepted attempts and its derived invariants. -/
theorem chain_one : EpochPrefix firstTransfer.pre 1 [firstOccurrence]
    (epochContinuedState firstGlobal) :=
  EpochPrefix.cons (source := firstTransfer.pre) (next := firstGlobal) EpochPrefix.nil
    first_requirements first_accepted
theorem chain_two : EpochPrefix firstTransfer.pre 2 [firstOccurrence, secondOccurrence]
    (epochContinuedState secondGlobal) :=
  EpochPrefix.cons (source := firstTransfer.pre) (next := secondGlobal) chain_one
    second_requirements second_accepted
example : StateInvariant (epochContinuedState secondGlobal) :=
  epochPrefix_invariant first_invariant chain_two
example : [firstOccurrence, secondOccurrence].length = 2 ∧ 2 ≤ maxEpochCommands :=
  epochPrefix_length chain_two
example : (epochContinuedState secondGlobal).economic.height =
    expectedPriorHeight ⟨firstEconomic, 2⟩ :=
  (epochPrefix_metadata chain_two).2.2.2.1
example : (epochContinuedState secondGlobal).economic.replayState =
    [firstOccurrence, secondOccurrence].foldl insertReplay firstEconomic.replayState :=
  (epochPrefix_metadata chain_two).2.2.2.2
example : SameContext firstEconomic (epochContinuedState secondGlobal).economic :=
  (epochPrefix_metadata chain_two).2.2.1
example : 1 ≤ 2 ∧ 2 ≤ maxEpochCommands ∧
    (epochContinuedState secondGlobal).economic.height = firstTransfer.pre.economic.height + 1 :=
  epochPrefix_nonempty chain_two (by decide)
example : SharedHeightVerified ⟨firstEconomic, 1⟩ secondGlobal ∧
    (1 = 0 → Verified (pre secondGlobal) (result secondGlobal).plan ⟨[]⟩ ⟨[]⟩ [secondOccurrence]
      (epochSuccessor secondGlobal)) :=
  epochPrefix_next_verified first_invariant chain_one second_requirements second_accepted
"""
    )


def _index_and_freshness_controls(source_height: int) -> str:
    """Each control refutes exactly one named requirement clause."""
    return (f"""
/-- Index controls: first-versus-later and the 63/64 boundary. -/
example : ¬ EpochRequirements ⟨firstEconomic, 1⟩ firstTransfer.pre firstGlobal := by
  intro requirements
  exact absurd requirements.priorHeight (by decide)
example : ¬ EpochRequirements ⟨firstEconomic, 0⟩ (epochContinuedState firstGlobal) secondGlobal := by
  intro requirements
  have prior := requirements.priorHeight
  rw [epochContinuedState_accepted first_accepted] at prior
  exact absurd prior (by decide)
example : ¬ EpochRequirements ⟨firstEconomic, {MAX_EPOCH_COMMANDS_V1}⟩
    (epochContinuedState firstGlobal) secondGlobal := by
  intro requirements
  exact absurd requirements.indexBound (by decide)
"""
    + _carried_requirements(
        "index63_requirements", "second", "first", "first", MAX_EPOCH_COMMANDS_V1 - 1,
    )
    + f"""
example : SharedHeightVerified ⟨firstEconomic, {MAX_EPOCH_COMMANDS_V1 - 1}⟩ secondGlobal :=
  epochContinuation_verified carried_invariant index63_requirements second_accepted

/-- Freshness, height and context controls at the later position. -/
def reusedReplayGlobal : {GLOBAL_INPUT} :=
  {{ secondGlobal with occurrence := {{ secondOccurrence with replayId := firstOccurrence.replayId }} }}
example : ¬ EpochRequirements ⟨firstEconomic, 1⟩ (epochContinuedState firstGlobal)
    reusedReplayGlobal := by
  intro requirements
  have fresh := requirements.freshReplay
  rw [epochContinuedState_accepted first_accepted] at fresh
  exact absurd fresh (by decide)
def reusedOccurrenceIdGlobal : {GLOBAL_INPUT} :=
  {{ secondGlobal with
      occurrence := {{ secondOccurrence with occurrenceId := firstOccurrence.occurrenceId }} }}
example : ¬ EpochRequirements ⟨firstEconomic, 1⟩ (epochContinuedState firstGlobal)
    reusedOccurrenceIdGlobal := by
  intro requirements
  have lookup : (epochContinuedState firstGlobal).economic.replayState firstOccurrence.replayId =
      some firstOccurrence.occurrenceId := by
    rw [epochContinuedState_accepted first_accepted]
    decide
  exact requirements.freshOccurrence firstOccurrence.replayId firstOccurrence.occurrenceId lookup rfl
def wrongHeightGlobal : {GLOBAL_INPUT} :=
  {{ secondGlobal with occurrence := {{ secondOccurrence with height := {source_height + 2} }} }}
example : ¬ EpochRequirements ⟨firstEconomic, 1⟩ (epochContinuedState firstGlobal)
    wrongHeightGlobal := by
  intro requirements
  exact absurd requirements.height (by decide)
def foreignGlobal : {GLOBAL_INPUT} :=
  {{ secondGlobal with occurrence := {{ secondOccurrence with chainId := "foreign" }} }}
example : ¬ EpochRequirements ⟨firstEconomic, 1⟩ (epochContinuedState firstGlobal)
    foreignGlobal := by
  intro requirements
  have same : foreignGlobal.occurrence.chainId = firstEconomic.chainId :=
    requirements.context.1.trans requirements.sourceContext.1
  exact absurd same (by decide)
"""
    )


def _replay_ids(pair: SharedHeightPair) -> list[str]:
    return [
        *(row.replay_id for row in pair.source.replay_state),
        pair.first.occurrence.replay_id, pair.second.occurrence.replay_id, "absent-replay",
    ]


def test_two_actual_transfers_share_the_epoch_height_and_close_the_state(
    lean: LeanSubject,
) -> None:
    pair = SharedHeightPair(height=7)
    _assert_shared_height_runtime(pair)
    # Swapped position claims are refused by the actual relation on both sides.
    for candidate, index in ((pair.pair(0), 1), (pair.pair(1), 0)):
        rejected = _relation(candidate, pair.source, index)
        assert rejected is not None
        assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT
    # Wrong height, wrong context, replay reuse: each refused by the named guard.
    wrong_height = replace(pair.second.occurrence, height=pair.source.height + 2)
    wrong_context = replace(pair.second.occurrence, chain_id="foreign")
    for occurrence, code in (
        (wrong_height, GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT),
        (wrong_context, GlobalAllocationBindingRejectCodeV1.GLOBAL_CONTEXT_DRIFT),
    ):
        rejected = _relation(AssetTransferGlobalAllocationCandidateV1(
            pair.second_accepted, occurrence, pair.first_post, pair.second_post,
        ), pair.source, 1)
        assert rejected is not None and rejected.code is code
    reuse = _next_witness(
        pair.first, pair.first_accepted, pair.first_post,
        height=pair.first_post.height, amount=2, nonce=5, op_index=1,
    )
    assert reuse.occurrence.replay_id == pair.first.occurrence.replay_id
    reuse_accepted = _run_custody_module(reuse)
    # A duplicate replay key is unrepresentable in the state constructor itself.
    with pytest.raises(ValueError, match="replay state must be canonically ordered and unique"):
        _prospective_post(pair.first_post, reuse.occurrence, reuse_accepted)
    reuse_post = replace(
        _prospective_post(pair.first_post, pair.second.occurrence, reuse_accepted),
        replay_state=pair.first_post.replay_state,
    )
    rejected = _relation(AssetTransferGlobalAllocationCandidateV1(
        reuse_accepted, reuse.occurrence, pair.first_post, reuse_post,
    ), pair.source, 1)
    assert rejected is not None
    assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_REPLAY_CONTINUITY_DRIFT
    with pytest.raises(ValueError):
        AssetTransferEpochPositionV1(pair.source, MAX_EPOCH_COMMANDS_V1)
    assert AssetTransferEpochPositionV1(pair.source, MAX_EPOCH_COMMANDS_V1 - 1).occurrence_index == 63

    replay_ids = _replay_ids(pair)
    lean_ids = "[" + ", ".join(json.dumps(key) for key in replay_ids) + "]"
    body = (
        _shared_height_body(pair)
        + _index_and_freshness_controls(pair.source.height)
        + OBSERVERS
        + f"#eval IO.println (reprStr (reprStr (epochObserve firstGlobal {lean_ids})))\n"
        + f"#eval IO.println (reprStr (reprStr (epochObserve secondGlobal {lean_ids})))\n"
    )
    decoded = _decode(_probe(lean, "EpochStateClosureTwoTransfers", body))
    assert decoded == [
        _expected_epoch_observation(pair.first_post, replay_ids, "ACCEPTED", 1),
        _expected_epoch_observation(pair.second_post, replay_ids, "ACCEPTED", 1),
    ]


def test_rejected_second_transfer_has_exact_no_effect_on_the_carried_state(
    lean: LeanSubject,
) -> None:
    pair = SharedHeightPair(height=7)
    rejected = _next_witness(
        pair.first, pair.first_accepted, pair.first_post,
        height=pair.first_post.height, amount=0, nonce=7, op_index=2,
    )
    before = canonical_global_bytes_v1(rejected.module_input.to_canonical())
    global_before = canonical_global_bytes_v1(rejected.pre_global.to_canonical())
    result = transition_asset_transfer_lane_module_custody_v1(rejected.module_input)
    assert canonical_global_bytes_v1(rejected.module_input.to_canonical()) == before
    assert canonical_global_bytes_v1(rejected.pre_global.to_canonical()) == global_before
    assert type(result) is AssetTransferRejectedV1
    assert result.code is AssetTransferRejectCodeV1.ZERO_AMOUNT
    assert result.effects == GlobalEconomicEffectPlanV1.empty()
    assert result.pre_state_root == result.post_state_root
    assert result.pre_state_root == rejected.module_input.pre_state.state_root
    # No accepted value exists, so no prospective disclosure and no epoch pair can be formed;
    # the carried global state is untouched.
    assert rejected.pre_global == pair.first_post

    replay_ids = [*_replay_ids(pair), rejected.occurrence.replay_id]
    lean_ids = "[" + ", ".join(json.dumps(key) for key in replay_ids) + "]"
    body = (
        _lean_mirror(
            pair.first, pair.first_accepted.private_port.post_state.state_root,
            pair.first_post.state_root, "first",
        )
        + _lean_mirror_carried(
            rejected, _root(0xCC), _root(0xDD), "rejected",
            f"{NAMESPACE}.epochContinuedState firstGlobal",
        )
        + _lean_admission("first") + _lean_fee_eligible("first") + _lean_admitted_record("first")
        + _lean_fee_eligible_carried("rejected", "first")
        + "\ntheorem first_accepted : (step firstTransfer).verdict = .accepted := by decide\n"
        + "theorem rejected_leaf : (step rejectedTransfer).verdict = .rejected .zeroAmount := by decide\n"
        + _first_requirements("first")
        + _carried_requirements("rejected_requirements", "rejected", "first", "first", 1)
        + """
theorem first_invariant : StateInvariant firstTransfer.pre := invariant_of_admitted first_admitted
theorem carried_invariant : StateInvariant (epochContinuedState firstGlobal) :=
  epochContinuation_invariant first_invariant first_requirements
example : epochContinuedState rejectedGlobal = epochContinuedState firstGlobal :=
  epochContinuedState_rejected rejected_leaf
example : epochStep rejectedGlobal = ⟨.rejected .zeroAmount, pre rejectedGlobal, EffectPlan.empty, []⟩ :=
  epochStep_rejected_exact rejected_leaf
example : StateInvariant (epochContinuedState rejectedGlobal) :=
  epochContinuation_invariant carried_invariant rejected_requirements
example : (epochContinuedState rejectedGlobal).economic.replayState rejectedOccurrence.replayId =
    none := by
  rw [epochContinuedState_rejected rejected_leaf]
  show (epochContinuedState firstGlobal).economic.replayState rejectedOccurrence.replayId = none
  rw [epochContinuedState_accepted (input := firstGlobal) first_accepted]
  decide
/-- A rejected attempt extends no chain: only the accepted first attempt is chained. -/
theorem chain_one : EpochPrefix firstTransfer.pre 1 [firstOccurrence]
    (epochContinuedState firstGlobal) :=
  EpochPrefix.cons (source := firstTransfer.pre) (next := firstGlobal) EpochPrefix.nil
    first_requirements first_accepted
example : (epochContinuedState firstGlobal).economic.height = expectedPriorHeight ⟨firstEconomic, 1⟩ :=
  (epochPrefix_metadata chain_one).2.2.2.1
"""
        + OBSERVERS
        + f"#eval IO.println (reprStr (reprStr (epochObserve rejectedGlobal {lean_ids})))\n"
    )
    decoded = _decode(_probe(lean, "EpochStateClosureRejectedContinuation", body))
    assert decoded == [_expected_epoch_observation(pair.first_post, replay_ids, "ZERO_AMOUNT", 0)]


def test_maximum_target_height_admits_the_shared_second_transfer_and_refuses_overflow(
    lean: LeanSubject,
) -> None:
    pair = SharedHeightPair(height=MAX_U64_V1 - 1)
    _assert_shared_height_runtime(pair)
    assert pair.first_post.height == pair.second_post.height == MAX_U64_V1
    # Overflow refusals: neither an occurrence nor a state can name MAX_U64 + 1.
    with pytest.raises(ValueError, match="^occurrence height must fit an unsigned 64-bit integer$"):
        replace(pair.second.occurrence, height=MAX_U64_V1 + 1)
    with pytest.raises(ValueError, match="^global state height must fit an unsigned 64-bit integer$"):
        replace(pair.first_post, height=MAX_U64_V1 + 1)
    # A source already at the maximum has no admissible target height at all.
    overflow_source = replace(pair.source, height=MAX_U64_V1)
    rejected = _relation(pair.pair(0), overflow_source, 0)
    assert rejected is not None
    assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT

    replay_ids = _replay_ids(pair)
    lean_ids = "[" + ", ".join(json.dumps(key) for key in replay_ids) + "]"
    body = (
        _shared_height_body(pair)
        + """
example : (epochContinuedState firstGlobal).economic.height = maxU64 := by
  rw [epochContinuedState_accepted first_accepted]
  decide
example : (epochContinuedState secondGlobal).economic.height = maxU64 := by
  rw [epochContinuedState_accepted second_accepted]
  decide
/-- The standalone continuation has no admissible next height here, while the epoch position
admits the shared-height second transfer. -/
example : ¬ FitsU64 ((epochContinuedState firstGlobal).economic.height + 1) := by
  rw [epochContinuedState_accepted first_accepted]
  unfold FitsU64
  decide
example : ¬ ContinuationRequirements (epochContinuedState firstGlobal) secondGlobal := by
  intro requirements
  have fits := requirements.heightFits
  rw [epochContinuedState_accepted first_accepted] at fits
  exact (by unfold FitsU64; decide : ¬ FitsU64 ((epochSuccessor firstGlobal).height + 1)) fits
def overflowSource : GlobalState := { firstEconomic with height := maxU64 }
example : ¬ EpochRequirements ⟨overflowSource, 0⟩ firstTransfer.pre firstGlobal := by
  intro requirements
  exact absurd requirements.targetFits (by unfold FitsU64; decide)
"""
        + OBSERVERS
        + f"#eval IO.println (reprStr (reprStr (epochObserve secondGlobal {lean_ids})))\n"
    )
    decoded = _decode(_probe(lean, "EpochStateClosureMaximumHeight", body))
    assert decoded == [_expected_epoch_observation(pair.second_post, replay_ids, "ACCEPTED", 1)]


# ---------------------------------------------------------------------------------------
# The actual epoch allocation checker: all-or-reject over two shared-height commands.


def _epoch_mutant(candidate, index: int, **changes):
    disclosures = candidate.route_state_disclosures
    mutated = replace(disclosures[index].post_state, **changes)
    return replace(
        candidate,
        post_state=mutated if index == len(disclosures) - 1 else candidate.post_state,
        route_state_disclosures=(
            *disclosures[:index], replace(disclosures[index], post_state=mutated),
            *disclosures[index + 1:],
        ),
    )


def test_actual_epoch_checker_accepts_two_shared_height_commands_and_rejects_mutants() -> None:
    candidate, evidence = _epoch_fixture(count=2)
    subject = (candidate.pre_state, candidate.post_state, candidate.command_occurrences)
    before = canonical_global_bytes_v1(subject)
    accepted = _check_epoch(candidate, evidence)
    assert isinstance(accepted, epoch_consumer.AssetTransferEpochAllocationAcceptedV1)
    assert len(accepted.checks) == 2
    disclosures = candidate.route_state_disclosures
    assert (
        disclosures[0].post_state.height == disclosures[1].post_state.height
        == candidate.pre_state.height + 1
    )
    assert all(occurrence.height == candidate.pre_state.height + 1
               for occurrence in candidate.command_occurrences)
    assert accepted.post_state_root == disclosures[1].post_state.state_root
    # Height double increment at index 1: the checker rejects with no partial checks.
    bumped = _epoch_mutant(candidate, 1, height=disclosures[1].post_state.height + 1)
    rejected = _check_epoch(bumped, evidence)
    assert isinstance(rejected, epoch_consumer.AssetTransferEpochAllocationRejectedV1)
    assert rejected.code is epoch_consumer.AssetTransferEpochAllocationRejectCodeV1.GLOBAL_FRAGMENT_REJECTED
    assert rejected.occurrence_index == 1
    assert rejected.cause is not None
    assert rejected.cause.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT
    assert not hasattr(rejected, "checks")
    # Replay omission at index 1: the replay continuity guard rejects, again with no checks.
    omitted = _epoch_mutant(candidate, 1, replay_state=disclosures[0].post_state.replay_state)
    rejected = _check_epoch(omitted, evidence)
    assert isinstance(rejected, epoch_consumer.AssetTransferEpochAllocationRejectedV1)
    assert rejected.code is epoch_consumer.AssetTransferEpochAllocationRejectCodeV1.GLOBAL_FRAGMENT_REJECTED
    assert rejected.occurrence_index == 1
    assert rejected.cause is not None
    assert rejected.cause.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_REPLAY_CONTINUITY_DRIFT
    assert not hasattr(rejected, "checks")
    assert canonical_global_bytes_v1(subject) == before


# ---------------------------------------------------------------------------------------
# Constructor mutants of the ordinary law.

MUTANTS = (
    (
        "height_double_increment",
        "    stateRoot := input.postStateRoot\n    height := input.occurrence.height\n",
        "    stateRoot := input.postStateRoot\n    height := (X.pre input).height + 1\n",
        "toString (epochSuccessor probeInput).height",
        "8",
        "9",
        ("epochSuccessor_metadata",),
    ),
    (
        "replay_omission",
        "    laneRoots := X.successorRoots (X.pre input) input.postLaneRoot\n"
        "    replayState := X.insertReplay (X.pre input).replayState input.occurrence }",
        "    laneRoots := X.successorRoots (X.pre input) input.postLaneRoot\n"
        "    replayState := (X.pre input).replayState }",
        "epochOptionView ((epochSuccessor probeInput).replayState probeOccurrence.replayId)",
        "occurrence-new",
        "NONE",
        ("epochSuccessor_metadata", "epochSuccessor_replay_registry"),
    ),
)

MUTANT_PROBE = """
def probeOccurrence : G.CommandOccurrence :=
  ⟨"occurrence-new", "replay-new", "chain", "deployment-root", "profile-root", "state-root", 8⟩
def probeInput : X.Input :=
  ⟨⟨⟨"release", "alice"⟩, ⟨"asset_transfer", "USD", "alice", "bob", 4, 1⟩,
    ⟨"release", [], { staticGlobalState with height := 8 }⟩⟩,
   probeOccurrence, "lane-pre", "lane-post", "state-post"⟩
def epochOptionView : Option String → String
  | some value => value
  | none => "NONE"
#eval IO.println (reprStr (reprStr [OBSERVATION_TERM]))

end AssetTransferEpochStateClosureV1
end Proofs
"""


def _theorem_lines(source: str, name: str) -> tuple[int, int]:
    lines = source.splitlines()
    start = next(index for index, line in enumerate(lines, 1) if line.startswith(f"theorem {name}"))
    end = next(
        index for index, line in enumerate(lines[start:], start + 1)
        if re.match(r"^(?:theorem|def|structure|inductive|/--|/-!|end) ", line + " ")
    )
    return start, end


@pytest.mark.parametrize(
    ("name", "old", "new", "observation", "good_value", "bad_value", "failing_theorems"), MUTANTS,
)
def test_constructor_mutants_are_killed_by_the_shared_height_law(
    lean: LeanSubject, name: str, old: str, new: str, observation: str, good_value: str,
    bad_value: str, failing_theorems: tuple[str, ...],
) -> None:
    captured_path = lean.source / "Proofs" / f"{MODULE}.lean"
    original_path = PROJECT / "Proofs" / f"{MODULE}.lean"
    original_bytes = original_path.read_bytes()
    assert captured_path.read_bytes() == original_bytes
    source = captured_path.read_text()
    assert source.count(old) == 1
    mutated = source.replace(old, new, 1)
    cut = "/-! ## Metadata and frame -/"
    assert source.count(cut) == 1
    # Definitions alone reveal the good and the bad value; a proof error alone is never the
    # mutation oracle.
    for label, text, expected in (("law", source, good_value), ("mutant", mutated, bad_value)):
        prefix_path = lean.source / f"Mutant_{name}_{label}_prefix.lean"
        prefix_path.write_text(
            text[:text.index(cut)] + MUTANT_PROBE.replace("OBSERVATION_TERM", observation),
        )
        prefix_result = _compile(lean, prefix_path)
        assert prefix_result.returncode == 0, prefix_result.stdout + prefix_result.stderr
        assert json.loads(json.loads(prefix_result.stdout.strip())) == [expected]
    assert good_value != bad_value

    full_path = lean.source / f"Mutant_{MODULE}_{name}.lean"
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
    for theorem in failing_theorems:
        start, end = _theorem_lines(mutated, theorem)
        assert any(start <= line < end for line in errors), (theorem, output)
    assert captured_path.read_bytes() == original_bytes
    assert original_path.read_bytes() == original_bytes
