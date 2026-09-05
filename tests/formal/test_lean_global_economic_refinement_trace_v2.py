"""Bind an actual V2 refinement history to the Lean finite-trace model.

Each Lean dependency is freshly compiled with the pinned standalone toolchain.
The runtime history below is produced by the live checker in
``src.core.global_economic_refinement_outcome_v2``; its observable projection is
then rendered into the Lean trace oracle that ``run_observation_is_ok`` proves
every model run passes.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from collections.abc import Callable
from dataclasses import dataclass, replace
from pathlib import Path
from typing import NamedTuple

import pytest

from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_refinement_outcome_v2 import (
    GlobalEconomicRefinementAcceptedV2,
    GlobalEconomicRefinementRejectCodeV2,
    GlobalEconomicRefinementRejectedV2,
    refine_global_economic_state_effects_outcome_v2,
)
from src.core.global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementCandidateV2,
)
from src.core.global_economic_state_v2 import (
    GlobalEconomicStateV2,
    LaneStateRootV2,
    ReplayStateV2,
)
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    hash_global_v2,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "lean-mathlib"
MODULE = "GlobalEconomicRefinementTraceV2"
NAMESPACE = f"Proofs.{MODULE}"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
DEPENDENCIES = ("GlobalSettlementCoreV2", "GlobalEconomicStateRefinementV2")
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

# The bundle is the artifact this file advertises.  `TRACE_THEOREMS` pins the
# standalone theorems, but a conjunct can be dropped from the bundle while every
# underlying theorem survives, so the field list is pinned separately and a Lean
# probe reconstructs the structure field by field.
OUTBOX_CONJUNCT_FIELD = (
    "  outboxClosed : ∀ plan ∈ run.stepEffectPlans, plan.externalOutboxEnqueue = []\n"
)
OUTBOX_CONJUNCT_PROOF = "  outboxClosed := run_keeps_outbox_closed_before_o009 run\n"

TRACE_REFINES_FIELDS = (
    "committedVerified",
    "committedChain",
    "fixedContext",
    "heightAccounting",
    "replayMonotone",
    "replayIdsConsumedOnce",
    "occurrenceIdsConsumedOnce",
    "outboxClosed",
    "zeroOccurrenceStatic",
    "uncommittedIsCompleteNoOp",
)

TRACE_THEOREMS = (
    "committedHeightSteps_cons",
    "height_step_arithmetic",
    "verified_replay_registry_is_monotone",
    "verified_records_consumed_occurrence",
    "verified_consumed_replay_id_was_unset",
    "verified_consumed_occurrence_id_is_fresh",
    "string_lt_implies_ne",
    "fixedContext_refl",
    "fixedContext_trans",
    "run_committed_transitions_are_verified",
    "run_committed_transitions_chain",
    "run_preserves_fixed_context",
    "run_height_counts_committed_advancing_steps",
    "run_replay_registry_is_monotone",
    "run_consumed_replay_ids_start_unset",
    "run_consumed_occurrence_ids_are_fresh_at_start",
    "run_consumes_each_replay_id_at_most_once",
    "run_consumes_each_occurrence_id_at_most_once",
    "run_keeps_outbox_closed_before_o009",
    "run_committed_step_without_occurrences_is_static",
    "run_without_committed_steps_is_complete_no_op",
    "run_preserves_state_quantities",
    "run_preserves_owned_supply",
    "run_preserves_liability_backing",
    "run_keeps_oracles_within_global_height",
    "every_run_refines",
    "committing_post_state_quantities_admitted",
    "committing_step_verified",
    "witness_run_has_three_steps_and_two_committed",
    "witness_run_advances_height_exactly_once",
    "witness_run_consumes_one_replay_id",
    "witness_run_consumes_one_occurrence_id",
    "witness_run_height_accounting_is_nonvacuous",
    "observe_accepted",
    "observe_rejected",
    "committed_accepted",
    "committed_rejected",
    "verified_observed_step_ok",
    "run_observation_step_lists_agree",
    "run_observation_steps_are_ok",
    "run_observation_is_chained",
    "run_observation_is_ok",
    "witness_run_observation_is_ok",
)

# A rejected step that silently moves the state root.  The chain and height
# clauses accept it; only the rejection no-op clause refuses it.
MUTATING_REJECTION_TRACE = (
    '#eval observedTraceOk "a" 7\n'
    '  [ { preStateRoot := "a", postStateRoot := "b", preHeight := 7, postHeight := 7,\n'
    "      committed := false, replayIds := [], occurrenceIds := [] } ]\n"
    '  "b" 7\n'
)

CHAIN_ID = "zeno-v2-trace"
DEPLOYMENT_ROOT = f"0x{901:064x}"
PROFILE_ROOT = f"0x{902:064x}"
WRITER_EPOCH = 4
START_HEIGHT = 7
ASSET = "USD"
TOTAL_SUPPLY = 10


# --------------------------------------------------------------------------
# Pinned standalone Lean compilation
# --------------------------------------------------------------------------


def _check(
    path: Path,
    library: Path,
    output: Path | None = None,
    source_root: Path = LEAN_ROOT,
    warnings_as_errors: bool = True,
) -> subprocess.CompletedProcess[str]:
    environment = dict(os.environ)
    environment["LEAN_PATH"] = str(library)
    arguments = ["lean"]
    if warnings_as_errors:
        arguments.append("-DwarningAsError=true")
    if output is not None:
        arguments += ["-R", str(source_root), "-o", str(output)]
    arguments.append(str(path))
    return subprocess.run(
        arguments,
        cwd=source_root,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=300,
    )


def _assert_pinned_toolchain(source_root: Path) -> None:
    """`lean` on PATH is not the pin; elan selects it from the working directory."""

    assert (source_root / "lean-toolchain").read_text().strip() == PINNED_TOOLCHAIN
    version = subprocess.run(
        ["lean", "--version"],
        cwd=source_root,
        capture_output=True,
        text=True,
        check=True,
        timeout=30,
    )
    assert "version 4.27.0," in version.stdout, version.stdout


def _build_library(destination: Path, source_root: Path) -> Path:
    (destination / "Proofs").mkdir(parents=True, exist_ok=True)
    for name in (*DEPENDENCIES, MODULE):
        source = source_root / "Proofs" / f"{name}.lean"
        result = _check(
            source,
            destination,
            destination / "Proofs" / f"{name}.olean",
            source_root=source_root,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout.strip() == ""
        assert result.stderr.strip() == ""
    return destination


@pytest.fixture(scope="module")
def lean_source_root(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """Capture the pinned trace source before compiling any test-local artifacts."""

    source_root = tmp_path_factory.mktemp("trace-v2-source")
    (source_root / "Proofs").mkdir()
    (source_root / "lean-toolchain").write_bytes((LEAN_ROOT / "lean-toolchain").read_bytes())
    for name in (*DEPENDENCIES, MODULE):
        source_bytes = (LEAN_ROOT / "Proofs" / f"{name}.lean").read_bytes()
        captured = source_root / "Proofs" / f"{name}.lean"
        captured.write_bytes(source_bytes)
        assert captured.read_bytes() == source_bytes
    _assert_pinned_toolchain(source_root)
    return source_root


def _trace_source(source_root: Path) -> Path:
    return source_root / "Proofs" / f"{MODULE}.lean"


@pytest.fixture(scope="module")
def lean_library(lean_source_root: Path, tmp_path_factory: pytest.TempPathFactory) -> Path:
    assert shutil.which("lean") is not None, "pinned Lean installation required"
    return _build_library(tmp_path_factory.mktemp("trace-v2-imports"), lean_source_root)


def _structure_fields(source: str, name: str) -> tuple[str, ...]:
    body = re.search(
        rf"^structure {name}.*?\bwhere\n(?P<body>.*?)(?=\n(?:theorem|def|structure|inductive|end)\b)",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert body is not None, name
    return tuple(re.findall(r"^  ([a-zA-Z][A-Za-z0-9]*) :", body.group("body"), re.MULTILINE))


def _instance_assignments(source: str, name: str) -> tuple[str, ...]:
    body = re.search(
        rf"^theorem {name}.*?\bwhere\n(?P<body>.*?)(?=\n(?:theorem|def|structure|inductive|end|/-)\b)",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert body is not None, name
    return tuple(re.findall(r"^  ([a-zA-Z][A-Za-z0-9]*) :=", body.group("body"), re.MULTILINE))


def _declarations(source: str) -> str:
    return re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)


def _eval_lines(
    lean_library: Path,
    tmp_path: Path,
    name: str,
    body: str,
    source_root: Path = LEAN_ROOT,
    warnings_as_errors: bool = True,
) -> list[str]:
    probe = tmp_path / f"{name}.lean"
    probe.write_text(
        f"import {NAMESPACE}\nopen {NAMESPACE}\n{body}",
        encoding="utf-8",
    )
    result = _check(
        probe,
        lean_library,
        source_root=source_root,
        warnings_as_errors=warnings_as_errors,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr.strip() == ""
    return result.stdout.splitlines()


# --------------------------------------------------------------------------
# Actual runtime history
# --------------------------------------------------------------------------


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_roots() -> tuple[LaneStateRootV2, ...]:
    return tuple(
        LaneStateRootV2(
            lane_id=lane,
            module_release_id=_root(index + 1),
            enabled=lane is not LaneIdV2.EXTERNAL_CUSTODY,
            state_root=_root(index + 201),
        )
        for index, lane in enumerate(ALL_LANE_IDS_V2)
    )


def _state(
    height: int,
    balances: tuple[tuple[str, int], ...],
    replay: tuple[ReplayStateV2, ...],
) -> GlobalEconomicStateV2:
    return GlobalEconomicStateV2(
        chain_id=CHAIN_ID,
        deployment_root=DEPLOYMENT_ROOT,
        writer_epoch=WRITER_EPOCH,
        height=height,
        profile_root=PROFILE_ROOT,
        lane_roots=_lane_roots(),
        balances=tuple(
            EconomicAmountV2(owner, ASSET, "accounts", atoms) for owner, atoms in balances
        ),
        supplies=(AssetSupplyV2(ASSET, TOTAL_SUPPLY),),
        replay_state=replay,
        history_root=ZERO_ROOT_V2,
    )


def _occurrence(
    height: int,
    subject: str,
    nonce: int,
    pre_state_root: str,
    distinguisher: int,
) -> EconomicCommandOccurrenceV2:
    return EconomicCommandOccurrenceV2(
        chain_id=CHAIN_ID,
        deployment_root=DEPLOYMENT_ROOT,
        height=height,
        tx_index=0,
        op_index=0,
        command_kind="trace_transfer",
        command_body_hash=_root(700 + distinguisher),
        route_release_id=_root(750 + distinguisher),
        subject_id=subject,
        grant_root=_root(780 + distinguisher),
        nonce=nonce,
        profile_root=PROFILE_ROOT,
        pre_state_root=pre_state_root,
        consumed_object_ids=(),
    )


def _transfer_plan(
    occurrence_id: str,
    sender: str,
    recipient: str,
    atoms: int,
) -> GlobalEconomicEffectPlanV2:
    rows = (
        EconomicEffectRowV2(
            EconomicEffectKindV2.ACCOUNT_MOVEMENT, sender, ASSET, "accounts", -atoms
        ),
        EconomicEffectRowV2(
            EconomicEffectKindV2.ACCOUNT_MOVEMENT, recipient, ASSET, "accounts", atoms
        ),
    )
    conservation = (
        AssetConservationRowV2(ASSET, TOTAL_SUPPLY, TOTAL_SUPPLY, TOTAL_SUPPLY, TOTAL_SUPPLY, 0, 0),
    )
    return GlobalEconomicEffectPlanV2(
        tuple(sorted(rows, key=lambda row: row.key)),
        conservation,
        (),
        (),
        (occurrence_id,),
        (),
    )


class RuntimeStep(NamedTuple):
    """One submitted candidate and its checker-returned outcome."""

    candidate: GlobalEconomicStateEffectRefinementCandidateV2
    outcome: GlobalEconomicRefinementAcceptedV2 | GlobalEconomicRefinementRejectedV2


def _submitted_step(
    pre: GlobalEconomicStateV2,
    post: GlobalEconomicStateV2,
    plan: GlobalEconomicEffectPlanV2,
    occurrences: tuple[EconomicCommandOccurrenceV2, ...],
) -> RuntimeStep:
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        pre,
        post,
        plan,
        occurrences,
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )
    return RuntimeStep(
        candidate,
        refine_global_economic_state_effects_outcome_v2(candidate),
    )


def _replay_rows(*pairs: tuple[str, str]) -> tuple[ReplayStateV2, ...]:
    return tuple(
        ReplayStateV2(replay_id, occurrence_id)
        for replay_id, occurrence_id in sorted(pairs, key=lambda pair: pair[0])
    )


class RuntimeHistory(NamedTuple):
    start: GlobalEconomicStateV2
    middle: GlobalEconomicStateV2
    final: GlobalEconomicStateV2
    first: EconomicCommandOccurrenceV2
    reanchored_replay: EconomicCommandOccurrenceV2
    stale: EconomicCommandOccurrenceV2
    second: EconomicCommandOccurrenceV2
    steps: tuple[RuntimeStep, ...]


@dataclass
class ObservedStep:
    """Exactly the fields the Lean `ObservedStep` record carries."""

    pre_state_root: str
    post_state_root: str
    pre_height: int
    post_height: int
    committed: bool
    replay_ids: list[str]
    occurrence_ids: list[str]


def _actual_replay_insertions(
    pre: GlobalEconomicStateV2,
    post: GlobalEconomicStateV2,
) -> tuple[ReplayStateV2, ...]:
    """Derive newly recorded replay mappings from immutable endpoint snapshots."""

    pre_by_replay = {row.replay_id: row for row in pre.replay_state}
    post_by_replay = {row.replay_id: row for row in post.replay_state}
    assert len(pre_by_replay) == len(pre.replay_state)
    assert len(post_by_replay) == len(post.replay_state)
    assert set(pre_by_replay).issubset(post_by_replay)
    for replay_id, row in pre_by_replay.items():
        assert post_by_replay[replay_id] == row
    return tuple(
        sorted(
            (row for replay_id, row in post_by_replay.items() if replay_id not in pre_by_replay),
            key=lambda row: row.occurrence_id,
        )
    )


def _expected_state_delta_root(
    pre: GlobalEconomicStateV2,
    post: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
    terminal_plan: GlobalTerminalObligationPlanV2,
    oracle_plan: GlobalOracleOccurrencePlanV2,
    replay_insertions: tuple[ReplayStateV2, ...],
) -> str:
    """Recompute the exact state-delta commitment from submitted data."""

    return hash_global_v2(
        "global-economic-state-delta-v2",
        {
            "pre_state_root": pre.state_root,
            "post_state_root": post.state_root,
            "effect_plan_root": effect_plan.effect_plan_root,
            "lane_writes": effect_plan.lane_writes,
            "replay_insertions": replay_insertions,
            "terminal_plan_root": terminal_plan.plan_root,
            "oracle_plan_root": oracle_plan.plan_root,
        },
    )


def _runtime_history() -> RuntimeHistory:
    """Six live steps ending in a second committed replay insertion."""

    start = _state(START_HEIGHT, (("alice", 10),), ())

    static_accept = _submitted_step(start, start, GlobalEconomicEffectPlanV2.empty(), ())

    outbox_plan = GlobalEconomicEffectPlanV2(
        (),
        (),
        (),
        (),
        (),
        (
            ExternalOutboxEnqueueV2(
                effect_id=_root(501),
                destination_id="external:adapter",
                payload_hash=_root(502),
                adapter_profile_root=_root(503),
            ),
        ),
    )
    outbox_reject = _submitted_step(start, start, outbox_plan, ())

    first = _occurrence(START_HEIGHT + 1, "alice", 1, start.state_root, 1)
    middle = _state(
        START_HEIGHT + 1,
        (("alice", 7), ("bob", 3)),
        _replay_rows((first.replay_id, first.occurrence_id)),
    )
    first_commit = _submitted_step(
        start,
        middle,
        _transfer_plan(first.occurrence_id, "alice", "bob", 3),
        (first,),
    )

    # This reanchored reuse has a fresh occurrence after the first commit.
    # Publisher-owned exact retries are outside this core checker; the core
    # rejects a reused replay identifier here.
    reanchored_replay = _occurrence(
        START_HEIGHT + 2,
        "alice",
        1,
        middle.state_root,
        1,
    )
    reanchored_post = _state(
        START_HEIGHT + 2,
        (("alice", 4), ("bob", 6)),
        _replay_rows((reanchored_replay.replay_id, reanchored_replay.occurrence_id)),
    )
    reanchored_replay_reject = _submitted_step(
        middle,
        reanchored_post,
        _transfer_plan(reanchored_replay.occurrence_id, "alice", "bob", 3),
        (reanchored_replay,),
    )

    stale = _occurrence(START_HEIGHT + 2, "carol", 1, start.state_root, 2)
    stale_reject = _submitted_step(
        middle,
        middle,
        GlobalEconomicEffectPlanV2((), (), (), (), (stale.occurrence_id,), ()),
        (stale,),
    )

    second = _occurrence(START_HEIGHT + 2, "bob", 1, middle.state_root, 3)
    final = _state(
        START_HEIGHT + 2,
        (("alice", 9), ("bob", 1)),
        _replay_rows(
            (first.replay_id, first.occurrence_id),
            (second.replay_id, second.occurrence_id),
        ),
    )
    second_commit = _submitted_step(
        middle,
        final,
        _transfer_plan(second.occurrence_id, "bob", "alice", 2),
        (second,),
    )

    return RuntimeHistory(
        start=start,
        middle=middle,
        final=final,
        first=first,
        reanchored_replay=reanchored_replay,
        stale=stale,
        second=second,
        steps=(
            static_accept,
            outbox_reject,
            first_commit,
            reanchored_replay_reject,
            stale_reject,
            second_commit,
        ),
    )


def _observed_steps(history: RuntimeHistory) -> list[ObservedStep]:
    steps: list[ObservedStep] = []
    for runtime_step in history.steps:
        candidate = runtime_step.candidate
        pre = candidate.pre_state
        post = candidate.post_state
        effect_plan = candidate.effect_plan
        terminal_plan = candidate.terminal_plan
        oracle_plan = candidate.oracle_plan
        outcome = runtime_step.outcome
        if isinstance(outcome, GlobalEconomicRefinementAcceptedV2):
            witness = outcome.witness
            replay_insertions = _actual_replay_insertions(pre, post)
            submitted_pairs = tuple(
                (item.replay_id, item.occurrence_id) for item in candidate.consumed_occurrences
            )
            actual_pairs = tuple((item.replay_id, item.occurrence_id) for item in replay_insertions)
            assert actual_pairs == submitted_pairs
            assert effect_plan.occurrence_consumptions == tuple(
                item.occurrence_id for item in replay_insertions
            )
            assert witness.pre_state_root == pre.state_root
            assert witness.post_state_root == post.state_root
            assert witness.effect_plan_root == effect_plan.effect_plan_root
            assert witness.terminal_plan_root == terminal_plan.plan_root
            assert witness.oracle_plan_root == oracle_plan.plan_root
            assert witness.state_delta_root == _expected_state_delta_root(
                pre,
                post,
                effect_plan,
                terminal_plan,
                oracle_plan,
                replay_insertions,
            )
            steps.append(
                ObservedStep(
                    pre_state_root=witness.pre_state_root,
                    post_state_root=witness.post_state_root,
                    pre_height=pre.height,
                    post_height=post.height,
                    committed=True,
                    replay_ids=[item.replay_id for item in replay_insertions],
                    occurrence_ids=[item.occurrence_id for item in replay_insertions],
                )
            )
        else:
            assert isinstance(outcome, GlobalEconomicRefinementRejectedV2)
            assert outcome.pre_state_root == pre.state_root
            assert outcome.post_state_root == pre.state_root
            assert outcome.consumed_occurrences == ()
            steps.append(
                ObservedStep(
                    pre_state_root=outcome.pre_state_root,
                    post_state_root=outcome.post_state_root,
                    pre_height=pre.height,
                    post_height=pre.height,
                    committed=False,
                    replay_ids=[item.replay_id for item in outcome.consumed_occurrences],
                    occurrence_ids=[item.occurrence_id for item in outcome.consumed_occurrences],
                )
            )
    return steps


def _render_step(step: ObservedStep) -> str:
    replay = ", ".join(json.dumps(value) for value in step.replay_ids)
    occurrences = ", ".join(json.dumps(value) for value in step.occurrence_ids)
    return (
        "{ preStateRoot := "
        + json.dumps(step.pre_state_root)
        + ", postStateRoot := "
        + json.dumps(step.post_state_root)
        + f", preHeight := {step.pre_height}"
        + f", postHeight := {step.post_height}"
        + f", committed := {'true' if step.committed else 'false'}"
        + f", replayIds := [{replay}]"
        + f", occurrenceIds := [{occurrences}] }}"
    )


def _render_steps(steps: list[ObservedStep]) -> str:
    """Ascribe the element type: a bare record literal has no expected type in
    `.flatMap`/`.all` position and fails to elaborate."""

    body = ",\n    ".join(_render_step(step) for step in steps)
    return "([ " + body + " ] : List ObservedStep)"


def _render_trace(
    steps: list[ObservedStep],
    start_root: str,
    start_height: int,
    final_root: str,
    final_height: int,
) -> str:
    return (
        f"#eval observedTraceOk {json.dumps(start_root)} {start_height}\n"
        f"  {_render_steps(steps)}\n"
        f"  {json.dumps(final_root)} {final_height}\n"
    )


def _trace_refines_consumer_source() -> str:
    """Use every promised `TraceRefines` field at its exact public type."""

    return (
        f"import {NAMESPACE}\n\n"
        + """namespace Proofs.TraceRefinesConsumerV2
open Proofs.GlobalSettlementCoreV2
open Proofs.GlobalEconomicStateRefinementV2
open Proofs.GlobalEconomicRefinementTraceV2

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    ∀ transition ∈ run.committed, transition.IsVerified :=
  refines.committedVerified

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    Chained pre run.committed final :=
  refines.committedChain

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    FixedContext pre final :=
  refines.fixedContext

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    final.height = pre.height + committedHeightSteps run.committed :=
  refines.heightAccounting

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    ∀ (replayId : Identifier) (occurrenceId : RootId),
      pre.replayState replayId = some occurrenceId →
        final.replayState replayId = some occurrenceId :=
  refines.replayMonotone

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    run.consumedReplayIds.Nodup :=
  refines.replayIdsConsumedOnce

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    run.consumedOccurrenceIds.Nodup :=
  refines.occurrenceIdsConsumedOnce

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    ∀ plan ∈ run.stepEffectPlans, plan.externalOutboxEnqueue = [] :=
  refines.outboxClosed

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    ∀ transition ∈ run.committed, transition.occurrences = [] →
      transition.effects.IsEmpty ∧
      transition.terminalPlan.deltas = [] ∧
      transition.oraclePlan.deltas = [] ∧
      transition.pre = transition.post :=
  refines.zeroOccurrenceStatic

example {pre final : GlobalState} (run : Run pre final) (refines : TraceRefines run) :
    run.committed = [] →
      final = pre ∧
      (∀ plan ∈ run.stepEffectPlans, plan.IsEmpty) ∧
      run.stepTerminalDeltas = [] ∧
      run.stepOracleDeltas = [] ∧
      run.stepOccurrences = [] :=
  refines.uncommittedIsCompleteNoOp

end Proofs.TraceRefinesConsumerV2
"""
    )


# --------------------------------------------------------------------------
# Lean surface
# --------------------------------------------------------------------------


def test_trace_module_has_no_placeholders_and_only_standard_axioms(
    lean_library: Path, lean_source_root: Path, tmp_path: Path
) -> None:
    declarations = _declarations(_trace_source(lean_source_root).read_text())
    assert re.search(r"\b(sorry|admit|axiom)\b", declarations) is None
    probe = tmp_path / "TraceAxioms.lean"
    probe.write_text(
        f"import {NAMESPACE}\n"
        + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in TRACE_THEOREMS)
        + "\n",
        encoding="utf-8",
    )
    result = _check(probe, lean_library, source_root=lean_source_root)
    assert result.returncode == 0, result.stdout + result.stderr
    for name in TRACE_THEOREMS:
        assert f"'{NAMESPACE}.{name}'" in result.stdout, name
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= ALLOWED_AXIOMS


def test_theorem_surface_is_exact_and_removal_is_observable(
    lean_source_root: Path,
) -> None:
    declarations = _declarations(_trace_source(lean_source_root).read_text())
    names = tuple(re.findall(r"^theorem\s+([A-Za-z0-9_.]+)", declarations, re.MULTILINE))
    assert names == TRACE_THEOREMS
    weakened = declarations.replace("theorem every_run_refines", "lemma every_run_refines", 1)
    assert (
        tuple(re.findall(r"^theorem\s+([A-Za-z0-9_.]+)", weakened, re.MULTILINE)) != TRACE_THEOREMS
    )


def test_trace_bundle_carries_every_conjunct_and_proves_each_one(
    lean_source_root: Path,
) -> None:
    """A conjunct dropped from `TraceRefines` must not pass silently.

    Deleting a bundle field leaves every standalone theorem proved and the
    module compiling, so `TRACE_THEOREMS` alone cannot see it.
    """

    source = _trace_source(lean_source_root).read_text()
    fields = _structure_fields(source, "TraceRefines")
    assert fields == TRACE_REFINES_FIELDS, (
        f"TraceRefines conjuncts changed: {fields} != {TRACE_REFINES_FIELDS}"
    )
    assignments = _instance_assignments(source, "every_run_refines")
    assert assignments == TRACE_REFINES_FIELDS, (
        f"every_run_refines proves {assignments}, expected {TRACE_REFINES_FIELDS}"
    )

    dropped = source.replace(OUTBOX_CONJUNCT_FIELD, "", 1)
    assert dropped != source, "TraceRefines.outboxClosed is already absent"
    assert _structure_fields(dropped, "TraceRefines") != TRACE_REFINES_FIELDS


def test_trace_theorems_keep_every_single_step_dimension(
    lean_library: Path, lean_source_root: Path, tmp_path: Path
) -> None:
    """The trace bundle must expose the full one-step witness, not a summary."""

    probe = tmp_path / "TraceSignatures.lean"
    probe.write_text(
        f"""import {NAMESPACE}

namespace Proofs.GlobalEconomicRefinementTraceV2Signatures
open Proofs.GlobalSettlementCoreV2
open Proofs.GlobalEconomicStateRefinementV2
open {NAMESPACE}

-- The recovered per-step witness is the unweakened single-step relation.
example (transition : Transition) (verified : transition.IsVerified) :
    Verified transition.pre transition.effects transition.terminalPlan
      transition.oraclePlan transition.occurrences transition.post := verified

-- Every conjunct of the single-step accepted theorems is recoverable per step.
example {{pre final : GlobalState}} (run : Run pre final) (transition : Transition)
    (member : transition ∈ run.committed) :
    OwnedMatchesSupply transition.post ∧
      ClaimantLiabilitiesBacked transition.post ∧
      ExactEconomicTables transition.pre transition.post transition.effects ∧
      ExactSupplyEffects transition.pre transition.post transition.effects ∧
      ExactLaneWrites transition.pre transition.post transition.effects ∧
      ExactTerminalRefinement transition.pre transition.post transition.effects
        transition.terminalPlan ∧
      ExactOracleRefinement transition.pre transition.post transition.effects
        transition.oraclePlan ∧
      ExactReplayRefinement transition.pre transition.post transition.effects
        transition.occurrences ∧
      ProjectionMatches transition.effects ∧
      FeeAllocationCreditsMirrored transition.effects ∧
      transition.effects.externalOutboxEnqueue = [] := by
  have verified := run_committed_transitions_are_verified run transition member
  exact ⟨verified.ownedSupplyPost, verified.liabilitiesPost, verified.economicTables,
    verified.supplyEffects, verified.laneWrites, verified.terminal, verified.oracle,
    verified.replay, verified.effectPlan.2.2.2.1, verified.annotations.2.1,
    verified.outboxClosed⟩

-- The remaining single-step accepted conclusions, restated per committed step.
example {{pre final : GlobalState}} (run : Run pre final) (transition : Transition)
    (member : transition ∈ run.committed) :
    OpenTerminalLiabilitiesCovered transition.post ∧
      (∀ asset domain,
        0 ≤ amountForAssetDomain transition.post.liabilities asset domain ∧
        amountForAssetDomain transition.post.liabilities asset domain ≤
          amountForAssetDomain transition.post.custody asset domain) ∧
      (FeeAllocationCreditsMirrored transition.effects ∧
        FeeProjectionMatches transition.effects ∧
        FeeRowsCanonical transition.effects ∧
        FeeResidueExact transition.effects) ∧
      (OrderedOccurrenceIds transition.occurrences ∧
        transition.post.height =
          (if transition.occurrences.isEmpty then transition.pre.height
            else transition.pre.height + 1)) ∧
      (transition.occurrences = [] →
        transition.effects.IsEmpty ∧ transition.terminalPlan.deltas = [] ∧
          transition.oraclePlan.deltas = [] ∧ transition.pre = transition.post) ∧
      OracleRegistryWithinGlobalHeight transition.post := by
  have verified := run_committed_transitions_are_verified run transition member
  refine ⟨verified.liabilitiesPost.2, verified.liabilitiesPost.1,
    ⟨verified.annotations.2.1, verified.effectPlan.2.2.2.2.1,
      verified.annotations.2.2.2.1, verified.annotations.2.2.2.2⟩,
    ⟨verified.replay.1, verified.replay.2.2.2.2.1⟩, verified.zeroOccurrence, ?_⟩
  rcases verified.postQuantities with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, oracleAdmitted⟩
  exact oracleAdmitted.1

-- Composition results.
example {{pre final : GlobalState}} (run : Run pre final) :
    Chained pre run.committed final := run_committed_transitions_chain run
example {{pre final : GlobalState}} (run : Run pre final) :
    FixedContext pre final := run_preserves_fixed_context run
example {{pre final : GlobalState}} (run : Run pre final) :
    final.height = pre.height + committedHeightSteps run.committed :=
  run_height_counts_committed_advancing_steps run
example {{pre final : GlobalState}} (run : Run pre final)
    (replayId : Identifier) (occurrenceId : RootId)
    (recorded : pre.replayState replayId = some occurrenceId) :
    final.replayState replayId = some occurrenceId :=
  run_replay_registry_is_monotone run replayId occurrenceId recorded
example {{pre final : GlobalState}} (run : Run pre final) :
    run.consumedReplayIds.Nodup := run_consumes_each_replay_id_at_most_once run
example {{pre final : GlobalState}} (run : Run pre final) :
    run.consumedOccurrenceIds.Nodup := run_consumes_each_occurrence_id_at_most_once run

-- All five rejection dimensions survive at trace level.
example {{pre final : GlobalState}} (run : Run pre final) (uncommitted : run.committed = []) :
    final = pre ∧
      (∀ plan ∈ run.stepEffectPlans, plan.IsEmpty) ∧
      run.stepTerminalDeltas = [] ∧
      run.stepOracleDeltas = [] ∧
      run.stepOccurrences = [] :=
  run_without_committed_steps_is_complete_no_op run uncommitted

-- The runtime-facing oracle is proved sound for every model run.
example {{pre final : GlobalState}} (run : Run pre final) :
    observedTraceOk pre.stateRoot pre.height run.observe final.stateRoot
      final.height = true := run_observation_is_ok run

-- Conjunct-drop probe over the trace-level bundle.  Every field is projected
-- and the structure is rebuilt field by field, so a dropped field fails to
-- elaborate and an added field fails the reconstruction.
example {{pre final : GlobalState}} (run : Run pre final) (bundle : TraceRefines run) :
    TraceRefines run :=
  {{ committedVerified := bundle.committedVerified
    committedChain := bundle.committedChain
    fixedContext := bundle.fixedContext
    heightAccounting := bundle.heightAccounting
    replayMonotone := bundle.replayMonotone
    replayIdsConsumedOnce := bundle.replayIdsConsumedOnce
    occurrenceIdsConsumedOnce := bundle.occurrenceIdsConsumedOnce
    outboxClosed := bundle.outboxClosed
    zeroOccurrenceStatic := bundle.zeroOccurrenceStatic
    uncommittedIsCompleteNoOp := bundle.uncommittedIsCompleteNoOp }}

-- The bundle's outbox conjunct covers rejected steps, which `committedVerified`
-- cannot reach: `Run.committed` drops rejected steps by construction.
example {{pre final : GlobalState}} (run : Run pre final) :
    ∀ plan ∈ run.stepEffectPlans, plan.externalOutboxEnqueue = [] :=
  (every_run_refines run).outboxClosed
example {{pre final : GlobalState}} (run : Run pre final) (transition : Transition)
    (member : transition ∈ run.committed) (zero : transition.occurrences = []) :
    transition.effects.IsEmpty ∧ transition.terminalPlan.deltas = [] ∧
      transition.oraclePlan.deltas = [] ∧ transition.pre = transition.post :=
  (every_run_refines run).zeroOccurrenceStatic transition member zero

-- Non-vacuity: a history whose committed step really advances the height.
example : committedHeightSteps witnessRun.committed = 1 :=
  witness_run_advances_height_exactly_once
example : witnessRun.consumedReplayIds = ["replay-1"] :=
  witness_run_consumes_one_replay_id

end Proofs.GlobalEconomicRefinementTraceV2Signatures
""",
        encoding="utf-8",
    )
    result = _check(probe, lean_library, source_root=lean_source_root)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


def test_claim_boundary_and_atomicity_assumptions_stay_explicit(
    lean_source_root: Path,
) -> None:
    source = _trace_source(lean_source_root).read_text()
    for phrase in (
        "Atomicity assumptions, stated explicitly",
        "Sequential composition",
        "All-or-nothing steps",
        "No out-of-band mutation",
        "The outcome is given, not decided",
        "no Python or Rust runtime refinement",
        "no verifier, publisher,",
        "settlement, or value-moving authority",
        "no release status",
        "no production readiness",
        "no SQLite",
        "indeterminate client knowledge is represented as a rejection",
        "necessary condition, not a refinement proof",
    ):
        assert phrase in source, phrase


# --------------------------------------------------------------------------
# Runtime history
# --------------------------------------------------------------------------


def test_runtime_history_produces_the_expected_live_outcomes() -> None:
    history = _runtime_history()
    outcomes = [step.outcome for step in history.steps]

    accepted = [isinstance(outcome, GlobalEconomicRefinementAcceptedV2) for outcome in outcomes]
    assert accepted == [True, False, True, False, False, True]

    codes = [
        outcome.reject_code
        for outcome in outcomes
        if isinstance(outcome, GlobalEconomicRefinementRejectedV2)
    ]
    assert codes == [
        GlobalEconomicRefinementRejectCodeV2.EXTERNAL_OUTBOX_REQUIRES_PUBLISHER,
        GlobalEconomicRefinementRejectCodeV2.REPLAY_ALREADY_CONSUMED,
        GlobalEconomicRefinementRejectCodeV2.OCCURRENCE_CONTEXT_MISMATCH,
    ]

    # Every rejection is an exact no-op on all five reported dimensions.
    for outcome in outcomes:
        if isinstance(outcome, GlobalEconomicRefinementRejectedV2):
            assert outcome.post_state_root == outcome.pre_state_root
            assert outcome.effect_plan == GlobalEconomicEffectPlanV2.empty()
            assert outcome.terminal_plan == GlobalTerminalObligationPlanV2.empty()
            assert outcome.oracle_plan == GlobalOracleOccurrencePlanV2.empty()
            assert outcome.consumed_occurrences == ()
            assert outcome.outbox == ()

    # The reanchored reuse has a new occurrence but retains the consumed replay ID.
    assert history.reanchored_replay.replay_id == history.first.replay_id
    assert history.reanchored_replay.occurrence_id != history.first.occurrence_id

    # Independent integer expectations for the committed endpoints.
    assert (history.start.height, history.middle.height, history.final.height) == (7, 8, 9)
    assert [row.amount_atoms for row in history.start.balances] == [10]
    assert sorted(row.amount_atoms for row in history.middle.balances) == [3, 7]
    assert sorted(row.amount_atoms for row in history.final.balances) == [1, 9]
    for state in (history.start, history.middle, history.final):
        assert sum(row.amount_atoms for row in state.balances) == TOTAL_SUPPLY
    assert [row.replay_id for row in history.final.replay_state] == sorted(
        {history.first.replay_id, history.second.replay_id}
    )
    assert len({history.start.state_root, history.middle.state_root, history.final.state_root}) == 3


def test_runtime_observation_rejects_a_corrupted_returned_root_for_static_endpoints() -> None:
    """The returned witness, rather than equal submitted fixtures, owns observation."""

    history = _runtime_history()
    static_step = history.steps[0]
    assert static_step.candidate.pre_state == static_step.candidate.post_state
    assert isinstance(static_step.outcome, GlobalEconomicRefinementAcceptedV2)

    # Test-only corruption bypasses the witness's immutable API.  The submitted
    # endpoints are equal, so fixture-derived observation would miss this root.
    object.__setattr__(
        static_step.outcome.witness,
        "_fields",
        replace(static_step.outcome.witness._fields, post_state_root=_root(999)),
    )
    assert (
        static_step.outcome.witness.post_state_root != static_step.candidate.post_state.state_root
    )
    with pytest.raises(AssertionError):
        _observed_steps(history)


def test_runtime_history_observation_passes_the_proved_lean_trace_oracle(
    lean_library: Path, lean_source_root: Path, tmp_path: Path
) -> None:
    history = _runtime_history()
    steps = _observed_steps(history)

    # Independent expectations, derived without consulting Lean.
    assert [step.committed for step in steps] == [True, False, True, False, False, True]
    advancing = [step for step in steps if step.replay_ids]
    assert len(advancing) == 2
    assert history.final.height == history.start.height + len(advancing)
    running_root = history.start.state_root
    for step in steps:
        assert step.pre_state_root == running_root
        running_root = step.post_state_root
    assert running_root == history.final.state_root
    replay_ids = [value for step in steps for value in step.replay_ids]
    assert len(replay_ids) == len(set(replay_ids)) == 2

    rendered_ids = ", ".join(json.dumps(value) for value in replay_ids)
    lines = _eval_lines(
        lean_library,
        tmp_path,
        "TraceRuntimeHistory",
        _render_trace(
            steps,
            history.start.state_root,
            history.start.height,
            history.final.state_root,
            history.final.height,
        )
        + f"#eval ([{rendered_ids}] : List String).Nodup\n"
        + f"#eval observedAdvancingSteps {_render_steps(steps)}\n",
        source_root=lean_source_root,
    )
    assert lines == ["true", "true", "2"]


def _advance_rejected_height(steps: list[ObservedStep]) -> None:
    steps[1].post_height += 1


def _move_rejected_state_root(steps: list[ObservedStep]) -> None:
    steps[3].post_state_root = _root(7)


def _smuggle_occurrence_into_rejection(steps: list[ObservedStep]) -> None:
    steps[4].replay_ids = ["smuggled-replay"]
    steps[4].occurrence_ids = [_root(11)]


def _reuse_a_replay_id_on_an_otherwise_valid_commit(steps: list[ObservedStep]) -> None:
    """Keep all dimensions valid except replay-ID uniqueness."""

    steps[5].replay_ids = list(steps[2].replay_ids)


def _commit_the_same_occurrence_twice(steps: list[ObservedStep]) -> None:
    steps[5].occurrence_ids = list(steps[2].occurrence_ids)


def _stall_a_committed_step(steps: list[ObservedStep]) -> None:
    steps[5].post_height = steps[5].pre_height


def _break_the_state_chain(steps: list[ObservedStep]) -> None:
    steps[2].post_state_root = _root(13)


@pytest.mark.parametrize(
    ("name", "mutate"),
    (
        ("rejection_advances_height", _advance_rejected_height),
        ("rejection_changes_state_root", _move_rejected_state_root),
        ("rejection_reports_a_consumed_occurrence", _smuggle_occurrence_into_rejection),
        (
            "duplicate_replay_id_with_valid_chain_and_heights",
            _reuse_a_replay_id_on_an_otherwise_valid_commit,
        ),
        ("same_occurrence_id_committed_twice", _commit_the_same_occurrence_twice),
        ("committed_step_does_not_advance_height", _stall_a_committed_step),
        ("chain_is_broken_between_steps", _break_the_state_chain),
    ),
)
def test_lean_trace_oracle_kills_semantic_mutations_of_the_runtime_history(
    lean_library: Path,
    lean_source_root: Path,
    tmp_path: Path,
    name: str,
    mutate: Callable[[list[ObservedStep]], None],
) -> None:
    history = _runtime_history()
    steps = _observed_steps(history)
    mutate(steps)

    if name == "duplicate_replay_id_with_valid_chain_and_heights":
        rendered_steps = _render_steps(steps)
        dimensions = _eval_lines(
            lean_library,
            tmp_path,
            "TraceMutationDuplicateReplayDimensions",
            f"#eval ({rendered_steps}).all observedStepOk\n"
            + f"#eval observedChained {json.dumps(history.start.state_root)} "
            + f"{history.start.height} ({rendered_steps}) "
            + f"{json.dumps(history.final.state_root)} {history.final.height}\n"
            + f"#eval decide ((({rendered_steps}).flatMap "
            + "(fun step => step.occurrenceIds)).Nodup)\n"
            + f"#eval decide ((({rendered_steps}).flatMap "
            + "(fun step => step.replayIds)).Nodup)\n"
            + f"#eval ({history.final.height} == {history.start.height} + "
            + f"observedAdvancingSteps ({rendered_steps}))\n",
            source_root=lean_source_root,
        )
        assert dimensions == ["true", "true", "true", "false", "true"]

    lines = _eval_lines(
        lean_library,
        tmp_path,
        f"TraceMutant_{name}",
        _render_trace(
            steps,
            history.start.state_root,
            history.start.height,
            history.final.state_root,
            history.final.height,
        ),
        source_root=lean_source_root,
    )
    assert lines == ["false"], name


def test_dropping_the_trace_bundle_outbox_conjunct_breaks_the_type_consumer(
    lean_library: Path, lean_source_root: Path, tmp_path: Path
) -> None:
    """A weak bundle compiles, while the exact ten-field consumer rejects it.

    Removing `TraceRefines.outboxClosed` and its instance line leaves the module
    compiling.  The consumer checks every promised field at its precise type,
    including the outbox closure that cannot be recovered from committed steps.
    """

    consumer = tmp_path / "TraceRefinesConsumer.lean"
    consumer.write_text(_trace_refines_consumer_source(), encoding="utf-8")
    result = _check(consumer, lean_library, source_root=lean_source_root)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""

    mutant_root = tmp_path / "dropped-conjunct"
    (mutant_root / "Proofs").mkdir(parents=True)
    (mutant_root / "lean-toolchain").write_text(
        (lean_source_root / "lean-toolchain").read_text(), encoding="utf-8"
    )
    for name in DEPENDENCIES:
        (mutant_root / "Proofs" / f"{name}.lean").write_text(
            (lean_source_root / "Proofs" / f"{name}.lean").read_text(), encoding="utf-8"
        )
    source = _trace_source(lean_source_root).read_text()
    dropped = source.replace(OUTBOX_CONJUNCT_FIELD, "", 1).replace(OUTBOX_CONJUNCT_PROOF, "", 1)
    assert dropped != source, (
        "the pristine module must still carry TraceRefines.outboxClosed; "
        "this test mutates a copy and cannot run once the conjunct is gone"
    )
    assert "outboxClosed" not in _structure_fields(dropped, "TraceRefines")
    (mutant_root / "Proofs" / f"{MODULE}.lean").write_text(dropped, encoding="utf-8")
    _assert_pinned_toolchain(mutant_root)

    library = mutant_root / "build"
    (library / "Proofs").mkdir(parents=True)
    for name in (*DEPENDENCIES, MODULE):
        built = _check(
            mutant_root / "Proofs" / f"{name}.lean",
            library,
            library / "Proofs" / f"{name}.olean",
            source_root=mutant_root,
        )
        # The mutant still compiles cleanly; a theorem-name list cannot reveal
        # this weaker bundle.
        assert built.returncode == 0, built.stdout + built.stderr

    weak_bundle = mutant_root / "TraceRefinesWeakBundle.lean"
    weak_bundle.write_text(
        f"import {NAMESPACE}\n"
        "open Proofs.GlobalSettlementCoreV2\n"
        "open Proofs.GlobalEconomicStateRefinementV2\n"
        f"open {NAMESPACE}\n\n"
        "example {pre final : GlobalState} (run : Run pre final) : TraceRefines run :=\n"
        "  every_run_refines run\n",
        encoding="utf-8",
    )
    result = _check(weak_bundle, library, source_root=mutant_root)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""

    mutant_consumer = mutant_root / "TraceRefinesConsumer.lean"
    mutant_consumer.write_text(_trace_refines_consumer_source(), encoding="utf-8")
    result = _check(mutant_consumer, library, source_root=mutant_root)
    assert result.returncode != 0
    assert "outboxClosed" in result.stdout + result.stderr


def test_dropping_the_rejection_no_op_clause_stops_killing_a_mutating_rejection(
    lean_source_root: Path, tmp_path: Path
) -> None:
    """A fixed semantic mutant of the model that the unchanged oracle kills.

    The mutant erases the requirement that a rejected step change nothing.  The
    chain and height clauses still hold for the probe history, so only the
    deleted clause separates the two oracles.
    """

    mutant_root = tmp_path / "mutant-lean"
    (mutant_root / "Proofs").mkdir(parents=True)
    # elan resolves the toolchain from the working directory upward, so the
    # mutant lane must carry the same pin or it silently builds on the default.
    (mutant_root / "lean-toolchain").write_text(
        (lean_source_root / "lean-toolchain").read_text(), encoding="utf-8"
    )
    for name in DEPENDENCIES:
        source = lean_source_root / "Proofs" / f"{name}.lean"
        (mutant_root / "Proofs" / f"{name}.lean").write_text(source.read_text(), encoding="utf-8")
    original = _trace_source(lean_source_root).read_text()
    mutated = original.replace(
        """      (step.postStateRoot == step.preStateRoot) && (step.postHeight == step.preHeight) &&
        step.replayIds.isEmpty && step.occurrenceIds.isEmpty)""",
        "      true)",
        1,
    )
    assert mutated != original
    (mutant_root / "Proofs" / f"{MODULE}.lean").write_text(mutated, encoding="utf-8")
    _assert_pinned_toolchain(mutant_root)

    library = mutant_root / "build"
    (library / "Proofs").mkdir(parents=True)
    for name in (*DEPENDENCIES, MODULE):
        result = _check(
            mutant_root / "Proofs" / f"{name}.lean",
            library,
            library / "Proofs" / f"{name}.olean",
            source_root=mutant_root,
            warnings_as_errors=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr

    assert _eval_lines(
        library,
        tmp_path,
        "MutantMutatingRejection",
        MUTATING_REJECTION_TRACE,
        source_root=mutant_root,
        warnings_as_errors=False,
    ) == ["true"]


def test_unchanged_oracle_kills_a_mutating_rejection_and_a_stalled_commit(
    lean_library: Path, lean_source_root: Path, tmp_path: Path
) -> None:
    assert _eval_lines(
        lean_library,
        tmp_path,
        "UnmutatedRejection",
        MUTATING_REJECTION_TRACE,
        source_root=lean_source_root,
    ) == ["false"]
    stalled = (
        '#eval observedTraceOk "a" 7\n'
        '  [ { preStateRoot := "a", postStateRoot := "b", preHeight := 7, postHeight := 7,\n'
        '      committed := true, replayIds := ["r1"], occurrenceIds := ["o1"] } ]\n'
        '  "b" 7\n'
    )
    assert _eval_lines(
        lean_library,
        tmp_path,
        "UnmutatedStalled",
        stalled,
        source_root=lean_source_root,
    ) == ["false"]
