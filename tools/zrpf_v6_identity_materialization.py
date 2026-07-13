#!/usr/bin/env python3
"""Reconstruct, check, and stage one exact ZRPF Spot V6 identity transition.

The executor builds inside a private source snapshot.  This tool independently
reconstructs the eight governed post-build files from the source commit and the
checker-accepted observation bundle.  It never copies bytes from the mutable
run snapshot into the checkout.

Both commands are authority-neutral.  ``check`` proves that an exact indexed
patch would apply to a clean checkout at C0.  ``apply`` stages that patch with
``git apply --index`` and writes a canonical external manifest.  Neither mode
promotes proof, receipt, release, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_identity_artifacts as artifacts
from tools import zrpf_v6_identity_materialization_git as git_boundary
from tools import zrpf_v6_identity_materialization_output as output_boundary
from tools import zrpf_v6_identity_materialization_rollback as rollback_boundary
from tools.zrpf_v6_identity_source_snapshot import (
    SOURCE_SNAPSHOT_DIRECTORY,
    V2_CANDIDATE_PATHS,
    GitSnapshotter,
    MaterializedSnapshot,
    validate_initial_snapshot,
)
from tools.zrpf_v6_identity_source_state import (
    ExpectedSourceState,
    render_expected_repin,
)

MANIFEST_SCHEMA = "zenodex/zrpf_v6_identity_materialization_manifest/v1"
MAX_TRANSITION_FILE_BYTES = git_boundary.MAX_TRANSITION_FILE_BYTES
MaterializationError = git_boundary.MaterializationError
MaterializationPartialStateError = git_boundary.MaterializationPartialStateError

MATERIALIZED_PATHS = tuple(
    sorted(
        {
            *(repin.path for stage in planner.STAGES for repin in stage.repins),
            *V2_CANDIDATE_PATHS,
        }
    )
)


@dataclass(frozen=True)
class MaterializationRequest:
    """Exact external evidence and checkout inputs for one transition."""

    repo_root: Path
    plan_path: Path
    observations_path: Path
    report_path: Path
    run_snapshot_root: Path


@dataclass(frozen=True)
class _Transition:
    source_commit: str
    plan_sha256: str
    observations_sha256: str
    report_sha256: str
    final_source_root: str
    before: dict[str, bytes]
    after: dict[str, bytes]
    git_modes: dict[str, str]
    patch: bytes


@dataclass(frozen=True)
class _ValidatedEvidence:
    repo_root: Path
    plan: dict[str, Any]
    observations: dict[str, Any]
    report: dict[str, Any]
    run_snapshot_root: Path


def check_materialization(request: MaterializationRequest) -> dict[str, Any]:
    """Return a candidate manifest after checking an exact non-mutating patch."""

    transition = _prepare_transition(request)
    git_boundary.check_patch(
        request.repo_root,
        transition.patch,
        transition.source_commit,
    )
    return _manifest(transition, mode="checked_not_applied", index_tree=None)


def apply_materialization(
    request: MaterializationRequest,
    *,
    manifest_output: Path,
) -> dict[str, Any]:
    """Stage the exact candidate patch and write its external manifest."""

    output = output_boundary.open_absent_external_output(
        manifest_output, request.repo_root
    )
    transition: _Transition | None = None
    patch_may_have_applied = False
    try:
        transition = _prepare_transition(request)
        git_boundary.check_patch(
            request.repo_root,
            transition.patch,
            transition.source_commit,
        )
        patch_may_have_applied = True
        index_tree = git_boundary.apply_patch(
            request.repo_root,
            transition.patch,
            transition.after,
            MATERIALIZED_PATHS,
            transition.source_commit,
        )
        manifest = _manifest(
            transition,
            mode="applied_indexed_candidate",
            index_tree=index_tree,
        )
        git_boundary.require_materialized_state(
            request.repo_root,
            transition.source_commit,
            index_tree,
            transition.after,
            MATERIALIZED_PATHS,
        )
        output_boundary.write_external_output(
            output,
            planner.canonical_bytes(manifest),
        )
        return manifest
    except BaseException:
        if patch_may_have_applied and transition is not None:
            _rollback_transition(request.repo_root, transition)
        raise
    finally:
        output_boundary.close_external_output(output)


def _rollback_transition(repo_root: Path, transition: _Transition) -> None:
    try:
        rollback_boundary.rollback_materialization(
            repo_root,
            transition.source_commit,
            transition.patch,
            transition.before,
            transition.after,
            MATERIALIZED_PATHS,
        )
    except MaterializationPartialStateError:
        raise
    except MaterializationError as rollback_error:
        raise MaterializationPartialStateError(
            "materialization rejected and governed rollback could not be verified"
        ) from rollback_error


def _prepare_transition(request: MaterializationRequest) -> _Transition:
    root = git_boundary.require_clean_checkout(request.repo_root)
    plan = planner.load_canonical_json(request.plan_path, "identity rebuild plan")
    observations = planner.load_canonical_json(
        request.observations_path, "identity rebuild observations"
    )
    report = planner.load_canonical_json(request.report_path, "identity rebuild report")
    source_commit = plan.get("source_commit")
    if source_commit != git_boundary.git_stdout(
        root, ["rev-parse", "HEAD"], 128
    ).decode().strip():
        raise MaterializationError("checkout HEAD differs from the plan source commit")
    recomputed = planner.check_observations(plan, observations, repo_root=root)
    if report != recomputed:
        raise MaterializationError("candidate report differs from independent recomposition")
    expected_run_snapshot = Path(plan["host_run_root"]) / SOURCE_SNAPSHOT_DIRECTORY
    if git_boundary.canonical_existing_directory(
        request.run_snapshot_root
    ) != git_boundary.canonical_existing_directory(expected_run_snapshot):
        raise MaterializationError("run snapshot path differs from the governed plan")
    return _reconstruct_transition(
        _ValidatedEvidence(
            repo_root=root,
            plan=plan,
            observations=observations,
            report=report,
            run_snapshot_root=request.run_snapshot_root,
        )
    )


def _reconstruct_transition(evidence: _ValidatedEvidence) -> _Transition:
    with tempfile.TemporaryDirectory(prefix="zrpf-v6-materializer-") as temporary:
        baseline = GitSnapshotter().materialize(
            evidence.repo_root,
            evidence.plan["source_commit"],
            Path(temporary) / SOURCE_SNAPSHOT_DIRECTORY,
        )
        validate_initial_snapshot(baseline, evidence.plan)
        state = ExpectedSourceState.capture(baseline)
        before = _selected_bytes(state)
        _apply_expected_transitions(state, evidence.observations, evidence.report)
        final_root = state.require_current("materializer final expected state")
        after = _selected_bytes(state)
        modes = {entry.relative_path: entry.git_mode for entry in baseline.entries}
        if any(modes[path] != "100644" for path in MATERIALIZED_PATHS):
            raise MaterializationError("governed transition file mode is not 100644")
        _require_run_snapshot_matches(
            evidence.run_snapshot_root,
            baseline,
            state,
            final_root,
        )
        patch = git_boundary.build_patch(before, after, MATERIALIZED_PATHS)
    if final_root != evidence.report["final_source_snapshot_root_sha256"]:
        raise MaterializationError("reconstructed final source root differs from report")
    return _Transition(
        source_commit=evidence.plan["source_commit"],
        plan_sha256=planner.canonical_sha256(evidence.plan),
        observations_sha256=planner.canonical_sha256(evidence.observations),
        report_sha256=planner.canonical_sha256(evidence.report),
        final_source_root=final_root,
        before=before,
        after=after,
        git_modes={path: modes[path] for path in MATERIALIZED_PATHS},
        patch=patch,
    )


def _apply_expected_transitions(
    state: ExpectedSourceState,
    observations: dict[str, Any],
    report: dict[str, Any],
) -> None:
    rows = observations["stages"]
    for spec, row in zip(planner.STAGES, rows, strict=True):
        for expected, candidate in zip(spec.repins, row["repins"], strict=True):
            raw = render_expected_repin(
                state.expected_bytes(expected.path),
                expected.symbol,
                expected.value_kind,
                candidate["value"],
            )
            state.apply_exact_transition(
                expected.path,
                raw,
                lambda expected=expected, candidate=candidate: artifacts.repin_rust_constant(
                    state.snapshot.root / expected.path,
                    expected.symbol,
                    expected.value_kind,
                    candidate["value"],
                ),
                f"materialize {spec.stage_id} {expected.symbol}",
            )
    candidates = report["governance_candidates"]
    _apply_candidate_document(state, candidates["current_source_anchor_v2"])
    _apply_candidate_document(state, candidates["v2_adapter_source_policy"])


def _apply_candidate_document(
    state: ExpectedSourceState, candidate: dict[str, Any]
) -> None:
    path = candidate["path"]
    document = candidate["document"]
    raw = planner.canonical_bytes(document)
    if candidate["canonical_sha256"] != hashlib.sha256(raw).hexdigest():
        raise MaterializationError("governance candidate digest mismatch")
    state.apply_exact_transition(
        path,
        raw,
        lambda: artifacts.write_candidate_document(state.snapshot.root, path, document),
        f"materialize candidate {path}",
    )


def _require_run_snapshot_matches(
    run_root: Path,
    baseline: MaterializedSnapshot,
    expected: ExpectedSourceState,
    final_root: str,
) -> None:
    observed_snapshot = MaterializedSnapshot(run_root, baseline.entries)
    observed = ExpectedSourceState.capture(observed_snapshot)
    if observed.require_current("materializer run snapshot comparison") != final_root:
        raise MaterializationError("run snapshot root differs from reconstructed result")
    for entry in baseline.entries:
        if observed.expected_bytes(entry.relative_path) != expected.expected_bytes(
            entry.relative_path
        ):
            raise MaterializationError("run snapshot bytes differ from reconstruction")


def _selected_bytes(state: ExpectedSourceState) -> dict[str, bytes]:
    selected: dict[str, bytes] = {}
    for path in MATERIALIZED_PATHS:
        raw = state.expected_bytes(path)
        if len(raw) > MAX_TRANSITION_FILE_BYTES:
            raise MaterializationError("governed transition file exceeds its byte bound")
        selected[path] = raw
    return selected


def _manifest(
    transition: _Transition, *, mode: str, index_tree: str | None
) -> dict[str, Any]:
    return {
        "schema": MANIFEST_SCHEMA,
        "status": mode,
        "source_commit": transition.source_commit,
        "plan_sha256": transition.plan_sha256,
        "observations_sha256": transition.observations_sha256,
        "candidate_report_sha256": transition.report_sha256,
        "final_source_snapshot_root_sha256": transition.final_source_root,
        "generated_patch_sha256": hashlib.sha256(transition.patch).hexdigest(),
        "generated_patch_bytes": len(transition.patch),
        "materialized_paths": [
            {
                "path": path,
                "git_mode": transition.git_modes[path],
                "before_sha256": hashlib.sha256(transition.before[path]).hexdigest(),
                "after_sha256": hashlib.sha256(transition.after[path]).hexdigest(),
                "after_bytes": len(transition.after[path]),
            }
            for path in MATERIALIZED_PATHS
        ],
        "checkout_index_tree": index_tree,
        "validated_facts": {
            "checkout_was_clean_at_exact_input_commit": True,
            "plan_observations_and_report_recomposed": True,
            "run_snapshot_matches_independent_reconstruction": True,
            "generated_patch_has_exact_governed_path_set": True,
            "generated_patch_passes_index_check": True,
            "index_and_worktree_match_reconstruction": index_tree is not None,
        },
        "authority": {
            "complete_build_input_closure_verified": False,
            "cross_host_reproducible_build": False,
            "evidence_promoted": False,
            "proof_authority": False,
            "receipt_authority": False,
            "release_authority": False,
            "settlement_authority": False,
            "source_to_program_binary_provenance_verified": False,
            "production_authority": False,
        },
        "non_claims": [
            "materialization_does_not_verify_or_generate_proofs",
            "materialization_does_not_promote_release_authority",
            "candidate_documents_continue_to_bind_the_input_commit",
            "same_uid_run_snapshot_resistance_is_not_claimed",
            "complete_build_input_closure_is_not_claimed",
        ],
    }
