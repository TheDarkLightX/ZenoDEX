#!/usr/bin/env python3
"""Materialize one checked V6 settlement image ID into the V7 child policy.

This module accepts only a clean checkout at an explicitly supplied C1 commit.
C1 must be the direct child of the rebuild plan's C0 commit and must contain
exactly the eight source changes independently reconstructed from the canonical
plan, observations, and candidate report.  The V7 policy must still contain its
single all-zero fail-closed placeholder.

``check`` constructs and validates the exact one-file indexed patch without
mutating the checkout.  ``apply`` stages only that patch and writes an external
canonical manifest.  Neither operation grants proof, receipt, release,
settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_identity_materialization as v6_materializer
from tools import zrpf_v6_identity_materialization_git as git_boundary
from tools import zrpf_v6_identity_materialization_output as output_boundary
from tools import zrpf_v6_identity_materialization_rollback as rollback_boundary
from tools.zrpf_v6_identity_executor_types import ExecutionError
from tools.zrpf_v6_identity_source_snapshot import read_bounded_regular
from tools.zrpf_v6_identity_source_state import render_expected_repin

MANIFEST_SCHEMA = "zenodex/zrpf_v6_to_v7_child_policy_materialization_manifest/v1"
V7_CHILD_POLICY_PATH = "zk/spot_settlement_v7_risc0/child_policy/src/lib.rs"
V7_CHILD_POLICY_SYMBOL = "FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1"
MATERIALIZED_PATHS = (V7_CHILD_POLICY_PATH,)
MAX_TRANSITION_FILE_BYTES = git_boundary.MAX_TRANSITION_FILE_BYTES
AUTHORITY_FIELDS = (
    "complete_build_input_closure_verified",
    "cross_host_reproducible_build",
    "evidence_promoted",
    "proof_authority",
    "receipt_authority",
    "release_authority",
    "settlement_authority",
    "source_to_program_binary_provenance_verified",
    "production_authority",
)
NON_CLAIMS = (
    "child_policy_materialization_does_not_verify_or_generate_proofs",
    "candidate_report_and_c1_remain_authority_neutral",
    "no_complete_build_input_closure",
    "no_cross_host_reproducibility",
    "no_receipt_or_release_authority",
    "same_uid_checkout_race_resistance_is_not_claimed",
    "no_settlement_or_production_authority",
)

MaterializationError = git_boundary.MaterializationError
MaterializationPartialStateError = git_boundary.MaterializationPartialStateError


@dataclass(frozen=True)
class MaterializationRequest:
    """Exact C1 checkout and external candidate-evidence inputs."""

    repo_root: Path
    c1_commit: str
    plan_path: Path
    observations_path: Path
    report_path: Path


@dataclass(frozen=True)
class _Transition:
    c0_commit: str
    c1_commit: str
    plan_sha256: str
    observations_sha256: str
    report_sha256: str
    final_source_root: str
    settlement_program: dict[str, Any]
    before: dict[str, bytes]
    after: dict[str, bytes]
    git_modes: dict[str, str]
    patch: bytes


@dataclass(frozen=True)
class _ValidatedCandidate:
    root: Path
    c0_commit: str
    c1_commit: str
    plan_sha256: str
    observations_sha256: str
    report_sha256: str
    final_source_root: str
    settlement_program: dict[str, Any]


@dataclass(frozen=True)
class _C1Reconstruction:
    before: dict[str, bytes]
    after: dict[str, bytes]


def check_materialization(request: MaterializationRequest) -> dict[str, Any]:
    """Return a manifest after validating the exact non-mutating C1 patch."""

    transition = _prepare_transition(request)
    git_boundary.check_patch(
        request.repo_root,
        transition.patch,
        transition.c1_commit,
    )
    return _manifest(transition, mode="checked_not_applied", index_tree=None)


def apply_materialization(
    request: MaterializationRequest,
    *,
    manifest_output: Path,
) -> dict[str, Any]:
    """Stage the exact V7 child-policy candidate and emit its manifest."""

    output = output_boundary.open_absent_external_output(
        manifest_output,
        request.repo_root,
    )
    transition: _Transition | None = None
    patch_may_have_applied = False
    try:
        transition = _prepare_transition(request)
        git_boundary.check_patch(
            request.repo_root,
            transition.patch,
            transition.c1_commit,
        )
        patch_may_have_applied = True
        index_tree = git_boundary.apply_patch(
            request.repo_root,
            transition.patch,
            transition.after,
            MATERIALIZED_PATHS,
            transition.c1_commit,
        )
        manifest = _manifest(
            transition,
            mode="applied_indexed_candidate",
            index_tree=index_tree,
        )
        git_boundary.require_materialized_state(
            request.repo_root,
            transition.c1_commit,
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
        _close_output_best_effort(output)


def _prepare_transition(request: MaterializationRequest) -> _Transition:
    candidate = _validate_candidate(request)
    before_raw = _read_commit_blob(
        candidate.root,
        candidate.c1_commit,
        V7_CHILD_POLICY_PATH,
    )
    checkout_raw = read_bounded_regular(
        candidate.root.joinpath(*PurePosixPath(V7_CHILD_POLICY_PATH).parts),
        "V7 child-policy checkout source",
        MAX_TRANSITION_FILE_BYTES,
    )
    if checkout_raw != before_raw:
        raise MaterializationError("V7 child-policy checkout differs from C1")
    _require_zero_v7_placeholder(before_raw)
    try:
        after_raw = render_expected_repin(
            before_raw,
            V7_CHILD_POLICY_SYMBOL,
            "image_id_words_le",
            candidate.settlement_program["image_id_words"],
        )
    except ExecutionError as exc:
        raise MaterializationError("V7 child-policy repin could not be rendered") from exc
    if after_raw == before_raw:
        raise MaterializationError("V7 child-policy repin produced no change")

    before = {V7_CHILD_POLICY_PATH: before_raw}
    after = {V7_CHILD_POLICY_PATH: after_raw}
    return _Transition(
        c0_commit=candidate.c0_commit,
        c1_commit=candidate.c1_commit,
        plan_sha256=candidate.plan_sha256,
        observations_sha256=candidate.observations_sha256,
        report_sha256=candidate.report_sha256,
        final_source_root=candidate.final_source_root,
        settlement_program=candidate.settlement_program,
        before=before,
        after=after,
        git_modes={
            V7_CHILD_POLICY_PATH: _require_blob_mode(
                candidate.root,
                candidate.c1_commit,
                V7_CHILD_POLICY_PATH,
            )
        },
        patch=git_boundary.build_patch(before, after, MATERIALIZED_PATHS),
    )


def _validate_candidate(request: MaterializationRequest) -> _ValidatedCandidate:
    root = git_boundary.require_clean_checkout(request.repo_root)
    if request.repo_root != root:
        raise MaterializationError("repository root must be an exact canonical path")
    c1_commit = _require_commit_id(request.c1_commit, "supplied C1")
    head = git_boundary.git_stdout(root, ["rev-parse", "HEAD"], 128).decode().strip()
    if head != c1_commit:
        raise MaterializationError("checkout HEAD differs from supplied C1")

    plan = planner.load_canonical_json(request.plan_path, "identity rebuild plan")
    observations = planner.load_canonical_json(
        request.observations_path,
        "identity rebuild observations",
    )
    report = planner.load_canonical_json(
        request.report_path,
        "identity rebuild report",
    )
    recomputed = planner.check_observations(plan, observations, repo_root=root)
    if report != recomputed:
        raise MaterializationError("candidate report differs from independent recomposition")

    c0_commit = _require_commit_id(plan.get("source_commit"), "plan C0")
    _require_direct_child(root, c0_commit, c1_commit)
    reconstruction = _reconstruct_c1_transition(
        root,
        c0_commit,
        observations,
        report,
    )
    _require_exact_c1_transition(
        root,
        c0_commit,
        c1_commit,
        reconstruction,
    )
    settlement = _select_settlement_program(report.get("programs"))
    return _ValidatedCandidate(
        root=root,
        c0_commit=c0_commit,
        c1_commit=c1_commit,
        plan_sha256=planner.canonical_sha256(plan),
        observations_sha256=planner.canonical_sha256(observations),
        report_sha256=planner.canonical_sha256(report),
        final_source_root=report["final_source_snapshot_root_sha256"],
        settlement_program=settlement,
    )


def _require_direct_child(root: Path, c0_commit: str, c1_commit: str) -> None:
    _require_no_git_grafts(root)
    raw = git_boundary.git_stdout(
        root,
        ["cat-file", "commit", c1_commit],
        64 * 1024,
    )
    headers, separator, _message = raw.partition(b"\n\n")
    if not separator:
        raise MaterializationError("C1 raw commit object is malformed")
    parents = [line[7:] for line in headers.splitlines() if line.startswith(b"parent ")]
    if parents != [c0_commit.encode("ascii")]:
        raise MaterializationError("supplied C1 must be the direct child of C0")
    _require_no_git_grafts(root)


def _require_no_git_grafts(root: Path) -> None:
    raw = git_boundary.git_stdout(
        root,
        ["rev-parse", "--path-format=absolute", "--git-path", "info/grafts"],
        4096,
    )
    try:
        path = Path(raw.decode("utf-8", errors="strict").strip())
    except UnicodeDecodeError as exc:
        raise MaterializationError("Git graft path is not UTF-8") from exc
    if not path.is_absolute():
        raise MaterializationError("Git graft path is not absolute")
    try:
        path.lstat()
    except FileNotFoundError:
        return
    except OSError as exc:
        raise MaterializationError("Git graft path could not be inspected") from exc
    else:
        raise MaterializationError("Git grafts are forbidden for V7 materialization")


def _reconstruct_c1_transition(
    root: Path,
    c0_commit: str,
    observations: dict[str, Any],
    report: dict[str, Any],
) -> _C1Reconstruction:
    before = {
        path: _read_commit_blob(root, c0_commit, path)
        for path in v6_materializer.MATERIALIZED_PATHS
    }
    after = dict(before)
    rows = observations["stages"]
    try:
        for spec, row in zip(planner.STAGES, rows, strict=True):
            for expected, candidate in zip(spec.repins, row["repins"], strict=True):
                after[expected.path] = render_expected_repin(
                    after[expected.path],
                    expected.symbol,
                    expected.value_kind,
                    candidate["value"],
                )
    except (KeyError, TypeError, ExecutionError, ValueError) as exc:
        raise MaterializationError("C1 V6 repin reconstruction failed") from exc

    candidates = report["governance_candidates"]
    for name in ("current_source_anchor_v2", "v2_adapter_source_policy"):
        candidate = candidates[name]
        raw = planner.canonical_bytes(candidate["document"])
        if hashlib.sha256(raw).hexdigest() != candidate["canonical_sha256"]:
            raise MaterializationError("C1 governance candidate digest mismatch")
        path = candidate["path"]
        if path not in after:
            raise MaterializationError("C1 governance candidate path is unexpected")
        after[path] = raw
    return _C1Reconstruction(before=before, after=after)


def _require_exact_c1_transition(
    root: Path,
    c0_commit: str,
    c1_commit: str,
    reconstruction: _C1Reconstruction,
) -> None:
    before = reconstruction.before
    after = reconstruction.after
    expected_paths = v6_materializer.MATERIALIZED_PATHS
    raw_paths = git_boundary.git_stdout(
        root,
        ["diff", "--name-only", "-z", "--no-renames", c0_commit, c1_commit, "--"],
        64 * 1024,
    )
    try:
        actual_paths = tuple(
            sorted(item.decode("utf-8") for item in raw_paths.split(b"\0") if item)
        )
    except UnicodeDecodeError as exc:
        raise MaterializationError("C1 transition contains a non-UTF-8 path") from exc
    if actual_paths != expected_paths:
        raise MaterializationError("C1 transition path set differs from reconstruction")
    if set(before) != set(expected_paths) or set(after) != set(expected_paths):
        raise MaterializationError("C1 reconstruction path inventory mismatch")
    for path in expected_paths:
        if before[path] == after[path]:
            raise MaterializationError("C1 reconstructed transition contains a no-op")
        if _require_blob_mode(root, c0_commit, path) != "100644":
            raise MaterializationError("C0 transition file mode is not 100644")
        if _require_blob_mode(root, c1_commit, path) != "100644":
            raise MaterializationError("C1 transition file mode is not 100644")
        if _read_commit_blob(root, c0_commit, path) != before[path]:
            raise MaterializationError("C0 transition bytes differ from reconstruction")
        if _read_commit_blob(root, c1_commit, path) != after[path]:
            raise MaterializationError("C1 transition bytes differ from reconstruction")


def _select_settlement_program(programs: Any) -> dict[str, Any]:
    if type(programs) is not list:
        raise MaterializationError(
            "candidate report must contain exactly one V6 settlement program"
        )
    matches = [
        row for row in programs if type(row) is dict and row.get("stage_id") == "v6_settlement"
    ]
    if len(matches) != 1:
        raise MaterializationError(
            "candidate report must contain exactly one V6 settlement program"
        )
    row = matches[0]
    image_id = row.get("image_id")
    words = row.get("image_id_words")
    if (
        type(image_id) is not str
        or re.fullmatch(r"[0-9a-f]{64}", image_id) is None
        or type(words) is not list
        or len(words) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFFFFFF for word in words)
        or b"".join(word.to_bytes(4, "little") for word in words).hex() != image_id
    ):
        raise MaterializationError("V6 settlement image words do not encode its image ID")
    if all(word == 0 for word in words):
        raise MaterializationError("V6 settlement image ID must be nonzero")
    return dict(row)


def _require_zero_v7_placeholder(raw: bytes) -> None:
    try:
        source = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise MaterializationError("V7 child-policy source is not UTF-8") from exc
    declaration = re.compile(
        rf"^pub const {re.escape(V7_CHILD_POLICY_SYMBOL)}: \[u32; 8\] = (.+);$",
        re.MULTILINE,
    )
    matches = list(declaration.finditer(source))
    if len(matches) != 1 or matches[0].group(1) != "[0; 8]":
        raise MaterializationError("V7 child policy must contain the exact all-zero placeholder")


def _read_commit_blob(root: Path, commit: str, path: str) -> bytes:
    raw = git_boundary.git_stdout(
        root,
        ["show", f"{commit}:{path}"],
        MAX_TRANSITION_FILE_BYTES,
    )
    if not raw:
        raise MaterializationError("governed commit blob is empty")
    return raw


def _require_blob_mode(root: Path, commit: str, path: str) -> str:
    raw = git_boundary.git_stdout(
        root,
        ["ls-tree", "-z", commit, "--", path],
        512,
    )
    entries = [entry for entry in raw.split(b"\0") if entry]
    if len(entries) != 1:
        raise MaterializationError("governed commit path is absent or ambiguous")
    try:
        header, observed_path = entries[0].split(b"\t", 1)
        mode, kind, _object_id = header.split(b" ", 2)
        decoded_path = observed_path.decode("utf-8", errors="strict")
        decoded_mode = mode.decode("ascii", errors="strict")
    except (UnicodeDecodeError, ValueError) as exc:
        raise MaterializationError("governed commit tree entry is malformed") from exc
    if decoded_path != path or kind != b"blob":
        raise MaterializationError("governed commit path is not the expected blob")
    return decoded_mode


def _require_commit_id(value: Any, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise MaterializationError(f"{label} must be a 40-character lowercase commit ID")
    return value


def _rollback_transition(repo_root: Path, transition: _Transition) -> None:
    try:
        rollback_boundary.rollback_materialization(
            repo_root,
            transition.c1_commit,
            transition.patch,
            transition.before,
            transition.after,
            MATERIALIZED_PATHS,
        )
    except MaterializationPartialStateError:
        raise
    except MaterializationError as rollback_error:
        raise MaterializationPartialStateError(
            "V7 materialization rejected and governed rollback could not be verified"
        ) from rollback_error


def _close_output_best_effort(output: output_boundary.ExternalOutput) -> None:
    """Close after the fsynced manifest commit point without reversing success."""

    try:
        output_boundary.close_external_output(output)
    except OSError:
        try:
            os.close(output.directory_fd)
        except OSError:
            pass


def _manifest(
    transition: _Transition,
    *,
    mode: str,
    index_tree: str | None,
) -> dict[str, Any]:
    path = V7_CHILD_POLICY_PATH
    return {
        "schema": MANIFEST_SCHEMA,
        "status": mode,
        "c0_commit": transition.c0_commit,
        "c1_commit": transition.c1_commit,
        "plan_sha256": transition.plan_sha256,
        "observations_sha256": transition.observations_sha256,
        "candidate_report_sha256": transition.report_sha256,
        "final_source_snapshot_root_sha256": transition.final_source_root,
        "v6_settlement_image_id": transition.settlement_program["image_id"],
        "v6_settlement_image_id_words": transition.settlement_program["image_id_words"],
        "materialized_symbol": V7_CHILD_POLICY_SYMBOL,
        "generated_patch_sha256": hashlib.sha256(transition.patch).hexdigest(),
        "generated_patch_bytes": len(transition.patch),
        "materialized_paths": [
            {
                "path": path,
                "git_mode": transition.git_modes[path],
                "before_bytes": len(transition.before[path]),
                "before_sha256": hashlib.sha256(transition.before[path]).hexdigest(),
                "after_bytes": len(transition.after[path]),
                "after_sha256": hashlib.sha256(transition.after[path]).hexdigest(),
            }
        ],
        "checkout_index_tree": index_tree,
        "validated_facts": {
            "checkout_was_clean_at_exact_c1": True,
            "c1_is_direct_child_of_plan_c0": True,
            "c1_exactly_matches_reconstructed_v6_materialization": True,
            "plan_observations_and_report_recomposed": True,
            "candidate_contains_exactly_one_v6_settlement_program": True,
            "image_words_encode_v6_settlement_image_id": True,
            "v6_settlement_image_id_is_nonzero": True,
            "v7_policy_started_at_exact_all_zero_placeholder": True,
            "generated_patch_has_exact_v7_child_policy_path": True,
            "generated_patch_passes_index_check": True,
            "index_and_worktree_match_reconstruction": index_tree is not None,
        },
        "authority": {field: False for field in AUTHORITY_FIELDS},
        "non_claims": list(NON_CLAIMS),
    }
