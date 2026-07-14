#!/usr/bin/env python3
"""Check the committed, authority-neutral V6-to-V7 post-pin evidence chain.

The checker accepts one exact four-commit relation:

``C0 -> C1 -> C2 -> G``

``C1`` must be the independently reconstructed V6 identity materialization,
``C2`` must add only the exact V7 child-policy pin described by the committed
materialization manifest, and ``G`` must add only the four fixed canonical
evidence objects.  A successful result binds those committed bytes and keeps
every proof, receipt, release, settlement, and production authority claim
false.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_identity_materialization_git as git_boundary
from tools import zrpf_v6_v7_child_policy_materialization as materializer
from tools.zrpf_v6_identity_executor_types import ExecutionError
from tools.zrpf_v6_identity_source_snapshot import read_bounded_regular
from tools.zrpf_v6_identity_source_state import render_expected_repin

CHECK_SCHEMA = "zenodex/zrpf_v6_to_v7_post_pin_governance_check/v1"
EVIDENCE_DIRECTORY = "evidence/zrpf_v6_to_v7_post_pin_v1"
PLAN_PATH = f"{EVIDENCE_DIRECTORY}/identity-rebuild-plan.json"
OBSERVATIONS_PATH = f"{EVIDENCE_DIRECTORY}/identity-rebuild-observations.json"
REPORT_PATH = f"{EVIDENCE_DIRECTORY}/identity-rebuild-candidate-report.json"
MANIFEST_PATH = f"{EVIDENCE_DIRECTORY}/materialization-manifest.json"
EVIDENCE_PATHS = tuple(sorted((PLAN_PATH, OBSERVATIONS_PATH, REPORT_PATH, MANIFEST_PATH)))

AUTHORITY_FIELDS = materializer.AUTHORITY_FIELDS
NON_CLAIMS = (
    "committed_post_pin_binding_does_not_verify_or_generate_proofs",
    "candidate_report_c1_c2_and_governance_commit_remain_authority_neutral",
    "no_complete_build_input_closure",
    "no_cross_host_reproducibility",
    "no_receipt_or_release_authority",
    "no_source_to_program_binary_provenance_authority",
    "same_uid_checkout_race_resistance_is_not_claimed",
    "no_settlement_or_production_authority",
)

_MANIFEST_FIELDS = {
    "schema",
    "status",
    "c0_commit",
    "c1_commit",
    "plan_sha256",
    "observations_sha256",
    "candidate_report_sha256",
    "final_source_snapshot_root_sha256",
    "v6_settlement_image_id",
    "v6_settlement_image_id_words",
    "materialized_symbol",
    "generated_patch_sha256",
    "generated_patch_bytes",
    "materialized_paths",
    "checkout_index_tree",
    "validated_facts",
    "authority",
    "non_claims",
}
_VALIDATED_FACTS = {
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
    "index_and_worktree_match_reconstruction": True,
}


class GovernanceError(ValueError):
    """Stable fail-closed post-pin governance rejection."""


@dataclass(frozen=True)
class _GovernedChain:
    root: Path
    c0_commit: str
    c1_commit: str
    c2_commit: str
    governance_commit: str
    evidence: dict[str, dict[str, Any]]
    plan: dict[str, Any]
    observations: dict[str, Any]
    report: dict[str, Any]
    manifest: dict[str, Any]
    settlement: dict[str, Any]


@dataclass(frozen=True)
class _ExpectedPin:
    before: bytes
    after: bytes
    patch: bytes
    tree: str


def check_post_pin_governance(repo_root: Path) -> dict[str, Any]:
    """Validate the exact committed post-pin chain at the checkout's HEAD."""

    root = _require_governance_checkout(repo_root)
    governance_commit = _head_commit(root)
    c2_commit = _literal_parent(root, governance_commit, "governance commit")
    _require_exact_transition_paths(
        root,
        c2_commit,
        governance_commit,
        EVIDENCE_PATHS,
        "governance",
    )
    evidence = _load_committed_evidence(root, c2_commit, governance_commit)
    chain = _reconstruct_governed_chain(
        root,
        c2_commit,
        governance_commit,
        evidence,
    )
    _validate_manifest_metadata(chain)
    pin = _reconstruct_expected_pin(chain)
    _validate_c2_transition(chain, pin)
    _require_unchanged_checkout(chain)
    return _result(chain, pin)


def _reconstruct_governed_chain(
    root: Path,
    c2_commit: str,
    governance_commit: str,
    evidence: dict[str, dict[str, Any]],
) -> _GovernedChain:
    plan = evidence[PLAN_PATH]
    observations = evidence[OBSERVATIONS_PATH]
    report = evidence[REPORT_PATH]
    manifest = evidence[MANIFEST_PATH]

    recomputed = planner.check_observations(plan, observations, repo_root=root)
    if report != recomputed:
        raise GovernanceError("candidate report differs from independent recomposition")

    c0_commit = materializer._require_commit_id(plan.get("source_commit"), "plan C0")
    c1_commit = materializer._require_commit_id(manifest.get("c1_commit"), "manifest C1")
    _require_literal_parent(root, c1_commit, c0_commit, "C1")
    _require_literal_parent(root, c2_commit, c1_commit, "C2")
    reconstruction = materializer._reconstruct_c1_transition(
        root,
        c0_commit,
        observations,
        report,
    )
    materializer._require_exact_c1_transition(
        root,
        c0_commit,
        c1_commit,
        reconstruction,
    )
    settlement = materializer._select_settlement_program(report.get("programs"))
    return _GovernedChain(
        root=root,
        c0_commit=c0_commit,
        c1_commit=c1_commit,
        c2_commit=c2_commit,
        governance_commit=governance_commit,
        evidence=evidence,
        plan=plan,
        observations=observations,
        report=report,
        manifest=manifest,
        settlement=settlement,
    )


def _require_unchanged_checkout(chain: _GovernedChain) -> None:
    materializer._require_no_git_grafts(chain.root)
    git_boundary.require_no_git_replace_refs(chain.root)
    if (
        _require_governance_checkout(chain.root) != chain.root
        or _head_commit(chain.root) != chain.governance_commit
    ):
        raise GovernanceError("governance checkout changed during verification")


def _require_governance_checkout(repo_root: Path) -> Path:
    try:
        root = git_boundary.require_clean_checkout(repo_root)
    except (ExecutionError, git_boundary.MaterializationError) as exc:
        raise GovernanceError("governance check requires a clean checkout") from exc
    if root != repo_root:
        raise GovernanceError("repository root must be an exact canonical path")
    try:
        materializer._require_no_git_grafts(root)
    except git_boundary.MaterializationError as exc:
        raise GovernanceError("Git grafts are forbidden for governance") from exc
    return root


def _head_commit(root: Path) -> str:
    raw = git_boundary.git_stdout(root, ["rev-parse", "HEAD"], 128)
    try:
        value = raw.decode("ascii", errors="strict").strip()
    except UnicodeDecodeError as exc:
        raise GovernanceError("governance HEAD is not an ASCII commit ID") from exc
    return materializer._require_commit_id(value, "governance HEAD")


def _literal_parent(root: Path, commit: str, label: str) -> str:
    materializer._require_no_git_grafts(root)
    raw = git_boundary.git_stdout(root, ["cat-file", "commit", commit], 64 * 1024)
    headers, separator, _message = raw.partition(b"\n\n")
    if not separator:
        raise GovernanceError(f"{label} raw commit object is malformed")
    parents = [line[7:] for line in headers.splitlines() if line.startswith(b"parent ")]
    if len(parents) != 1:
        raise GovernanceError(f"{label} must have exactly one literal parent")
    try:
        parent = parents[0].decode("ascii", errors="strict")
    except UnicodeDecodeError as exc:
        raise GovernanceError(f"{label} parent is not ASCII") from exc
    materializer._require_no_git_grafts(root)
    return materializer._require_commit_id(parent, f"{label} parent")


def _require_literal_parent(root: Path, child: str, parent: str, label: str) -> None:
    if _literal_parent(root, child, label) != parent:
        raise GovernanceError(f"{label} is not the required direct child")


def _require_exact_transition_paths(
    root: Path,
    before: str,
    after: str,
    expected: tuple[str, ...],
    label: str,
) -> None:
    raw = git_boundary.git_stdout(
        root,
        ["diff", "--name-only", "-z", "--no-renames", before, after, "--"],
        64 * 1024,
    )
    try:
        actual = tuple(sorted(item.decode("utf-8") for item in raw.split(b"\0") if item))
    except UnicodeDecodeError as exc:
        raise GovernanceError(f"{label} transition contains a non-UTF-8 path") from exc
    if actual != expected:
        raise GovernanceError(f"{label} transition path set differs from policy")


def _load_committed_evidence(
    root: Path,
    c2_commit: str,
    governance_commit: str,
) -> dict[str, dict[str, Any]]:
    documents: dict[str, dict[str, Any]] = {}
    for relative in EVIDENCE_PATHS:
        if git_boundary.git_stdout(
            root,
            ["ls-tree", "-z", c2_commit, "--", relative],
            512,
        ):
            raise GovernanceError("governance evidence path already existed at C2")
        if materializer._require_blob_mode(root, governance_commit, relative) != "100644":
            raise GovernanceError("governance evidence mode must be 100644")
        committed = _read_commit_blob(root, governance_commit, relative)
        checkout = read_bounded_regular(
            root.joinpath(*PurePosixPath(relative).parts),
            f"governance evidence {relative}",
            planner.MAX_JSON_BYTES,
        )
        if checkout != committed:
            raise GovernanceError("governance evidence checkout differs from commit")
        document = planner.load_canonical_json(
            root.joinpath(*PurePosixPath(relative).parts),
            f"governance evidence {relative}",
        )
        if planner.canonical_bytes(document) != committed:
            raise GovernanceError("governance evidence canonical bytes differ from commit")
        documents[relative] = document
    return documents


def _validate_manifest_metadata(chain: _GovernedChain) -> None:
    manifest = chain.manifest
    _require_exact_fields(manifest, _MANIFEST_FIELDS, "materialization manifest")
    if manifest["schema"] != materializer.MANIFEST_SCHEMA:
        raise GovernanceError("materialization manifest schema mismatch")
    if manifest["status"] != "applied_indexed_candidate":
        raise GovernanceError("materialization manifest is not an applied candidate")
    if manifest["c0_commit"] != chain.c0_commit or manifest["c1_commit"] != chain.c1_commit:
        raise GovernanceError("materialization manifest ancestry mismatch")
    _require_equal(
        manifest["plan_sha256"],
        planner.canonical_sha256(chain.plan),
        "plan digest",
    )
    _require_equal(
        manifest["observations_sha256"],
        planner.canonical_sha256(chain.observations),
        "observations digest",
    )
    _require_equal(
        manifest["candidate_report_sha256"],
        planner.canonical_sha256(chain.report),
        "candidate report digest",
    )
    _require_equal(
        manifest["final_source_snapshot_root_sha256"],
        chain.report["final_source_snapshot_root_sha256"],
        "final source snapshot root",
    )
    _require_manifest_image(manifest, chain.settlement)
    if manifest["materialized_symbol"] != materializer.V7_CHILD_POLICY_SYMBOL:
        raise GovernanceError("materialized symbol mismatch")
    if manifest["validated_facts"] != _VALIDATED_FACTS:
        raise GovernanceError("materialization validated facts mismatch")
    expected_authority = {field: False for field in materializer.AUTHORITY_FIELDS}
    if manifest["authority"] != expected_authority or any(
        value is not False for value in manifest["authority"].values()
    ):
        raise GovernanceError("materialization authority fields must remain exactly false")
    if manifest["non_claims"] != list(materializer.NON_CLAIMS):
        raise GovernanceError("materialization non-claims mismatch")


def _reconstruct_expected_pin(chain: _GovernedChain) -> _ExpectedPin:
    _require_exact_transition_paths(
        chain.root,
        chain.c1_commit,
        chain.c2_commit,
        materializer.MATERIALIZED_PATHS,
        "C2",
    )
    before = materializer._read_commit_blob(
        chain.root,
        chain.c1_commit,
        materializer.V7_CHILD_POLICY_PATH,
    )
    materializer._require_zero_v7_placeholder(before)
    try:
        after = render_expected_repin(
            before,
            materializer.V7_CHILD_POLICY_SYMBOL,
            "image_id_words_le",
            chain.settlement["image_id_words"],
        )
    except ExecutionError as exc:
        raise GovernanceError("expected V7 child-policy source could not be rendered") from exc
    patch = git_boundary.build_patch(
        {materializer.V7_CHILD_POLICY_PATH: before},
        {materializer.V7_CHILD_POLICY_PATH: after},
        materializer.MATERIALIZED_PATHS,
    )
    tree = git_boundary._expected_materialized_tree(
        chain.root,
        chain.c1_commit,
        {materializer.V7_CHILD_POLICY_PATH: after},
        materializer.MATERIALIZED_PATHS,
    )
    return _ExpectedPin(before=before, after=after, patch=patch, tree=tree)


def _validate_c2_transition(chain: _GovernedChain, pin: _ExpectedPin) -> None:
    if (
        materializer._require_blob_mode(
            chain.root,
            chain.c2_commit,
            materializer.V7_CHILD_POLICY_PATH,
        )
        != "100644"
    ):
        raise GovernanceError("C2 child-policy mode must be 100644")
    actual_after = materializer._read_commit_blob(
        chain.root,
        chain.c2_commit,
        materializer.V7_CHILD_POLICY_PATH,
    )
    if actual_after != pin.after:
        raise GovernanceError("C2 child-policy bytes differ from exact materialization")
    c2_tree = _commit_tree(chain.root, chain.c2_commit)
    if c2_tree != pin.tree or chain.manifest["checkout_index_tree"] != pin.tree:
        raise GovernanceError("C2 tree differs from exact materialization manifest")
    expected_path = {
        "path": materializer.V7_CHILD_POLICY_PATH,
        "git_mode": "100644",
        "before_bytes": len(pin.before),
        "before_sha256": hashlib.sha256(pin.before).hexdigest(),
        "after_bytes": len(pin.after),
        "after_sha256": hashlib.sha256(pin.after).hexdigest(),
    }
    if chain.manifest["materialized_paths"] != [expected_path]:
        raise GovernanceError("materialization path record mismatch")
    if chain.manifest["generated_patch_sha256"] != hashlib.sha256(
        pin.patch
    ).hexdigest() or chain.manifest["generated_patch_bytes"] != len(pin.patch):
        raise GovernanceError("materialization patch identity mismatch")


def _require_manifest_image(
    manifest: dict[str, Any],
    settlement: dict[str, Any],
) -> None:
    image_id = manifest["v6_settlement_image_id"]
    words = manifest["v6_settlement_image_id_words"]
    if type(image_id) is not str or re.fullmatch(r"[0-9a-f]{64}", image_id) is None:
        raise GovernanceError("materialization image ID is malformed")
    if (
        type(words) is not list
        or len(words) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFFFFFF for word in words)
        or b"".join(word.to_bytes(4, "little") for word in words).hex() != image_id
    ):
        raise GovernanceError("materialization image words do not encode the image ID")
    if all(word == 0 for word in words):
        raise GovernanceError("materialization image ID must be nonzero")
    if image_id != settlement["image_id"] or words != settlement["image_id_words"]:
        raise GovernanceError("materialization image identity differs from report")


def _commit_tree(root: Path, commit: str) -> str:
    raw = git_boundary.git_stdout(root, ["rev-parse", f"{commit}^{{tree}}"], 128)
    try:
        tree = raw.decode("ascii", errors="strict").strip()
    except UnicodeDecodeError as exc:
        raise GovernanceError("C2 tree identity is not ASCII") from exc
    if re.fullmatch(r"[0-9a-f]{40,64}", tree) is None:
        raise GovernanceError("C2 tree identity is malformed")
    return tree


def _read_commit_blob(root: Path, commit: str, relative: str) -> bytes:
    raw = git_boundary.git_stdout(
        root,
        ["show", f"{commit}:{relative}"],
        planner.MAX_JSON_BYTES,
    )
    if not raw:
        raise GovernanceError("governance evidence blob is empty")
    return raw


def _require_exact_fields(value: Any, expected: set[str], label: str) -> None:
    if type(value) is not dict or set(value) != expected:
        raise GovernanceError(f"{label} fields differ from the exact schema")


def _require_equal(actual: Any, expected: Any, label: str) -> None:
    if actual != expected:
        raise GovernanceError(f"materialization {label} mismatch")


def _result(chain: _GovernedChain, pin: _ExpectedPin) -> dict[str, Any]:
    return {
        "schema": CHECK_SCHEMA,
        "status": "committed_post_pin_governance_binding_checked",
        "c0_commit": chain.c0_commit,
        "c1_commit": chain.c1_commit,
        "c2_commit": chain.c2_commit,
        "governance_commit": chain.governance_commit,
        "plan_sha256": planner.canonical_sha256(chain.evidence[PLAN_PATH]),
        "observations_sha256": planner.canonical_sha256(chain.evidence[OBSERVATIONS_PATH]),
        "candidate_report_sha256": planner.canonical_sha256(chain.evidence[REPORT_PATH]),
        "materialization_manifest_sha256": planner.canonical_sha256(chain.evidence[MANIFEST_PATH]),
        "v6_settlement_image_id": chain.settlement["image_id"],
        "v6_settlement_image_id_words": chain.settlement["image_id_words"],
        "v7_child_policy_tree": pin.tree,
        "v7_child_policy_sha256": hashlib.sha256(pin.after).hexdigest(),
        "validated_facts": {
            "governance_checkout_is_clean_and_exact": True,
            "c1_is_literal_direct_child_of_c0": True,
            "c1_matches_exact_v6_materialization": True,
            "c2_is_literal_direct_child_of_c1": True,
            "c2_contains_only_exact_v7_child_pin": True,
            "governance_commit_is_literal_direct_child_of_c2": True,
            "governance_commit_adds_only_fixed_canonical_evidence": True,
            "manifest_recomposes_from_committed_evidence": True,
            "v6_settlement_image_id_is_nonzero_and_exact": True,
            "committed_v7_policy_matches_manifest_and_c2_tree": True,
        },
        "authority": {field: False for field in AUTHORITY_FIELDS},
        "non_claims": list(NON_CLAIMS),
    }
