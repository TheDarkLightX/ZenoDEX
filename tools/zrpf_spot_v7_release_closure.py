#!/usr/bin/env python3
"""Orchestrate authority-neutral Spot V7 source/build closure evidence."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from tools import zrpf_spot_v7_release_schema as release_schema
from tools import zrpf_v6_v7_post_pin_governance as governance
from tools.zrpf_spot_v7_release_ancestry import (
    require_clean_root,
    validate_child_pin,
    validate_governed_ancestry,
)
from tools.zrpf_spot_v7_release_inventory import build_source_closure
from tools.zrpf_spot_v7_release_schema import (
    AUTHORITY_FIELDS,
    EVIDENCE_SCHEMA,
    NON_CLAIMS,
    PLAN_FIELDS,
    PLAN_SCHEMA,
    ReleaseClosureError,
    build_closure,
    canonical_sha256,
    require_exact_fields,
    require_nonzero_hex,
    validate_runtime_identity,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
RUNTIME_IDENTITY_SCHEMA = release_schema.RUNTIME_IDENTITY_SCHEMA
V7_CHILD_POLICY_PATH = release_schema.V7_CHILD_POLICY_PATH
V7_CHILD_POLICY_SYMBOL = release_schema.V7_CHILD_POLICY_SYMBOL
V7_WORKSPACE_MANIFEST = release_schema.V7_WORKSPACE_MANIFEST
canonical_bytes = release_schema.canonical_bytes


def build_release_closure_plan(
    repo_root: Path,
    runtime_identity: Any,
) -> dict[str, Any]:
    """Build the deterministic authority-neutral V7 closure plan at exact G."""

    root = require_clean_root(repo_root)
    runtime = validate_runtime_identity(runtime_identity)
    governed = governance.check_post_pin_governance(root)
    ancestry = validate_governed_ancestry(root, governed)
    source_closure = build_source_closure(root, ancestry["governance_commit"])
    return {
        "schema": PLAN_SCHEMA,
        "status": "authority_neutral_v7_release_closure_plan",
        "ancestry": ancestry,
        "v7_child_pin": validate_child_pin(root, ancestry, governed),
        "source_closure": source_closure,
        "build_closure": build_closure(runtime),
        "required_future_release_evidence": {
            "two_clean_builds": True,
            "fresh_target_and_output_per_build": True,
            "different_outer_host_paths": True,
            "same_canonical_in_container_source_path": True,
            "byte_identical_guest_elf_required": True,
            "equal_recomputed_v7_image_id_required": True,
            "source_built_verifier_replay_required": True,
            "exact_seal_mutation_rejection_required": True,
            "independent_release_governance_required": True,
        },
        "authority": {field: False for field in AUTHORITY_FIELDS},
        "non_claims": list(NON_CLAIMS),
    }


def check_release_closure_plan(
    repo_root: Path,
    plan: Any,
    runtime_identity: Any,
    *,
    expected_plan_sha256: str,
) -> dict[str, Any]:
    """Recompose one plan and emit canonical authority-neutral evidence."""

    require_exact_fields(plan, PLAN_FIELDS, "release-closure plan")
    require_nonzero_hex(expected_plan_sha256, 64, "expected plan SHA-256")
    actual_sha256 = canonical_sha256(plan)
    if actual_sha256 != expected_plan_sha256:
        raise ReleaseClosureError("release-closure plan digest differs from expectation")
    runtime = validate_runtime_identity(runtime_identity)
    expected = build_release_closure_plan(repo_root, runtime)
    if plan != expected:
        if plan.get("build_closure", {}).get("runtime_identity") != runtime:
            raise ReleaseClosureError("runtime identity differs from the governed plan")
        raise ReleaseClosureError("release closure differs from the deterministic plan")
    _require_authority_false(plan["authority"])
    return _render_evidence(plan, actual_sha256)


def _require_authority_false(authority: Any) -> None:
    expected = {field: False for field in AUTHORITY_FIELDS}
    if authority != expected or any(value is not False for value in authority.values()):
        raise ReleaseClosureError("release closure authority must remain exactly false")


def _render_evidence(plan: dict[str, Any], plan_sha256: str) -> dict[str, Any]:
    ancestry = plan["ancestry"]
    source = plan["source_closure"]
    return {
        "schema": EVIDENCE_SCHEMA,
        "status": "authority_neutral_v7_release_closure_checked",
        "plan_sha256": plan_sha256,
        "c0_commit": ancestry["c0_commit"],
        "c1_commit": ancestry["c1_commit"],
        "c2_commit": ancestry["c2_commit"],
        "governance_commit": ancestry["governance_commit"],
        "governance_tree": ancestry["governance_tree"],
        "v7_child_image_id": plan["v7_child_pin"]["image_id"],
        "source_closure_root_sha256": source["inventory_root_sha256"],
        "lockfile_set_root_sha256": source["lockfile_set_root_sha256"],
        "runtime_identity_sha256": plan["build_closure"]["runtime_identity_sha256"],
        "validated_facts": {
            "literal_c0_c1_c2_g_ancestry_checked": True,
            "governed_nonzero_v7_child_pin_checked": True,
            "recursive_local_path_dependency_graph_checked": True,
            "local_cargo_patch_and_replace_overrides_checked": True,
            "all_reached_workspace_lockfiles_bound": True,
            "ancestor_cargo_configs_bound": True,
            "tracked_workspace_source_superset_bound": True,
            "literal_external_compiler_inputs_bound": True,
            "literal_compiler_input_fixed_point_checked": True,
            "literal_compiler_source_graph_acyclic": True,
            "toolchain_and_container_identities_bound": True,
            "declared_runtime_identity_bound": True,
            "no_authority_promoted": True,
        },
        "authority": {field: False for field in AUTHORITY_FIELDS},
        "non_claims": list(NON_CLAIMS),
    }
