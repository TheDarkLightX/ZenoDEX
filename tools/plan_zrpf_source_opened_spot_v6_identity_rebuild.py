#!/usr/bin/env python3
"""Plan and check the acyclic source-opened Spot V6 identity rebuild.

This tool is deliberately authority-neutral.  It neither builds guests nor
edits policy constants.  ``plan`` emits the exact bounded build/repin order;
``check`` validates independently captured stage observations and emits one
candidate report whose authority claims are all false.

The final clean rebuild comparison is load-bearing.  It establishes, for the
observed candidate bytes, that downstream policy repins did not feed back into
an upstream program binary.  The report remains a local candidate until the
separate source, build, proof, replay, release, and admission gates accept it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, NoReturn, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
PLAN_SCHEMA = "zenodex/zrpf_spot_v6_identity_rebuild_plan/v2"
OBSERVATION_SCHEMA = "zenodex/zrpf_spot_v6_identity_rebuild_observations/v2"
REPORT_SCHEMA = "zenodex/zrpf_spot_v6_identity_rebuild_candidate_report/v2"
RUNNER_SECURITY_POSTURE_SCHEMA = (
    "zenodex/zrpf_v6_identity_runner_security_posture/v1"
)
CARGO_REGISTRY_IDENTITY_SCHEMA = (
    "zenodex/zrpf_bounded_cargo_registry_identity/v1"
)
CANONICAL_SOURCE_ROOT = "/src/zenodex"
CANONICAL_CARGO = "/risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin/cargo"
CANONICAL_RUSTC = "/risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin/rustc"
CANONICAL_R0VM = "/risc0/bin/r0vm"
CANONICAL_CARGO_RISCZERO = "/risc0/bin/cargo-risczero"
BUILD_IMAGE = "sha256:de7091a181792417fbd5eaf6b3aff77d8a26ae0f2ae7ce298c01bf4ad9cd4b9c"
BUILD_IMAGE_PARENT = (
    "ubuntu@sha256:4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90"
)
MAX_JSON_BYTES = 2 * 1024 * 1024
MAX_JSON_DEPTH = 20
MAX_JSON_NODES = 8_192
MAX_JSON_STRING_CHARS = 4_096
MAX_JSON_INTEGER_DIGITS = 20
MAX_PROGRAM_BINARY_BYTES = 64 * 1024 * 1024
MAX_HOST_BINARY_BYTES = 64 * 1024 * 1024
MAX_TRACKED_SOURCE_FILES = 8_192
MAX_TRACKED_SOURCE_BYTES = 64 * 1024 * 1024
BUILD_JOBS = 2
BUILD_CPUS = 2
BUILD_MEMORY_BYTES = 6 * 1024 * 1024 * 1024
TARGET_TMPFS_QUOTA_BYTES = 3 * 1024 * 1024 * 1024
OUTPUT_TMPFS_QUOTA_BYTES = 160 * 1024 * 1024
MAX_PINNED_TOOL_BYTES = 256 * 1024 * 1024
MAX_CARGO_REGISTRY_FILES = 100_000
MAX_CARGO_REGISTRY_BYTES = 2 * 1024 * 1024 * 1024
MAX_CARGO_REGISTRY_FILE_BYTES = 64 * 1024 * 1024
NESTED_CARGO_WRAPPER_BYTES = f"""#!/bin/bash
set -euo pipefail
export CARGO_BUILD_JOBS={BUILD_JOBS}
exec {CANONICAL_CARGO} "$@"
""".encode("ascii")
NESTED_CARGO_WRAPPER_SHA256 = hashlib.sha256(NESTED_CARGO_WRAPPER_BYTES).hexdigest()
RUNNER_RESOURCE_POLICY = {
    "aggregate_container_cpu_quota": BUILD_CPUS,
    "outer_cargo_jobs": BUILD_JOBS,
    "nested_cargo_jobs": BUILD_JOBS,
    "nested_cargo_wrapper_sha256": NESTED_CARGO_WRAPPER_SHA256,
    "target_storage": "container_tmpfs",
    "target_mount_execution": "exec_required",
    "target_quota_bytes": TARGET_TMPFS_QUOTA_BYTES,
    "output_storage": "container_tmpfs",
    "output_and_auxiliary_mount_execution": "noexec_required",
    "output_quota_bytes": OUTPUT_TMPFS_QUOTA_BYTES,
    "output_transport": "bounded_base64_stdout_v1",
    "container_cleanup_identity": "private_cidfile_exact_id_v1",
}

TOOLCHAIN = {
    "cargo_version": "cargo 1.94.1-dev (29ea6fb6a 2026-03-24)",
    "outer_cargo_sha256": "b1d3a17e834a1cd593634d8f6e7866bbc498e56f5205560c7418bae6ee4447da",
    "nested_cargo_sha256": "b1d3a17e834a1cd593634d8f6e7866bbc498e56f5205560c7418bae6ee4447da",
    "rustc_version": "rustc 1.94.1-dev (06e01cb0d 2026-04-09)",
    "rustc_sha256": "e7fd8dcc397b4e4756cdb8ceb1851347daf326234b78abea3d42d4e61ad5e8e5",
    "r0vm_version": "risc0-r0vm 3.0.5",
    "r0vm_sha256": "36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b",
    "cargo_risczero_version": "cargo-risczero 3.0.5",
    "cargo_risczero_sha256": "45aba69689cef25d81237f3ff62456fc96ff1e23f75adfcd16f7c8b8c1606619",
    "risc0_zkvm_version": "3.0.5",
}

AUTHORITY_FLAGS = (
    "complete_build_input_closure_verified",
    "cross_host_reproducible_build",
    "evidence_promoted",
    "proofs_generated",
    "receipts_verified",
    "release_authority",
    "settlement_authority",
    "source_to_program_binary_provenance_verified",
    "production_authority",
)

NON_CLAIMS = (
    "candidate_report_does_not_promote_evidence",
    "no_complete_build_input_closure",
    "no_cross_host_reproducibility",
    "no_proof_or_receipt_generation",
    "no_release_authority",
    "no_settlement_authority",
    "no_source_to_binary_provenance_authority",
    "no_same_uid_resistance",
    "no_production_authority",
)


class RebuildPlanError(ValueError):
    """Stable fail-closed planning or observation rejection."""


@dataclass(frozen=True)
class RepinSpec:
    path: str
    symbol: str
    value_kind: str
    visibility: str


@dataclass(frozen=True)
class StageSpec:
    ordinal: int
    stage_id: str
    topology_node: str
    predecessor_stage: str | None
    workspace: str
    cargo_package: str
    method_host_package: str
    guest_package: str
    artifact_file: str
    repins: tuple[RepinSpec, ...]


STAGES = (
    StageSpec(
        1,
        "source_spot",
        "source_spot_guest_and_cli",
        None,
        "zk/state_proof_risc0",
        "tau-state-proof-risc0-cli",
        "tau-state-proof-risc0-methods",
        "tau-state-proof-risc0-spot-leaf",
        "source_spot.bin",
        (
            RepinSpec(
                "zk/zrpf_risc0/shared/src/source_policy_v2.rs",
                "PINNED_CURRENT_SPOT_LEAF_IMAGE_ID_V2",
                "image_id_words_le",
                "v2_adapter_guest",
            ),
            RepinSpec(
                "zk/zrpf_risc0/shared/src/source_policy_v2.rs",
                "PINNED_CURRENT_SPOT_LEAF_PROGRAM_SHA256_V2",
                "sha256_bytes",
                "v2_adapter_guest",
            ),
            RepinSpec(
                "zk/zrpf_risc0/shared/src/source_policy_v2.rs",
                "PINNED_CURRENT_SPOT_SOURCE_CLOSURE_ROOT_V2",
                "source_closure_root_bytes",
                "v2_adapter_guest",
            ),
        ),
    ),
    StageSpec(
        2,
        "v2_adapter",
        "v2_adapter_guest",
        "source_spot",
        "zk/zrpf_risc0",
        "zenodex-zrpf-risc0-methods",
        "zenodex-zrpf-risc0-methods",
        "zenodex-zrpf-risc0-v2-leaf-adapter",
        "v2_adapter.bin",
        (
            RepinSpec(
                "zk/zrpf_risc0/spot_value_leaf_v6_shared/src/lib.rs",
                "PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID",
                "image_id_words_le",
                "leaf_guest",
            ),
        ),
    ),
    StageSpec(
        3,
        "v6_leaf",
        "v6_leaf_guest",
        "v2_adapter",
        "zk/zrpf_risc0",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-value-leaf-v6",
        "spot_value_leaf_v6.bin",
        (
            RepinSpec(
                "zk/zrpf_risc0/spot_value_aggregate_l1_policy_v6/src/lib.rs",
                "PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6",
                "image_id_words_le",
                "l1_guest",
            ),
        ),
    ),
    StageSpec(
        4,
        "v6_l1",
        "v6_l1_guest",
        "v6_leaf",
        "zk/zrpf_risc0",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-value-aggregate-l1-v6",
        "spot_value_aggregate_l1_v6.bin",
        (
            RepinSpec(
                "zk/zrpf_risc0/spot_value_aggregate_l2_policy_v6/src/lib.rs",
                "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6",
                "image_id_words_le",
                "l2_guest",
            ),
        ),
    ),
    StageSpec(
        5,
        "v6_l2",
        "v6_l2_guest",
        "v6_l1",
        "zk/zrpf_risc0",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-value-aggregate-l2-v6",
        "spot_value_aggregate_l2_v6.bin",
        (
            RepinSpec(
                "zk/zrpf_risc0/spot_value_aggregate_root_policy_v6/src/lib.rs",
                "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6",
                "image_id_words_le",
                "settlement_guest",
            ),
        ),
    ),
    StageSpec(
        6,
        "v6_settlement",
        "v6_settlement_guest",
        "v6_l2",
        "zk/zrpf_risc0",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-source-opened-spot-settlement-v6",
        "source_opened_spot_settlement_v6.bin",
        (
            RepinSpec(
                "zk/zrpf_risc0/spot_settlement_root_policy_v6/src/lib.rs",
                "PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6",
                "image_id_words_le",
                "host_only",
            ),
        ),
    ),
)

TOPOLOGY_NODES = (
    "source_spot_guest_and_cli",
    "current_source_policy_v2",
    "v2_adapter_guest",
    "leaf_expected_adapter_pin",
    "v6_leaf_guest",
    "l1_child_pin",
    "v6_l1_guest",
    "l2_child_pin",
    "v6_l2_guest",
    "settlement_child_pin",
    "v6_settlement_guest",
    "settlement_self_host_pin",
    "host_verifier",
)

TOPOLOGY_EDGES = (
    ("source_spot_guest_and_cli", "current_source_policy_v2"),
    ("current_source_policy_v2", "v2_adapter_guest"),
    ("v2_adapter_guest", "leaf_expected_adapter_pin"),
    ("leaf_expected_adapter_pin", "v6_leaf_guest"),
    ("v6_leaf_guest", "l1_child_pin"),
    ("l1_child_pin", "v6_l1_guest"),
    ("v6_l1_guest", "l2_child_pin"),
    ("l2_child_pin", "v6_l2_guest"),
    ("v6_l2_guest", "settlement_child_pin"),
    ("settlement_child_pin", "v6_settlement_guest"),
    ("v6_settlement_guest", "settlement_self_host_pin"),
    ("settlement_self_host_pin", "host_verifier"),
)

REQUIRED_GOVERNANCE_UPDATES = (
    "replace the pending current-source V2 anchor from the exact stage-1 candidate",
    "replace the pending V2 adapter policy from the exact stage-2 candidate",
    "V6 program build record and governed checker anchor",
    "fresh source, adapter, leaf, L1, L2, and settlement receipts",
    "seal-mutation and exact-journal negative controls",
    "release manifest, CBC matrix, and public claim review",
)

PROTECTED_HISTORICAL_ARTIFACTS = (
    "config/proof_profiles/zrpf_v1_retained_source_anchor_v1.json",
    "config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json",
    "zk/zrpf_risc0/methods/v1_leaf_adapter/src/main.rs",
    "zk/zrpf_risc0/shared/src/source_policy_v1.rs",
)

RELEVANT_WORKSPACE_ROOTS = (
    "zk/state_proof_risc0",
    "zk/zrpf_protocol",
    "zk/zrpf_risc0",
)

SOURCE_GUEST_WORKSPACE_ROOTS = ("zk/state_proof_risc0",)


def canonical_bytes(document: Any) -> bytes:
    return (
        json.dumps(document, allow_nan=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def canonical_sha256(document: Any) -> str:
    return hashlib.sha256(canonical_bytes(document)).hexdigest()


def build_plan(
    source_commit: str,
    run_root: str,
    *,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    """Return the candidate plan without executing any build."""

    _require_hex(source_commit, 40, "source commit")
    _require_absolute_path(run_root, "run root")
    _validate_static_topology()
    workspace_coverage = audit_tracked_workspace_source(repo_root, source_commit)
    source_guest_coverage = audit_source_guest_workspace(repo_root, source_commit)
    stage_rows = [_stage_plan(spec, run_root) for spec in STAGES]
    return {
        "schema": PLAN_SCHEMA,
        "status": "dry_run_candidate_rebuild_plan",
        "source_commit": source_commit,
        "host_run_root": run_root,
        "canonical_in_sandbox_source_root": CANONICAL_SOURCE_ROOT,
        "tracked_workspace_source_coverage": workspace_coverage,
        "source_guest_source_coverage": source_guest_coverage,
        "toolchain": dict(TOOLCHAIN),
        "resource_policy": {
            "build_image": BUILD_IMAGE,
            "build_image_parent": BUILD_IMAGE_PARENT,
            "build_cpus": BUILD_CPUS,
            "build_jobs": BUILD_JOBS,
            "build_memory_bytes": BUILD_MEMORY_BYTES,
            "target_storage": RUNNER_RESOURCE_POLICY["target_storage"],
            "target_quota_bytes": TARGET_TMPFS_QUOTA_BYTES,
            "output_storage": RUNNER_RESOURCE_POLICY["output_storage"],
            "output_quota_bytes": OUTPUT_TMPFS_QUOTA_BYTES,
            "output_transport": RUNNER_RESOURCE_POLICY["output_transport"],
            "nested_cargo_wrapper_sha256": NESTED_CARGO_WRAPPER_SHA256,
            "cargo_locked": True,
            "cargo_offline": True,
            "network_disabled": True,
            "fresh_target_per_pass": True,
            "fresh_output_per_pass": True,
            "outer_cargo_path": CANONICAL_CARGO,
            "nested_cargo_path": CANONICAL_CARGO,
            "rustc_path": CANONICAL_RUSTC,
            "r0vm_path": CANONICAL_R0VM,
            "cargo_risczero_path": CANONICAL_CARGO_RISCZERO,
        },
        "topology": {
            "nodes": list(TOPOLOGY_NODES),
            "edges": [list(edge) for edge in TOPOLOGY_EDGES],
            "acyclic": True,
            "downstream_policy_must_not_feed_upstream_program": True,
        },
        "stages": stage_rows,
        "settlement_self_image_two_pass": {
            "first_pass": "build v6_settlement before the host-only self pin",
            "repin_path": STAGES[-1].repins[0].path,
            "repin_symbol": STAGES[-1].repins[0].symbol,
            "second_pass": "rebuild v6_settlement after the host-only self pin",
            "required_equality": [
                "program_binary_bytes",
                "program_binary_sha256",
                "image_id",
                "image_id_words",
            ],
        },
        "final_clean_rebuild": {
            "required": True,
            "fresh_target_and_output_per_stage": True,
            "comparison": "all six final binaries and image IDs equal primary stage outputs",
            "purpose": "detect any downstream policy feedback into an upstream program",
        },
        "host_verifier": {
            "workspace": "zk/zrpf_risc0",
            "cargo_package": "zenodex-zrpf-risc0-verifier",
            "binary": "source-opened-spot-settlement-verifier-v6",
            "expected_settlement_identity_source": STAGES[-1].repins[0].path,
            "command": _host_verifier_command(),
        },
        "required_governance_updates_after_candidate": list(REQUIRED_GOVERNANCE_UPDATES),
        "protected_historical_artifacts": list(PROTECTED_HISTORICAL_ARTIFACTS),
        "authority": {field: False for field in AUTHORITY_FLAGS},
        "non_claims": list(NON_CLAIMS),
    }


def _stage_plan(spec: StageSpec, run_root: str) -> dict[str, Any]:
    stem = f"{spec.ordinal:02d}-{spec.stage_id.replace('_', '-')}"
    return {
        "ordinal": spec.ordinal,
        "stage_id": spec.stage_id,
        "topology_node": spec.topology_node,
        "predecessor_stage": spec.predecessor_stage,
        "workspace": spec.workspace,
        "cargo_package": spec.cargo_package,
        "method_host_package": spec.method_host_package,
        "guest_package": spec.guest_package,
        "artifact_file": spec.artifact_file,
        "target_directory": f"targets/{stem}",
        "output_directory": f"outputs/{stem}",
        "host_target_directory": f"{run_root}/targets/{stem}",
        "host_output_directory": f"{run_root}/outputs/{stem}",
        "command": _guest_command(spec, stem),
        "identity_command": [
            CANONICAL_R0VM,
            "--elf",
            f"/build/{stem}/output/{spec.artifact_file}",
            "--id",
        ],
        "extraction": {
            "source": (
                f"/build/{stem}/target/riscv-guest/{spec.method_host_package}/"
                f"{spec.guest_package}/riscv32im-risc0-zkvm-elf/release/"
                f"{spec.guest_package}.bin"
            ),
            "destination": f"/build/{stem}/output/{spec.artifact_file}",
            "required_magic_hex": "52304246",
            "maximum_bytes": MAX_PROGRAM_BINARY_BYTES,
            "destination_mode": "0444",
        },
        "companion_host_binary": (
            {
                "source": f"/build/{stem}/target/release/tau-state-proof-risc0-cli",
                "destination": f"/build/{stem}/output/tau-state-proof-risc0-cli",
                "maximum_bytes": MAX_HOST_BINARY_BYTES,
                "destination_mode": "0555",
            }
            if spec.stage_id == "source_spot"
            else None
        ),
        "repins_after_success": [
            {
                "path": item.path,
                "symbol": item.symbol,
                "value_kind": item.value_kind,
                "visibility": item.visibility,
            }
            for item in spec.repins
        ],
    }


def _guest_command(spec: StageSpec, stem: str) -> list[str]:
    return [
        CANONICAL_CARGO,
        "build",
        "--manifest-path",
        f"{CANONICAL_SOURCE_ROOT}/{spec.workspace}/Cargo.toml",
        "--package",
        spec.cargo_package,
        "--release",
        "--locked",
        "--offline",
        "--jobs",
        str(BUILD_JOBS),
        "--target-dir",
        f"/build/{stem}/target",
    ]


def _host_verifier_command() -> list[str]:
    return [
        CANONICAL_CARGO,
        "build",
        "--manifest-path",
        f"{CANONICAL_SOURCE_ROOT}/zk/zrpf_risc0/Cargo.toml",
        "--package",
        "zenodex-zrpf-risc0-verifier",
        "--bin",
        "source-opened-spot-settlement-verifier-v6",
        "--release",
        "--locked",
        "--offline",
        "--jobs",
        str(BUILD_JOBS),
        "--target-dir",
        "/build/host-verifier/target",
    ]


def check_observations(
    plan: dict[str, Any], observations: dict[str, Any]
) -> dict[str, Any]:
    """Validate one complete candidate observation bundle."""

    _validate_plan(plan)
    _require_exact_fields(
        observations,
        {
            "schema",
            "plan_sha256",
            "source_commit",
            "toolchain",
            "runner_security_posture",
            "stages",
            "settlement_self_image_two_pass",
            "final_clean_rebuild",
            "host_verifier",
        },
        "observations",
    )
    _require_equal(observations["schema"], OBSERVATION_SCHEMA, "observation schema")
    _require_equal(observations["plan_sha256"], canonical_sha256(plan), "plan SHA-256")
    _require_equal(observations["source_commit"], plan["source_commit"], "source commit")
    _require_equal(observations["toolchain"], TOOLCHAIN, "toolchain")
    runner_security_posture = check_runner_security_posture(
        observations["runner_security_posture"]
    )
    expected_source_tree_root = plan["source_guest_source_coverage"][
        "inventory_root_sha256"
    ]
    stage_programs = _check_stage_observations(
        observations["stages"], expected_source_tree_root
    )
    _check_settlement_two_pass(
        observations["settlement_self_image_two_pass"], stage_programs[-1]
    )
    final_root = _check_final_clean_rebuild(
        observations["final_clean_rebuild"], stage_programs
    )
    host_binary = _check_host_verifier(
        observations["host_verifier"], stage_programs[-1]
    )
    governance_candidates = _build_governance_candidates(
        plan,
        observations["stages"][0],
        observations["stages"][1],
    )
    return _candidate_report(
        plan,
        stage_programs,
        observations["stages"][0]["companion_host_binary"],
        final_root,
        host_binary,
        runner_security_posture,
        canonical_sha256(observations),
        governance_candidates,
    )


def check_runner_security_posture(value: Any) -> dict[str, Any]:
    """Validate and detach the exact authority-neutral runner posture."""

    _validate_json_shape(value)
    _require_exact_fields(
        value,
        {
            "schema",
            "tool_identities",
            "cargo_registry_identity",
            "resource_policy",
            "same_uid_resistance",
            "complete_build_input_closure_verified",
        },
        "runner security posture",
    )
    _require_equal(
        value["schema"],
        RUNNER_SECURITY_POSTURE_SCHEMA,
        "runner security posture schema",
    )
    expected_tools = {
        "cargo": TOOLCHAIN["outer_cargo_sha256"],
        "rustc": TOOLCHAIN["rustc_sha256"],
        "r0vm": TOOLCHAIN["r0vm_sha256"],
        "cargo_risczero": TOOLCHAIN["cargo_risczero_sha256"],
    }
    _require_exact_fields(
        value["tool_identities"],
        set(expected_tools),
        "runner tool identities",
    )
    for name, expected_sha256 in expected_tools.items():
        row = value["tool_identities"][name]
        _require_exact_fields(row, {"sha256", "bytes"}, f"runner tool {name}")
        _require_equal(row["sha256"], expected_sha256, f"runner tool {name} SHA-256")
        _require_bounded_positive_int(
            row["bytes"],
            MAX_PINNED_TOOL_BYTES,
            f"runner tool {name} bytes",
        )

    registry = value["cargo_registry_identity"]
    _require_exact_fields(
        registry,
        {
            "schema",
            "root_sha256",
            "file_count",
            "total_bytes",
            "components",
            "maximum_files",
            "maximum_total_bytes",
            "maximum_file_bytes",
        },
        "runner Cargo registry identity",
    )
    _require_equal(
        registry["schema"],
        CARGO_REGISTRY_IDENTITY_SCHEMA,
        "runner Cargo registry schema",
    )
    _require_hex(registry["root_sha256"], 64, "runner Cargo registry root")
    _require_bounded_positive_int(
        registry["file_count"],
        MAX_CARGO_REGISTRY_FILES,
        "runner Cargo registry file count",
    )
    _require_bounded_positive_int(
        registry["total_bytes"],
        MAX_CARGO_REGISTRY_BYTES,
        "runner Cargo registry bytes",
    )
    _require_equal(
        registry["components"],
        ["cache", "index", "src"],
        "runner Cargo registry components",
    )
    for field, expected in (
        ("maximum_files", MAX_CARGO_REGISTRY_FILES),
        ("maximum_total_bytes", MAX_CARGO_REGISTRY_BYTES),
        ("maximum_file_bytes", MAX_CARGO_REGISTRY_FILE_BYTES),
    ):
        _require_equal(registry[field], expected, f"runner Cargo registry {field}")

    _require_exact_fields(
        value["resource_policy"],
        set(RUNNER_RESOURCE_POLICY),
        "runner resource policy",
    )
    _require_equal(
        value["resource_policy"],
        RUNNER_RESOURCE_POLICY,
        "runner resource policy",
    )
    _require_equal(
        value["same_uid_resistance"],
        False,
        "runner same-UID resistance non-claim",
    )
    _require_equal(
        value["complete_build_input_closure_verified"],
        False,
        "runner complete build-input closure non-claim",
    )
    return json.loads(canonical_bytes(value))


def _validate_plan(plan: dict[str, Any]) -> None:
    expected = build_plan(plan.get("source_commit", ""), plan.get("host_run_root", ""))
    if plan != expected:
        raise RebuildPlanError("rebuild plan differs from the deterministic plan")


def _check_stage_observations(
    value: Any, expected_source_tree_root: str
) -> list[dict[str, Any]]:
    if type(value) is not list or len(value) != len(STAGES):
        raise RebuildPlanError("observations must contain exactly six ordered stages")
    programs: list[dict[str, Any]] = []
    for spec, row in zip(STAGES, value, strict=True):
        _check_stage_row(spec, row, programs, expected_source_tree_root)
        programs.append(row["program"])
    return programs


def _check_stage_row(
    spec: StageSpec,
    row: Any,
    preceding_programs: list[dict[str, Any]],
    expected_source_tree_root: str,
) -> None:
    _require_exact_fields(
        row,
        {
            "stage_id",
            "ordinal",
            "source_snapshot_root_sha256",
            "source_tree_root_sha256",
            "canonical_source_root",
            "target_was_absent",
            "output_was_absent",
            "network_disabled",
            "cargo_locked",
            "cargo_offline",
            "build_jobs",
            "build_cpus",
            "build_memory_bytes",
            "program",
            "companion_host_binary",
            "child_pin",
            "repins",
        },
        f"stage {spec.stage_id}",
    )
    _require_equal(row["stage_id"], spec.stage_id, "stage ID")
    _require_equal(row["ordinal"], spec.ordinal, "stage ordinal")
    _require_hex(row["source_snapshot_root_sha256"], 64, "source snapshot root")
    _check_build_facts(row)
    program = _check_program(row["program"], spec.artifact_file)
    _check_stage_companion(spec, row["companion_host_binary"])
    _check_child_pin(spec, row["child_pin"], preceding_programs)
    source_tree_root = row["source_tree_root_sha256"]
    if spec.stage_id == "source_spot":
        _require_hex(source_tree_root, 64, "source tree root")
        _require_equal(
            source_tree_root,
            expected_source_tree_root,
            "source tree root",
        )
    elif source_tree_root is not None:
        raise RebuildPlanError("only source_spot may report a source tree root")
    _check_repins(spec, row["repins"], program, source_tree_root)


def _check_stage_companion(spec: StageSpec, value: Any) -> None:
    if spec.stage_id != "source_spot":
        if value is not None:
            raise RebuildPlanError("only source_spot may report a companion host binary")
        return
    _require_exact_fields(
        value,
        {"binary_file", "binary_bytes", "binary_sha256"},
        "source Spot companion CLI",
    )
    _require_equal(value["binary_file"], "tau-state-proof-risc0-cli", "source CLI file")
    size = value["binary_bytes"]
    if type(size) is not int or not 0 < size <= MAX_HOST_BINARY_BYTES:
        raise RebuildPlanError("source CLI binary byte length is outside the bound")
    _require_hex(value["binary_sha256"], 64, "source CLI SHA-256")


def _check_build_facts(row: dict[str, Any]) -> None:
    expected = {
        "canonical_source_root": CANONICAL_SOURCE_ROOT,
        "target_was_absent": True,
        "output_was_absent": True,
        "network_disabled": True,
        "cargo_locked": True,
        "cargo_offline": True,
        "build_jobs": BUILD_JOBS,
        "build_cpus": BUILD_CPUS,
        "build_memory_bytes": BUILD_MEMORY_BYTES,
    }
    for field, wanted in expected.items():
        _require_equal(row[field], wanted, f"build fact {field}")


def _check_program(value: Any, expected_file: str) -> dict[str, Any]:
    _require_exact_fields(
        value,
        {
            "artifact_file",
            "program_binary_bytes",
            "program_binary_sha256",
            "image_id",
            "image_id_words",
        },
        "program",
    )
    _require_equal(value["artifact_file"], expected_file, "artifact file")
    size = value["program_binary_bytes"]
    if type(size) is not int or not 4 < size <= MAX_PROGRAM_BINARY_BYTES:
        raise RebuildPlanError("program binary byte length is outside the bound")
    _require_hex(value["program_binary_sha256"], 64, "program binary SHA-256")
    _require_hex(value["image_id"], 64, "program image ID")
    words = value["image_id_words"]
    if (
        type(words) is not list
        or len(words) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFFFFFF for word in words)
    ):
        raise RebuildPlanError("program image words must contain exactly eight u32 values")
    if b"".join(word.to_bytes(4, "little") for word in words).hex() != value["image_id"]:
        raise RebuildPlanError("program image words do not encode the image ID")
    return value


def _check_child_pin(
    spec: StageSpec, value: Any, preceding_programs: list[dict[str, Any]]
) -> None:
    if spec.predecessor_stage is None:
        if value is not None:
            raise RebuildPlanError("source_spot must not declare a child pin")
        return
    _require_exact_fields(
        value,
        {"stage_id", "image_id", "program_binary_sha256"},
        f"{spec.stage_id} child pin",
    )
    predecessor = STAGES[spec.ordinal - 2]
    expected_program = preceding_programs[-1]
    _require_equal(value["stage_id"], predecessor.stage_id, "child stage ID")
    _require_equal(value["image_id"], expected_program["image_id"], "child image ID")
    _require_equal(
        value["program_binary_sha256"],
        expected_program["program_binary_sha256"],
        "child program binary SHA-256",
    )


def _check_repins(
    spec: StageSpec,
    value: Any,
    program: dict[str, Any],
    source_tree_root: str | None,
) -> None:
    if type(value) is not list or len(value) != len(spec.repins):
        raise RebuildPlanError(f"{spec.stage_id} repin inventory mismatch")
    for expected, observed in zip(spec.repins, value, strict=True):
        _require_exact_fields(
            observed,
            {"path", "symbol", "value_kind", "visibility", "value"},
            f"{spec.stage_id} repin",
        )
        for field in ("path", "symbol", "value_kind", "visibility"):
            _require_equal(observed[field], getattr(expected, field), f"repin {field}")
        expected_value = _repin_value(expected.value_kind, program, source_tree_root)
        _require_equal(observed["value"], expected_value, f"repin value {expected.symbol}")


def _repin_value(
    value_kind: str, program: dict[str, Any], source_tree_root: str | None
) -> list[int]:
    if value_kind == "image_id_words_le":
        return program["image_id_words"]
    if value_kind == "sha256_bytes":
        return list(bytes.fromhex(program["program_binary_sha256"]))
    if value_kind == "source_closure_root_bytes" and source_tree_root is not None:
        return list(bytes.fromhex(source_tree_root))
    raise RebuildPlanError("unsupported or incomplete repin value")


def _check_settlement_two_pass(value: Any, settlement: dict[str, Any]) -> None:
    _require_exact_fields(
        value,
        {
            "host_only_policy_path",
            "host_only_policy_symbol",
            "settlement_guest_depends_on_host_only_policy",
            "second_pass_source_snapshot_root_sha256",
            "second_pass_program",
        },
        "settlement two-pass observation",
    )
    repin = STAGES[-1].repins[0]
    _require_equal(value["host_only_policy_path"], repin.path, "host-only policy path")
    _require_equal(value["host_only_policy_symbol"], repin.symbol, "host-only policy symbol")
    _require_equal(
        value["settlement_guest_depends_on_host_only_policy"],
        False,
        "settlement guest host-only dependency",
    )
    _require_hex(
        value["second_pass_source_snapshot_root_sha256"],
        64,
        "second-pass source snapshot root",
    )
    second = _check_program(value["second_pass_program"], STAGES[-1].artifact_file)
    _require_equal(second, settlement, "settlement two-pass program identity")


def _check_final_clean_rebuild(
    value: Any, primary_programs: list[dict[str, Any]]
) -> str:
    _require_exact_fields(
        value,
        {
            "final_source_snapshot_root_sha256",
            "canonical_source_root",
            "network_disabled",
            "cargo_locked",
            "cargo_offline",
            "fresh_target_per_stage",
            "fresh_output_per_stage",
            "programs",
        },
        "final clean rebuild",
    )
    root = value["final_source_snapshot_root_sha256"]
    _require_hex(root, 64, "final source snapshot root")
    expected_facts = {
        "canonical_source_root": CANONICAL_SOURCE_ROOT,
        "network_disabled": True,
        "cargo_locked": True,
        "cargo_offline": True,
        "fresh_target_per_stage": True,
        "fresh_output_per_stage": True,
    }
    for field, expected in expected_facts.items():
        _require_equal(value[field], expected, f"final rebuild {field}")
    programs = value["programs"]
    if type(programs) is not list or len(programs) != len(STAGES):
        raise RebuildPlanError("final rebuild must contain exactly six programs")
    for spec, observed, primary in zip(STAGES, programs, primary_programs, strict=True):
        checked = _check_program(observed, spec.artifact_file)
        _require_equal(checked, primary, f"final rebuild identity for {spec.stage_id}")
    return root


def _check_host_verifier(value: Any, settlement: dict[str, Any]) -> dict[str, Any]:
    _require_exact_fields(
        value,
        {
            "source_snapshot_root_sha256",
            "expected_settlement_image_id",
            "binary_file",
            "binary_bytes",
            "binary_sha256",
            "canonical_source_root",
            "target_was_absent",
            "cargo_locked",
            "cargo_offline",
            "network_disabled",
        },
        "host verifier",
    )
    _require_hex(value["source_snapshot_root_sha256"], 64, "host verifier source root")
    _require_equal(
        value["expected_settlement_image_id"], settlement["image_id"], "host settlement ID"
    )
    _require_equal(
        value["binary_file"],
        "source-opened-spot-settlement-verifier-v6",
        "host verifier binary",
    )
    size = value["binary_bytes"]
    if type(size) is not int or not 0 < size <= MAX_HOST_BINARY_BYTES:
        raise RebuildPlanError("host verifier binary byte length is outside the bound")
    _require_hex(value["binary_sha256"], 64, "host verifier SHA-256")
    expected_facts = {
        "canonical_source_root": CANONICAL_SOURCE_ROOT,
        "target_was_absent": True,
        "cargo_locked": True,
        "cargo_offline": True,
        "network_disabled": True,
    }
    for field, expected in expected_facts.items():
        _require_equal(value[field], expected, f"host verifier {field}")
    return {
        "binary_file": value["binary_file"],
        "binary_bytes": size,
        "binary_sha256": value["binary_sha256"],
        "expected_settlement_image_id": value["expected_settlement_image_id"],
    }


def _candidate_report(
    plan: dict[str, Any],
    programs: list[dict[str, Any]],
    source_cli: dict[str, Any],
    final_root: str,
    host_binary: dict[str, Any],
    runner_security_posture: dict[str, Any],
    observations_sha256: str,
    governance_candidates: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "status": "candidate_repin_chain_observations_validated",
        "source_commit": plan["source_commit"],
        "plan_sha256": canonical_sha256(plan),
        "observations_sha256": observations_sha256,
        "canonical_in_sandbox_source_root": CANONICAL_SOURCE_ROOT,
        "toolchain": dict(TOOLCHAIN),
        "runner_security_posture": runner_security_posture,
        "tracked_workspace_source_coverage": plan["tracked_workspace_source_coverage"],
        "source_guest_source_coverage": plan["source_guest_source_coverage"],
        "governance_candidates": governance_candidates,
        "programs": [
            {"stage_id": spec.stage_id, **program}
            for spec, program in zip(STAGES, programs, strict=True)
        ],
        "source_spot_cli": dict(source_cli),
        "host_verifier": host_binary,
        "final_source_snapshot_root_sha256": final_root,
        "validated_facts": {
            "acyclic_topology_validated": True,
            "child_pins_match_predecessor_programs": True,
            "exact_program_binary_hashes_and_image_ids_recorded": True,
            "final_clean_rebuild_matches_all_primary_programs": True,
            "fresh_external_target_and_output_reported": True,
            "locked_offline_builds_reported": True,
            "network_disabled_builds_reported": True,
            "runner_tools_registry_and_resource_policy_recorded": True,
            "settlement_host_only_two_pass_match": True,
            "source_anchor_matches_source_guest_inventory": True,
        },
        "required_governance_updates_after_candidate": list(REQUIRED_GOVERNANCE_UPDATES),
        "protected_historical_artifacts": list(PROTECTED_HISTORICAL_ARTIFACTS),
        "authority": {field: False for field in AUTHORITY_FLAGS},
        "non_claims": list(NON_CLAIMS),
    }


def _build_governance_candidates(
    plan: dict[str, Any],
    source_stage: dict[str, Any],
    adapter_stage: dict[str, Any],
) -> dict[str, Any]:
    anchor = build_current_source_anchor_candidate(plan, source_stage)
    policy = build_v2_adapter_source_policy_candidate(
        plan,
        source_stage,
        adapter_stage,
        anchor,
    )
    return {
        "current_source_anchor_v2": {
            "path": "config/proof_profiles/zrpf_current_source_anchor_v2.json",
            "canonical_sha256": canonical_sha256(anchor),
            "document": anchor,
        },
        "v2_adapter_source_policy": {
            "path": "config/proof_profiles/zrpf_v2_leaf_adapter_source_policy_v2.json",
            "canonical_sha256": canonical_sha256(policy),
            "document": policy,
        },
        "authority": {field: False for field in AUTHORITY_FLAGS},
    }


def build_current_source_anchor_candidate(
    plan: dict[str, Any],
    source_stage: dict[str, Any],
) -> dict[str, Any]:
    """Return the exact authority-neutral V2 source-anchor candidate."""

    source_program = source_stage["program"]
    source_coverage = plan["source_guest_source_coverage"]
    return {
        "schema": "zenodex/zrpf_current_source_anchor/v2",
        "status": "observed_unpromoted_candidate",
        "observation_binding": {
            "plan_schema": PLAN_SCHEMA,
            "plan_sha256": canonical_sha256(plan),
            "source_commit": plan["source_commit"],
            "stage_id": "source_spot",
            "source_snapshot_root_sha256": source_stage[
                "source_snapshot_root_sha256"
            ],
        },
        "source_closure": {
            "kind": "tracked_state_proof_workspace_superset_v1",
            "workspace_roots": list(SOURCE_GUEST_WORKSPACE_ROOTS),
            "inventory_root_sha256": source_coverage["inventory_root_sha256"],
            "tracked_file_count": source_coverage["tracked_file_count"],
            "tracked_bytes": source_coverage["tracked_bytes"],
            "complete_build_input_closure_verified": False,
        },
        "spot_program": {
            "image_id": source_program["image_id"],
            "image_id_words": source_program["image_id_words"],
            "program_sha256": source_program["program_binary_sha256"],
        },
        "release_authority": False,
        "production_authority": False,
        "non_claims": [
            "source_build_observation_is_candidate_only",
            "no_complete_build_input_closure",
            "no_release_authority",
            "no_production_authority",
            "does_not_replace_receipt_verification",
        ],
    }


def build_v2_adapter_source_policy_candidate(
    plan: dict[str, Any],
    source_stage: dict[str, Any],
    adapter_stage: dict[str, Any],
    anchor: dict[str, Any],
) -> dict[str, Any]:
    """Return the exact authority-neutral V2 adapter-policy candidate."""

    source_program = source_stage["program"]
    adapter_program = adapter_stage["program"]
    source_coverage = plan["source_guest_source_coverage"]
    return {
        "schema": "zenodex/zrpf_v2_leaf_adapter_source_policy/v2",
        "status": "observed_unpromoted_candidate",
        "adapter_profile": "zrpf_v2_leaf_adapter_compatibility_v2",
        "count_unit": "source_transition_receipt",
        "source_reference": {
            "path": "config/proof_profiles/zrpf_current_source_anchor_v2.json",
            "schema": anchor["schema"],
            "sha256": canonical_sha256(anchor),
        },
        "sources": [
            {
                "source_kind": "spot",
                "proof_type": "risc0.zenodex_recursive_spot_leaf.v1",
                "proof_profile": "recursive_spot_leaf_v1",
                "lane_kind": "spot",
                "image_id": source_program["image_id"],
                "image_id_words": source_program["image_id_words"],
                "program_sha256": source_program["program_binary_sha256"],
                "source_closure_root": source_coverage["inventory_root_sha256"],
            }
        ],
        "adapter_program": {
            "image_id": adapter_program["image_id"],
            "image_id_words": adapter_program["image_id_words"],
            "program_sha256": adapter_program["program_binary_sha256"],
        },
        "receipt_authority": False,
        "release_authority": False,
        "production_authority": False,
        "unsupported_compatibility_fields": [
            "data_availability_certificate_root",
            "carry_queue_pre_root",
            "carry_queue_post_root",
        ],
        "non_claims": [
            "pure_mapping_does_not_authenticate_receipts",
            "candidate_adapter_identity_is_unpromoted",
            "no_durable_data_availability",
            "no_carry_queue_evidence",
            "no_settlement_or_ledger_admission_authority",
            "no_release_or_production_authority",
        ],
    }


def _validate_static_topology() -> None:
    if len(set(TOPOLOGY_NODES)) != len(TOPOLOGY_NODES):
        raise RebuildPlanError("topology nodes must be unique")
    positions = {node: index for index, node in enumerate(TOPOLOGY_NODES)}
    for source, destination in TOPOLOGY_EDGES:
        if source not in positions or destination not in positions:
            raise RebuildPlanError("topology edge references an unknown node")
        if positions[source] >= positions[destination]:
            raise RebuildPlanError("topology contains a backward or cyclic edge")
    if tuple(spec.ordinal for spec in STAGES) != tuple(range(1, len(STAGES) + 1)):
        raise RebuildPlanError("stage ordinals must be dense")
    for index, spec in enumerate(STAGES):
        expected = None if index == 0 else STAGES[index - 1].stage_id
        if spec.predecessor_stage != expected:
            raise RebuildPlanError("stage predecessor chain is not linear and acyclic")
    if STAGES[-1].repins[0].visibility != "host_only":
        raise RebuildPlanError("settlement self identity must remain host-only")
    repin_paths = {repin.path for stage in STAGES for repin in stage.repins}
    historical_overlap = repin_paths.intersection(PROTECTED_HISTORICAL_ARTIFACTS)
    if historical_overlap:
        raise RebuildPlanError("repin plan attempts to mutate a historical artifact")


def audit_tracked_workspace_source(
    repo_root: Path,
    source_commit: str,
) -> dict[str, Any]:
    """Bind every tracked file under the three compiler-relevant workspaces.

    This deliberately includes files beyond the derived Cargo dependency graph.
    The conservative superset prevents a newly added compiler-visible file from
    silently falling outside the candidate snapshot.  It remains a repository
    source inventory, not a complete build-input closure.
    """

    files = _tracked_files_for_roots(
        repo_root,
        source_commit,
        RELEVANT_WORKSPACE_ROOTS,
    )
    parallel = sorted(
        path
        for path, _mode, _size, _sha256 in files
        if path.startswith("zk/zrpf_protocol/protocol/src/parallel_shard_epoch_v1/")
        and path.endswith(".rs")
    )
    if not parallel:
        raise RebuildPlanError(
            "parallel_shard_epoch_v1 tracked Rust sources are absent from the inventory"
        )
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.zrpf.spot_v6.tracked_workspace_source.v1\0")
    total = 0
    for path, mode, size, sha256 in files:
        encoded = path.encode("utf-8")
        encoded_mode = mode.encode("ascii")
        total += size
        hasher.update(len(encoded).to_bytes(4, "big"))
        hasher.update(encoded)
        hasher.update(len(encoded_mode).to_bytes(1, "big"))
        hasher.update(encoded_mode)
        hasher.update(size.to_bytes(8, "big"))
        hasher.update(bytes.fromhex(sha256))
    return {
        "workspace_roots": list(RELEVANT_WORKSPACE_ROOTS),
        "tracked_file_count": len(files),
        "tracked_bytes": total,
        "inventory_root_sha256": hasher.hexdigest(),
        "all_tracked_workspace_files_included": True,
        "tracked_file_modes_included": True,
        "explicitly_excluded_tracked_files": [],
        "parallel_shard_epoch_v1_files": parallel,
        "complete_build_input_closure_verified": False,
    }


def audit_source_guest_workspace(
    repo_root: Path,
    source_commit: str,
) -> dict[str, Any]:
    """Bind the source program workspace without any ZRPF policy input.

    The current-source policy commits this acyclic source-specific superset.
    The broader three-workspace inventory remains a separate repository
    observation and must never be repinned into a guest that belongs to it.
    """

    files = _tracked_files_for_roots(
        repo_root,
        source_commit,
        SOURCE_GUEST_WORKSPACE_ROOTS,
    )
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.zrpf.current_spot.source_workspace.v2\0")
    total = 0
    for path, mode, size, sha256 in files:
        encoded = path.encode("utf-8")
        encoded_mode = mode.encode("ascii")
        total += size
        hasher.update(len(encoded).to_bytes(4, "big"))
        hasher.update(encoded)
        hasher.update(len(encoded_mode).to_bytes(1, "big"))
        hasher.update(encoded_mode)
        hasher.update(size.to_bytes(8, "big"))
        hasher.update(bytes.fromhex(sha256))
    return {
        "kind": "tracked_state_proof_workspace_superset_v1",
        "workspace_roots": list(SOURCE_GUEST_WORKSPACE_ROOTS),
        "tracked_file_count": len(files),
        "tracked_bytes": total,
        "inventory_root_sha256": hasher.hexdigest(),
        "all_tracked_workspace_files_included": True,
        "tracked_file_modes_included": True,
        "explicitly_excluded_tracked_files": [],
        "excludes_zrpf_policy_and_adapter_sources": all(
            not path.startswith("zk/zrpf_risc0/") for path, _mode, _size, _sha256 in files
        ),
        "complete_build_input_closure_verified": False,
    }


def _tracked_files_for_roots(
    repo_root: Path,
    source_commit: str,
    workspace_roots: tuple[str, ...],
) -> list[tuple[str, str, int, str]]:
    _require_hex(source_commit, 40, "source commit")
    root = repo_root.resolve(strict=True)
    completed = _run_git(
        root,
        ["ls-tree", "-r", "-z", source_commit, "--", *workspace_roots],
        maximum_stdout=8 * 1024 * 1024,
    )
    entries = _parse_ls_tree(completed.stdout)
    if not entries or len(entries) > MAX_TRACKED_SOURCE_FILES:
        raise RebuildPlanError("tracked workspace source inventory exceeds its file bound")
    return _git_blob_sha256_inventory(root, entries)


def _run_git(
    root: Path,
    arguments: list[str],
    *,
    input_bytes: bytes | None = None,
    maximum_stdout: int,
) -> subprocess.CompletedProcess[bytes]:
    environment = {
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "HOME": "/nonexistent",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    try:
        completed = subprocess.run(
            ["/usr/bin/git", "-C", str(root), *arguments],
            input=input_bytes,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise RebuildPlanError("bounded Git source inventory failed") from exc
    if completed.returncode != 0 or completed.stderr:
        raise RebuildPlanError("bounded Git source inventory rejected")
    if len(completed.stdout) > maximum_stdout:
        raise RebuildPlanError("bounded Git source inventory output exceeds its cap")
    return completed


def _parse_ls_tree(raw: bytes) -> list[tuple[str, str, str]]:
    if raw and not raw.endswith(b"\0"):
        raise RebuildPlanError("Git source inventory framing is invalid")
    entries: list[tuple[str, str, str]] = []
    for item in raw.split(b"\0"):
        if not item:
            continue
        try:
            header, path_raw = item.split(b"\t", 1)
            mode, kind, object_id = header.split(b" ", 2)
            path = path_raw.decode("utf-8", errors="strict")
        except (ValueError, UnicodeDecodeError) as exc:
            raise RebuildPlanError("Git source inventory entry is malformed") from exc
        if mode not in {b"100644", b"100755"} or kind != b"blob":
            raise RebuildPlanError("tracked workspace source contains a non-regular entry")
        if re.fullmatch(rb"[0-9a-f]{40,64}", object_id) is None:
            raise RebuildPlanError("Git source inventory object ID is invalid")
        pure = PurePosixPath(path)
        if (
            pure.is_absolute()
            or ".." in pure.parts
            or pure.as_posix() != path
            or any(ord(character) < 32 or ord(character) == 127 for character in path)
        ):
            raise RebuildPlanError("Git source inventory path is invalid")
        entries.append((path, mode.decode("ascii"), object_id.decode("ascii")))
    if len(entries) != len({path for path, _mode, _object_id in entries}):
        raise RebuildPlanError("Git source inventory contains duplicate paths")
    return sorted(entries)


def _git_blob_sha256_inventory(
    root: Path,
    entries: list[tuple[str, str, str]],
) -> list[tuple[str, str, int, str]]:
    request = b"".join(f"{object_id}\n".encode("ascii") for _, _, object_id in entries)
    completed = _run_git(
        root,
        ["cat-file", "--batch"],
        input_bytes=request,
        maximum_stdout=MAX_TRACKED_SOURCE_BYTES + len(entries) * 128,
    )
    output = completed.stdout
    cursor = 0
    total = 0
    results: list[tuple[str, str, int, str]] = []
    for path, mode, object_id in entries:
        line_end = output.find(b"\n", cursor)
        if line_end < 0:
            raise RebuildPlanError("Git source blob header is unavailable")
        header = output[cursor:line_end].split()
        cursor = line_end + 1
        if (
            len(header) != 3
            or header[0] != object_id.encode("ascii")
            or header[1] != b"blob"
            or not header[2].isdigit()
        ):
            raise RebuildPlanError("Git source object is not a blob")
        size = int(header[2])
        end = cursor + size
        total += size
        if (
            size < 0
            or total > MAX_TRACKED_SOURCE_BYTES
            or end >= len(output)
            or output[end : end + 1] != b"\n"
        ):
            raise RebuildPlanError("Git source blob framing exceeds its bound")
        raw = output[cursor:end]
        results.append((path, mode, size, hashlib.sha256(raw).hexdigest()))
        cursor = end + 1
    if cursor != len(output):
        raise RebuildPlanError("Git source blob batch has trailing bytes")
    return results


def _require_exact_fields(value: Any, expected: set[str], label: str) -> None:
    if type(value) is not dict:
        raise RebuildPlanError(f"{label} must be an object")
    actual = set(value)
    if actual != expected:
        missing = ",".join(sorted(expected - actual)) or "none"
        extra = ",".join(sorted(actual - expected)) or "none"
        raise RebuildPlanError(f"{label} fields mismatch; missing={missing}; extra={extra}")


def _require_equal(actual: Any, expected: Any, label: str) -> None:
    if type(actual) is not type(expected) or actual != expected:
        raise RebuildPlanError(f"{label} mismatch")


def _require_hex(value: Any, length: int, label: str) -> None:
    if type(value) is not str or re.fullmatch(rf"[0-9a-f]{{{length}}}", value) is None:
        raise RebuildPlanError(f"{label} must be {length} lowercase hexadecimal characters")


def _require_bounded_positive_int(value: Any, maximum: int, label: str) -> None:
    if type(value) is not int or not 0 < value <= maximum:
        raise RebuildPlanError(f"{label} is outside its positive bound")


def _require_absolute_path(value: Any, label: str) -> None:
    if type(value) is not str or not value.startswith("/") or "\x00" in value:
        raise RebuildPlanError(f"{label} must be an absolute path")
    path = PurePosixPath(value)
    if path.as_posix() != value or ".." in path.parts:
        raise RebuildPlanError(f"{label} must be a normalized absolute path")


def _reject_float(_value: str) -> NoReturn:
    raise RebuildPlanError("floating-point JSON values are forbidden")


def _bounded_int(value: str) -> int:
    digits = value[1:] if value.startswith("-") else value
    if not digits or len(digits) > MAX_JSON_INTEGER_DIGITS:
        raise RebuildPlanError("JSON integer exceeds the digit bound")
    return int(value, 10)


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RebuildPlanError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _validate_json_shape(document: Any) -> None:
    nodes = 0
    pending = [(document, 1)]
    while pending:
        value, depth = pending.pop()
        nodes += 1
        if nodes > MAX_JSON_NODES or depth > MAX_JSON_DEPTH:
            raise RebuildPlanError("JSON structure exceeds its bound")
        if type(value) is str:
            if len(value) > MAX_JSON_STRING_CHARS:
                raise RebuildPlanError("JSON string exceeds its bound")
        elif type(value) is dict:
            pending.extend((child, depth + 1) for child in value.values())
        elif type(value) is list:
            pending.extend((child, depth + 1) for child in value)
        elif type(value) not in {bool, int, type(None)}:
            raise RebuildPlanError("JSON contains an unsupported value")


def load_canonical_json(path: Path, label: str) -> dict[str, Any]:
    raw = _read_bounded_regular(path, label, MAX_JSON_BYTES)
    try:
        document = json.loads(
            raw.decode("utf-8", errors="strict"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
            parse_int=_bounded_int,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RebuildPlanError(f"{label} JSON rejected") from exc
    _validate_json_shape(document)
    if type(document) is not dict:
        raise RebuildPlanError(f"{label} root must be an object")
    if raw != canonical_bytes(document):
        raise RebuildPlanError(f"{label} must use canonical JSON bytes")
    return document


def _read_bounded_regular(path: Path, label: str, maximum: int) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise RebuildPlanError(f"{label} is unavailable") from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or not 0 < before.st_size <= maximum:
            raise RebuildPlanError(f"{label} is not a bounded regular file")
        raw = b""
        while len(raw) <= maximum:
            chunk = os.read(descriptor, min(1 << 20, maximum + 1 - len(raw)))
            if not chunk:
                break
            raw += chunk
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if len(raw) > maximum:
        raise RebuildPlanError(f"{label} exceeds its byte bound")
    stable = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
    if stable != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns):
        raise RebuildPlanError(f"{label} changed during read")
    return raw


def _validate_run_root(path: Path) -> str:
    if not path.is_absolute() or path.exists() or path.is_symlink():
        raise RebuildPlanError("run root must be an absent absolute path")
    try:
        parent = path.parent.resolve(strict=True)
        repository = REPO_ROOT.resolve(strict=True)
    except OSError as exc:
        raise RebuildPlanError("run root parent is unavailable") from exc
    candidate = parent / path.name
    if candidate != path:
        raise RebuildPlanError("run root must be canonical")
    if candidate == repository or repository in candidate.parents:
        raise RebuildPlanError("run root must be external to the repository")
    return candidate.as_posix()


def _write_new_external(path: Path, raw: bytes) -> None:
    if not path.is_absolute() or path.exists() or path.is_symlink():
        raise RebuildPlanError("output must be an absent absolute path")
    repository = REPO_ROOT.resolve(strict=True)
    parent = path.parent.resolve(strict=True)
    candidate = parent / path.name
    if candidate != path or candidate == repository or repository in candidate.parents:
        raise RebuildPlanError("output must be canonical and external to the repository")
    descriptor = os.open(candidate, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        candidate.unlink(missing_ok=True)
        raise
    finally:
        os.close(descriptor)


def _emit(document: dict[str, Any], output: Path | None) -> None:
    raw = canonical_bytes(document)
    if output is None:
        sys.stdout.buffer.write(raw)
    else:
        _write_new_external(output, raw)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    plan = subparsers.add_parser("plan")
    plan.add_argument("--source-commit", required=True)
    plan.add_argument("--run-root", type=Path, required=True)
    plan.add_argument("--output", type=Path)
    check = subparsers.add_parser("check")
    check.add_argument("--plan", type=Path, required=True)
    check.add_argument("--observations", type=Path, required=True)
    check.add_argument("--output", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.command == "plan":
            run_root = _validate_run_root(args.run_root)
            document = build_plan(args.source_commit, run_root)
        else:
            plan = load_canonical_json(args.plan, "rebuild plan")
            observations = load_canonical_json(args.observations, "observations")
            document = check_observations(plan, observations)
        _emit(document, args.output)
    except (OSError, RebuildPlanError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
