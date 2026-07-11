"""Canonical evidence-document construction for retained ZRPF V3 replay."""

from __future__ import annotations

import importlib
from pathlib import Path
from typing import Any

_MODULE_PREFIX = "tools." if __package__ else ""
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")


def expected_evidence(repo_root: Path) -> dict[str, Any]:
    return {
        "claims": _claims(),
        "evidence_date": "2026-07-10",
        "non_claims": list(support.NON_CLAIMS),
        "recorded_build": _recorded_build(),
        "recorded_execution": _recorded_execution(),
        "replay_source_closure": support.source_closure(repo_root),
        "retained_receipt_set": support.retained_receipt_set(
            repo_root / support.RECEIPT_DIRECTORY.relative_to(support.REPO_ROOT)
        ),
        "sanitization": {
            "absolute_paths_in_record": False,
            "guest_binaries_in_evidence_directory": False,
            "native_verifier_binary_in_evidence_directory": False,
            "receipt_directory_contains_only_exact_receipts": True,
        },
        "schema": support.SCHEMA,
        "scope": "same_host_current_source_host_verifier_replay_of_exact_retained_v3_receipt_bytes",
        "source_anchor": {
            "commit": support.SOURCE_COMMIT,
            "tree": support.SOURCE_TREE,
        },
        "stale_evidence_disposition": {
            "historical_root_receipt_sha256_record_preserved": "021af13025e7dc7c40e06d689ad30e3194e58793435cd11ae07d684c80ddfd33",
            "historical_source_closures_refreshed": False,
            "new_retained_root_receipt": support.ROOT_RECEIPT_SHA256,
            "same_authenticated_root_journal": support.ROOT_JOURNAL_HASH,
        },
        "status": "same_host_source_built_host_verifier_exact_retained_receipts_replayed",
        "verified_tree": _verified_tree(),
        "version": 1,
    }


def _claims() -> dict[str, bool]:
    claims = {name: True for name in sorted(support.TRUE_CLAIMS)}
    claims.update({name: False for name in sorted(support.FALSE_CLAIMS)})
    return claims


def _recorded_build() -> dict[str, Any]:
    return {
        "cargo_home_config_isolated": True,
        "cargo_offline_mode_enforced": True,
        "cargo_version": "cargo 1.94.1-dev (29ea6fb6a 2026-03-24)",
        "command": "cargo build --frozen --release -p zenodex-zrpf-risc0-replay-verifier",
        "dependency_graph_edges": "normal,build,no-proc-macro",
        "external_target_directory": True,
        "parent_environment_allowlisted": True,
        "private_source_snapshot": True,
        "risc0_default_features": False,
        "risc0_features": ["disable-dev-mode", "std"],
        "rustc_version": "rustc 1.94.1-dev (06e01cb0d 2026-04-09)",
        "rustdoc_version": "rustdoc 1.94.1-dev (06e01cb0d 2026-04-09)",
        "selected_graph_forbidden_packages_absent": True,
        "source_closure_checked_before_and_after_build": True,
        "source_snapshot_commit": support.SOURCE_COMMIT,
        "source_snapshot_tree": support.SOURCE_TREE,
        "toolchain_lock_path": support.TOOLCHAIN_LOCK_PATH,
    }


def _recorded_execution() -> dict[str, Any]:
    return {
        "negative_controls": _negative_controls(),
        "normal_and_risc0_dev_mode_one_stdout_identical": True,
        "stderr_sha256": support.EMPTY_SHA256,
        "stderr_size_bytes": 0,
        "stdout_sha256": support.EXPECTED_STDOUT_SHA256,
        "stdout_size_bytes": support.EXPECTED_STDOUT_SIZE,
    }


def _negative_controls() -> list[dict[str, str]]:
    return [
        _negative("altered_leaf", support.RECEIPTS[0][0], "receipt_artifact_binding"),
        _negative("swapped_l1", support.RECEIPTS[4][0], "receipt_artifact_binding"),
        _negative("extra_inventory", "replay", "bundle_inventory"),
        _negative("missing_inventory", "replay", "bundle_inventory"),
        _negative("receipt_symlink", support.RECEIPTS[0][0], "receipt_artifact"),
        _negative("receipt_fifo", support.RECEIPTS[0][0], "receipt_artifact"),
        _negative("directory_symlink", "replay", "bundle_directory"),
        _negative("no_arguments", "replay", "usage"),
    ]


def _negative(case_id: str, context: str, error_code: str) -> dict[str, str]:
    return {"case_id": case_id, "context": context, "error_code": error_code}


def _verified_tree() -> dict[str, str]:
    return {
        "adapter_image_id": support.EXPECTED_REPORT_IMAGES["adapter"],
        "level_one_image_id": support.EXPECTED_REPORT_IMAGES["structural_l1"],
        "level_two_image_id": support.EXPECTED_REPORT_IMAGES["structural_l2"],
        "mutation_receipt_sha256": support.MUTATION_RECEIPT_SHA256,
        "mutation_reject_code": "receipt_verification_failed",
        "operation_count_unit": "source_transition_receipt_v3",
        "root_journal_hash": support.ROOT_JOURNAL_HASH,
        "root_receipt_sha256": support.ROOT_RECEIPT_SHA256,
    }
