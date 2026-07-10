#!/usr/bin/env python3
"""Validate the recursive STARK CBC obligation matrix.

The matrix is an obligation map, not production evidence. This checker fails
closed when the matrix allows production language, omits required critical
obligations, or marks implemented obligations without code and test refs.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
import stat
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

_MODULE_PREFIX = f"{__package__}." if __package__ else ""
recursive_v1_evidence: Any = importlib.import_module(
    f"{_MODULE_PREFIX}check_risc0_recursive_rebuild_evidence"
)
recursive_v2_evidence: Any = importlib.import_module(
    f"{_MODULE_PREFIX}check_risc0_recursive_v2_rebuild_evidence"
)

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MATRIX = REPO_ROOT / "docs" / "research" / "RECURSIVE_STARK_CBC_MATRIX_20260709.json"

MATRIX_SCHEMA = "zenodex/recursive_stark_cbc_matrix/v1"
REPORT_SCHEMA = "zenodex/recursive_stark_cbc_matrix_report/v1"
MAX_MATRIX_BYTES = 1024 * 1024
MAX_REFERENCED_FILE_BYTES = 4 * 1024 * 1024
MAX_REFERENCE_PATH_BYTES = 512

MATRIX_ALLOWED_FIELDS = frozenset(
    {
        "schema",
        "status",
        "updated_at",
        "promotion_boundary",
        "typed_statements",
        "obligations",
    }
)
PROMOTION_BOUNDARY_ALLOWED_FIELDS = frozenset(
    {"public_claim_allowed", "production_ready", "claim_status", "non_claims"}
)
TYPED_STATEMENT_ALLOWED_FIELDS = frozenset(
    {
        "id",
        "status",
        "statement",
        "journal",
        "owner_surface",
        "authority_boundary",
        "required_fields",
    }
)
OBLIGATION_ALLOWED_FIELDS = frozenset(
    {
        "id",
        "title",
        "severity",
        "status",
        "defense_layer",
        "disaster_state",
        "construction_rule",
        "non_claim",
        "code_refs",
        "test_refs",
        "external_commands",
        "next_action",
    }
)
REFERENCE_ALLOWED_FIELDS = frozenset({"path", "symbol"})

REQUIRED_NON_CLAIMS = {
    "no_production_ready_recursive_starks",
    "no_full_zk_execution_for_all_value_moving_surfaces",
    "no_complete_zusd_lifecycle_coverage",
    "no_recursive_data_availability_solution",
    "no_arbitrary_depth_or_general_fanout_recursive_tree",
    "no_promoted_general_multi_leaf_fanout_profile",
    "no_nonempty_receipt_set_recursive_proof_evidence",
    "no_durable_atomic_recursive_admission",
    "no_source_pinned_recursive_release_toolchain",
    "no_cross_host_or_reproducible_recursive_release",
    "no_perps_global_cross_lane_conservation_claim",
    "no_local_smoke_as_production_evidence",
    "no_affected_risc0_1_2_6_evidence",
    "no_risc0_zero_knowledge_privacy_claim",
    "no_whole_build_network_isolation",
    "no_public_recursive_replay",
    "no_separately_governed_recursive_authority_manifest",
    "no_canonical_recursive_outer_envelope",
    "no_v3_semantic_receipt_authenticated_tree",
    "no_release_backed_v3_receipt_authenticated_tree",
    "no_complete_v3_semantic_composition",
    "no_zrpf_16x4_profile",
}
REQUIRED_STATEMENTS = {
    "recursive_epoch_v1",
    "recursive_effect_summary_v1",
    "recursive_spot_leaf_v1",
    "recursive_zusd_leaf_v1",
    "recursive_perps_np_leaf_v1",
    "recursive_node_v2",
    "zrpf_node_v3_structural",
    "zrpf_v1_spot_adapter_receipt_v1",
}
REQUIRED_STATEMENT_FIELDS = {
    "zrpf_node_v3_structural": frozenset(
        {
            "journal_version",
            "task_id",
            "node_kind",
            "node_level",
            "partition",
            "immediate_child_count",
            "leaf_count",
            "operation_count",
            "count_unit_id",
            "subtree_node_count",
            "scope",
            "proof_profile_id",
            "actual_program_id",
            "verifier_id",
            "node_statement_hash",
            "program_manifest_root",
            "commitments",
            "commitments.provenance_root",
            "child_tasks_root",
            "child_claims_root",
            "child_journals_root",
            "child_programs_root",
            "child_profiles_root",
            "child_verifiers_root",
            "immediate_verifier_set_root",
            "child_statements_root",
            "child_manifests_root",
            "child_effects_root",
            "child_provenance_roots",
            "child_data_availability_roots",
        }
    ),
    "zrpf_v1_spot_adapter_receipt_v1": frozenset(
        {
            "schema_version",
            "source_kind",
            "source_journal_bytes",
            "assigned_leaf_ordinal",
            "expected_adapter_image_id",
            "governed_source_image_id",
            "canonical_node_journal_v3",
            "outer_verified_adapter_image_equality",
        }
    ),
}
REQUIRED_OBLIGATION_POLICY = {
    "RS-CBC-001": ("critical", "guarded_transition"),
    "RS-CBC-002": ("critical", "guarded_transition"),
    "RS-CBC-003": ("critical", "guarded_transition"),
    "RS-CBC-004": ("critical", "guarded_transition"),
    "RS-CBC-005": ("critical", "bounded_blast_radius"),
    "RS-CBC-006": ("critical", "guarded_transition"),
    "RS-CBC-007": ("critical", "guarded_transition"),
    "RS-CBC-008": ("critical", "detected_at_commit"),
    "RS-CBC-009": ("critical", "guarded_transition"),
    "RS-CBC-010": ("critical", "unrepresentable"),
    "RS-CBC-011": ("critical", "guarded_transition"),
    "RS-CBC-012": ("critical", "detected_at_commit"),
    "RS-CBC-013": ("high", "unrepresentable"),
    "RS-CBC-014": ("critical", "detected_at_commit"),
    "RS-CBC-015": ("critical", "detected_at_commit"),
    "RS-CBC-016": ("critical", "unrepresentable"),
    "RS-CBC-017": ("critical", "detected_at_commit"),
    "RS-CBC-018": ("critical", "bounded_blast_radius"),
    "RS-CBC-019": ("critical", "guarded_transition"),
    "RS-CBC-020": ("critical", "unrepresentable"),
    "RS-CBC-021": ("critical", "unrepresentable"),
    "RS-CBC-022": ("critical", "guarded_transition"),
    "RS-CBC-023": ("critical", "unrepresentable"),
}
REQUIRED_OBLIGATIONS = frozenset(REQUIRED_OBLIGATION_POLICY)
PINNED_PENDING_OBLIGATIONS = frozenset({"RS-CBC-021", "RS-CBC-023"})
ALLOWED_STATUSES = {"implemented", "implemented_partial", "pending", "deferred_nonclaim"}
ALLOWED_SEVERITIES = {"critical", "high", "medium", "low"}
ALLOWED_DEFENSE_LAYERS = {
    "unrepresentable",
    "guarded_transition",
    "detected_at_commit",
    "bounded_blast_radius",
}
IMPLEMENTED_STATUSES = {"implemented", "implemented_partial"}
PENDING_STATUSES = {"pending", "deferred_nonclaim"}
ACCEPTED_CLAIM_STATUSES = frozenset(
    {
        "v1_v2_current_image_local_recursive_proofs_and_temporary_v3_structural_tree_verified"
    }
)
STALE_CURRENT_IMAGE_NON_CLAIM = "no_current_image_recursive_proof_after_composition_repair"
STALE_V3_TREE_ABSENCE_NON_CLAIM = "no_v3_receipt_authenticated_tree"
SEVERITY_RANK = {"low": 0, "medium": 1, "high": 2, "critical": 3}


class MatrixInputError(ValueError):
    """A malformed, unsafe, or oversized matrix input."""


def validate_matrix(matrix: Any, *, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    matrix_sha256 = _canonical_matrix_sha256(matrix, errors)
    root = _mapping(matrix, "matrix", errors)
    _reject_unknown_fields(root, MATRIX_ALLOWED_FIELDS, "matrix", errors)
    if root.get("schema") != MATRIX_SCHEMA:
        errors.append("schema mismatch")
    if root.get("status") != "critical_code_cbc_obligation_matrix":
        errors.append("status must be critical_code_cbc_obligation_matrix")

    try:
        inspected_root = _canonical_repo_root(repo_root)
    except MatrixInputError as exc:
        inspected_root = None
        errors.append(f"repository root rejected: {exc}")

    promotion = _validate_promotion_boundary(root.get("promotion_boundary"))
    statements = _validate_typed_statements(root.get("typed_statements"), repo_root=inspected_root)
    obligations = _validate_obligations(root.get("obligations"), repo_root=inspected_root)

    if promotion["facts"]["claim_status"] in ACCEPTED_CLAIM_STATUSES:
        obligation_statuses = {item["id"]: item["status"] for item in obligations["items"]}
        if obligation_statuses.get("RS-CBC-014") != "implemented":
            errors.append("post-repair local-proof-verified status requires RS-CBC-014 implemented")
        for obligation_id in ("RS-CBC-016", "RS-CBC-022"):
            if obligation_statuses.get(obligation_id) not in IMPLEMENTED_STATUSES:
                errors.append(
                    "temporary V3 structural-tree-verified status requires "
                    f"{obligation_id} implemented or implemented_partial"
                )
        _validate_promoted_source_closures(inspected_root, errors)

    for section_name, section in (
        ("promotion_boundary", promotion),
        ("typed_statements", statements),
        ("obligations", obligations),
    ):
        if not section["ok"]:
            errors.append(f"{section_name} rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "matrix_sha256": matrix_sha256,
        "facts": {
            "typed_statement_count": statements["facts"]["typed_statement_count"],
            "obligation_count": obligations["facts"]["obligation_count"],
            "implemented_obligation_count": obligations["facts"]["implemented_obligation_count"],
            "pending_obligation_count": obligations["facts"]["pending_obligation_count"],
            "missing_required_statements": statements["facts"]["missing_required_statements"],
            "missing_required_obligations": obligations["facts"]["missing_required_obligations"],
        },
        "promotion_boundary": promotion,
        "typed_statements": statements,
        "obligations": obligations,
    }


def _validate_promoted_source_closures(
    repo_root: Path | None,
    errors: list[str],
) -> None:
    if repo_root is None:
        errors.append("promoted recursive proof source closures cannot be checked")
        return

    try:
        v1_raw = _read_repo_file(
            repo_root,
            _normalized_repo_path("config/proof_profiles/risc0_recursive_rebuild_reference.json"),
            max_bytes=recursive_v1_evidence.MAX_REFERENCE_BYTES,
        )
        v1_reference = recursive_v1_evidence.validate_reference(
            recursive_v1_evidence._parse_json(v1_raw, label="REFERENCE")
        )
        v1_digest = recursive_v1_evidence.reference_canonical_sha256(v1_reference)
        if v1_digest != recursive_v1_evidence.EXPECTED_REFERENCE_CANONICAL_SHA256:
            raise recursive_v1_evidence.EvidenceError(
                "REFERENCE_DIGEST_MISMATCH",
                v1_digest,
            )
        recursive_v1_evidence._check_source_workspace(
            repo_root / "zk/state_proof_risc0",
            v1_reference["source_compile"],
        )
    except (MatrixInputError, recursive_v1_evidence.EvidenceError) as exc:
        errors.append(f"promoted V1 source closure rejected: {exc}")

    try:
        v2_raw = _read_repo_file(
            repo_root,
            _normalized_repo_path(
                "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json"
            ),
            max_bytes=recursive_v2_evidence.MAX_REFERENCE_BYTES,
        )
        v2_reference = recursive_v2_evidence.validate_reference(
            recursive_v2_evidence._parse_json(v2_raw, label="REFERENCE")
        )
        v2_digest = recursive_v2_evidence.reference_canonical_sha256(v2_reference)
        if v2_digest != recursive_v2_evidence.EXPECTED_REFERENCE_CANONICAL_SHA256:
            raise recursive_v2_evidence.EvidenceError(
                "REFERENCE_DIGEST_MISMATCH",
                v2_digest,
            )
        recursive_v2_evidence._check_source(v2_reference, repo_root)
    except (MatrixInputError, recursive_v2_evidence.EvidenceError) as exc:
        errors.append(f"promoted V2 source closure rejected: {exc}")


def _validate_promotion_boundary(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "promotion_boundary", errors)
    _reject_unknown_fields(
        obj,
        PROMOTION_BOUNDARY_ALLOWED_FIELDS,
        "promotion_boundary",
        errors,
    )
    public_claim_allowed = _bool(
        obj.get("public_claim_allowed"),
        "promotion_boundary.public_claim_allowed",
        errors,
    )
    production_ready = _bool(
        obj.get("production_ready"),
        "promotion_boundary.production_ready",
        errors,
    )
    claim_status = _str(
        obj.get("claim_status"),
        "promotion_boundary.claim_status",
        errors,
    )
    non_claims = _str_set(obj.get("non_claims"), "promotion_boundary.non_claims", errors)

    if public_claim_allowed is not False:
        errors.append("promotion_boundary.public_claim_allowed must be false")
    if production_ready is not False:
        errors.append("promotion_boundary.production_ready must be false")
    if claim_status is not None and claim_status not in ACCEPTED_CLAIM_STATUSES:
        errors.append("promotion_boundary.claim_status is not an accepted reviewed status")
    missing_non_claims = sorted(REQUIRED_NON_CLAIMS - non_claims)
    if missing_non_claims:
        errors.append("promotion_boundary.non_claims missing required values")
    if (
        claim_status in ACCEPTED_CLAIM_STATUSES
        and STALE_CURRENT_IMAGE_NON_CLAIM in non_claims
    ):
        errors.append("promotion_boundary.non_claims retains stale current-image proof absence")
    if (
        claim_status in ACCEPTED_CLAIM_STATUSES
        and STALE_V3_TREE_ABSENCE_NON_CLAIM in non_claims
    ):
        errors.append("promotion_boundary.non_claims retains stale V3 structural-tree absence")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "public_claim_allowed": public_claim_allowed,
            "production_ready": production_ready,
            "claim_status": claim_status,
            "missing_required_non_claims": missing_non_claims,
        },
    }


def _validate_typed_statements(value: Any, *, repo_root: Path | None) -> dict[str, Any]:
    errors: list[str] = []
    items = _list(value, "typed_statements", errors)
    statement_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    for index, raw in enumerate(items):
        item_errors: list[str] = []
        item_name = f"typed_statements[{index}]"
        item = _mapping(raw, item_name, item_errors)
        _reject_unknown_fields(
            item,
            TYPED_STATEMENT_ALLOWED_FIELDS,
            item_name,
            item_errors,
        )
        statement_id = _str(item.get("id"), f"typed_statements[{index}].id", item_errors)
        status = _str(item.get("status"), f"typed_statements[{index}].status", item_errors)
        _str(item.get("statement"), f"typed_statements[{index}].statement", item_errors)
        _str(item.get("journal"), f"typed_statements[{index}].journal", item_errors)
        owner_surface = _str(
            item.get("owner_surface"),
            f"typed_statements[{index}].owner_surface",
            item_errors,
        )
        _str(
            item.get("authority_boundary"),
            f"typed_statements[{index}].authority_boundary",
            item_errors,
        )
        required_fields = _str_set(
            item.get("required_fields"),
            f"typed_statements[{index}].required_fields",
            item_errors,
        )

        if statement_id is not None:
            if statement_id in statement_ids:
                item_errors.append("typed statement id must be unique")
            statement_ids.add(statement_id)
        if status is not None and status not in ALLOWED_STATUSES:
            item_errors.append("typed statement status unsupported")
        if owner_surface is not None:
            _validate_repo_file(
                owner_surface,
                repo_root=repo_root,
                label="typed statement owner_surface",
                errors=item_errors,
                read_text=False,
            )
        if len(required_fields) < 4:
            item_errors.append("typed statement must list at least four required fields")
        pinned_fields = REQUIRED_STATEMENT_FIELDS.get(statement_id or "", frozenset())
        missing_fields = sorted(pinned_fields - required_fields)
        if missing_fields:
            item_errors.append(
                "typed statement missing pinned required fields: " + ",".join(missing_fields)
            )
        unexpected_fields = sorted(required_fields - pinned_fields) if pinned_fields else []
        if unexpected_fields:
            item_errors.append(
                "typed statement has unpinned fields: " + ",".join(unexpected_fields)
            )

        reports.append(
            {
                "id": statement_id,
                "ok": not item_errors,
                "errors": item_errors,
            }
        )

    missing = sorted(REQUIRED_STATEMENTS - statement_ids)
    if missing:
        errors.append(f"missing required typed statements: {','.join(missing)}")
    if any(not report["ok"] for report in reports):
        errors.append("one or more typed statements rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "typed_statement_count": len(statement_ids),
            "typed_statement_ids": sorted(statement_ids),
            "missing_required_statements": missing,
        },
        "items": reports,
    }


def _validate_obligations(value: Any, *, repo_root: Path | None) -> dict[str, Any]:
    errors: list[str] = []
    items = _list(value, "obligations", errors)
    obligation_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    implemented_count = 0
    pending_count = 0

    for index, raw in enumerate(items):
        item_errors: list[str] = []
        item_name = f"obligations[{index}]"
        item = _mapping(raw, item_name, item_errors)
        _reject_unknown_fields(
            item,
            OBLIGATION_ALLOWED_FIELDS,
            item_name,
            item_errors,
        )
        obligation_id = _str(item.get("id"), f"obligations[{index}].id", item_errors)
        _str(item.get("title"), f"obligations[{index}].title", item_errors)
        severity = _str(item.get("severity"), f"obligations[{index}].severity", item_errors)
        status = _str(item.get("status"), f"obligations[{index}].status", item_errors)
        defense_layer = _str(
            item.get("defense_layer"), f"obligations[{index}].defense_layer", item_errors
        )
        _str(item.get("disaster_state"), f"obligations[{index}].disaster_state", item_errors)
        _str(item.get("construction_rule"), f"obligations[{index}].construction_rule", item_errors)
        non_claim = _str(item.get("non_claim"), f"obligations[{index}].non_claim", item_errors)
        code_refs = _refs(item.get("code_refs"), f"obligations[{index}].code_refs", item_errors)
        test_refs = _refs(item.get("test_refs"), f"obligations[{index}].test_refs", item_errors)
        external_commands = _str_list(
            item.get("external_commands"),
            f"obligations[{index}].external_commands",
            item_errors,
        )

        if obligation_id is not None:
            if obligation_id in obligation_ids:
                item_errors.append("obligation id must be unique")
            obligation_ids.add(obligation_id)
        if severity is not None and severity not in ALLOWED_SEVERITIES:
            item_errors.append("obligation severity unsupported")
        if defense_layer is not None and defense_layer not in ALLOWED_DEFENSE_LAYERS:
            item_errors.append("obligation defense_layer unsupported")
        if status is not None and status not in ALLOWED_STATUSES:
            item_errors.append("obligation status unsupported")
        if obligation_id in REQUIRED_OBLIGATION_POLICY:
            minimum_severity, required_defense_layer = REQUIRED_OBLIGATION_POLICY[obligation_id]
            if SEVERITY_RANK.get(severity or "", -1) < SEVERITY_RANK[minimum_severity]:
                item_errors.append("required obligation severity is below its pinned minimum")
            if defense_layer != required_defense_layer:
                item_errors.append(
                    "required obligation defense_layer differs from its pinned layer"
                )
        if obligation_id in PINNED_PENDING_OBLIGATIONS:
            if status != "pending":
                item_errors.append(
                    "required obligation remains pinned pending until checker policy is updated"
                )
            if code_refs or test_refs or external_commands:
                item_errors.append(
                    "pinned pending obligation must not cite implementation evidence"
                )
        if status in IMPLEMENTED_STATUSES:
            implemented_count += 1
            if not code_refs:
                item_errors.append("implemented obligation must include code_refs")
            if not test_refs:
                item_errors.append("implemented obligation must include test_refs")
            if not external_commands:
                item_errors.append("implemented obligation must include external_commands")
        if status in PENDING_STATUSES:
            pending_count += 1
            if not _str(item.get("next_action"), f"obligations[{index}].next_action", item_errors):
                item_errors.append("pending obligation must include next_action")
        if severity == "critical" and not non_claim:
            item_errors.append("critical obligation must include non_claim")

        for ref in code_refs + test_refs:
            _validate_ref(ref, repo_root=repo_root, errors=item_errors)

        reports.append(
            {
                "id": obligation_id,
                "status": status,
                "severity": severity,
                "defense_layer": defense_layer,
                "ok": not item_errors,
                "errors": item_errors,
            }
        )

    missing = sorted(REQUIRED_OBLIGATIONS - obligation_ids)
    if missing:
        errors.append(f"missing required obligations: {','.join(missing)}")
    if any(not report["ok"] for report in reports):
        errors.append("one or more obligations rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "obligation_count": len(obligation_ids),
            "implemented_obligation_count": implemented_count,
            "pending_obligation_count": pending_count,
            "obligation_ids": sorted(obligation_ids),
            "missing_required_obligations": missing,
        },
        "items": reports,
    }


def _validate_ref(ref: Mapping[str, str], *, repo_root: Path | None, errors: list[str]) -> None:
    path = ref.get("path")
    symbol = ref.get("symbol")
    if not path or not symbol:
        errors.append("ref must include path and symbol")
        return
    text = _validate_repo_file(
        path,
        repo_root=repo_root,
        label="ref path",
        errors=errors,
        read_text=True,
    )
    if text is None:
        return
    if symbol not in text:
        errors.append(f"ref symbol missing: {path}::{symbol}")


def _validate_repo_file(
    path: str,
    *,
    repo_root: Path | None,
    label: str,
    errors: list[str],
    read_text: bool,
) -> str | None:
    try:
        parts = _normalized_repo_path(path)
    except MatrixInputError as exc:
        errors.append(f"{label} rejected: {exc}")
        return None
    if repo_root is None:
        errors.append(f"{label} cannot be checked because repository root was rejected")
        return None
    try:
        raw = _read_repo_file(repo_root, parts, max_bytes=MAX_REFERENCED_FILE_BYTES)
    except MatrixInputError as exc:
        errors.append(f"{label} rejected: {path}: {exc}")
        return None
    if not read_text:
        return ""
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        errors.append(f"{label} is not utf-8 text: {path}")
        return None


def _canonical_repo_root(path: Path) -> Path:
    absolute = Path(os.path.abspath(path))
    try:
        resolved = absolute.resolve(strict=True)
        path_stat = absolute.lstat()
    except OSError as exc:
        raise MatrixInputError("path is missing or inaccessible") from exc
    if resolved != absolute or stat.S_ISLNK(path_stat.st_mode):
        raise MatrixInputError("path must not traverse symbolic links")
    if not stat.S_ISDIR(path_stat.st_mode):
        raise MatrixInputError("path is not a directory")
    return absolute


def _normalized_repo_path(value: str) -> tuple[str, ...]:
    if "\x00" in value:
        raise MatrixInputError("path contains NUL")
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise MatrixInputError("path must contain ASCII only") from exc
    if not encoded or len(encoded) > MAX_REFERENCE_PATH_BYTES or "\\" in value:
        raise MatrixInputError("path must be a bounded POSIX repository-relative path")
    parsed = PurePosixPath(value)
    if parsed.is_absolute() or any(part in ("", ".", "..") for part in parsed.parts):
        raise MatrixInputError("path must not be absolute or traverse parents")
    if parsed.as_posix() != value:
        raise MatrixInputError("path must be normalized")
    return parsed.parts


def _read_repo_file(root: Path, parts: tuple[str, ...], *, max_bytes: int) -> bytes:
    directory_flags = os.O_RDONLY | _required_flag("O_DIRECTORY") | _required_flag("O_NOFOLLOW")
    directory_flags |= getattr(os, "O_CLOEXEC", 0)
    file_flags = os.O_RDONLY | _required_flag("O_NOFOLLOW") | getattr(os, "O_CLOEXEC", 0)
    directory_fds: list[int] = []
    file_fd: int | None = None
    try:
        directory_fds.append(os.open(root, directory_flags))
        current_fd = directory_fds[0]
        for component in parts[:-1]:
            component_stat = os.stat(component, dir_fd=current_fd, follow_symlinks=False)
            if stat.S_ISLNK(component_stat.st_mode):
                raise MatrixInputError("path contains a symbolic link")
            if not stat.S_ISDIR(component_stat.st_mode):
                raise MatrixInputError("path contains a non-directory component")
            current_fd = os.open(component, directory_flags, dir_fd=current_fd)
            directory_fds.append(current_fd)

        leaf_stat = os.stat(parts[-1], dir_fd=current_fd, follow_symlinks=False)
        if stat.S_ISLNK(leaf_stat.st_mode):
            raise MatrixInputError("path is a symbolic link")
        if not stat.S_ISREG(leaf_stat.st_mode):
            raise MatrixInputError("path is not a regular file")
        file_fd = os.open(parts[-1], file_flags, dir_fd=current_fd)
        opened_stat = os.fstat(file_fd)
        if (leaf_stat.st_dev, leaf_stat.st_ino) != (opened_stat.st_dev, opened_stat.st_ino):
            raise MatrixInputError("path changed while it was opened")
        return _read_bounded_fd(file_fd, max_bytes=max_bytes)
    except MatrixInputError:
        raise
    except OSError as exc:
        raise MatrixInputError("path is missing or unsafe") from exc
    finally:
        if file_fd is not None:
            os.close(file_fd)
        for descriptor in reversed(directory_fds):
            os.close(descriptor)


def _read_bounded_file(path: Path, *, max_bytes: int) -> bytes:
    absolute = Path(os.path.abspath(path))
    try:
        resolved_parent = absolute.parent.resolve(strict=True)
    except OSError as exc:
        raise MatrixInputError("file parent is missing or inaccessible") from exc
    if resolved_parent != absolute.parent:
        raise MatrixInputError("file path must not traverse symbolic links")
    flags = os.O_RDONLY | _required_flag("O_NOFOLLOW") | getattr(os, "O_CLOEXEC", 0)
    descriptor: int | None = None
    try:
        descriptor = os.open(absolute, flags)
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise MatrixInputError("file is not a regular file")
        return _read_bounded_fd(descriptor, max_bytes=max_bytes)
    except MatrixInputError:
        raise
    except OSError as exc:
        raise MatrixInputError("file is missing or unsafe") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


def _read_bounded_fd(descriptor: int, *, max_bytes: int) -> bytes:
    before = os.fstat(descriptor)
    if not stat.S_ISREG(before.st_mode):
        raise MatrixInputError("file is not a regular file")
    if before.st_size > max_bytes:
        raise MatrixInputError("file exceeds size limit")
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = os.read(descriptor, min(1024 * 1024, max_bytes + 1 - total))
        if not chunk:
            break
        total += len(chunk)
        if total > max_bytes:
            raise MatrixInputError("file exceeds size limit")
        chunks.append(chunk)
    after = os.fstat(descriptor)
    identity_before = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
    identity_after = (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
    if total != before.st_size or identity_before != identity_after:
        raise MatrixInputError("file changed while it was read")
    return b"".join(chunks)


def _required_flag(name: str) -> int:
    value = getattr(os, name, None)
    if not isinstance(value, int):
        raise MatrixInputError(f"platform lacks required {name} support")
    return value


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _reject_unknown_fields(
    value: Mapping[Any, Any],
    allowed_fields: frozenset[str],
    name: str,
    errors: list[str],
) -> None:
    if any(not isinstance(field, str) for field in value):
        errors.append(f"{name} field names must be strings")
    unknown_fields = sorted(
        field
        for field in value
        if isinstance(field, str) and field not in allowed_fields
    )
    if unknown_fields:
        errors.append(f"{name} has unknown fields: {','.join(unknown_fields)}")


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if not isinstance(value, bool):
        errors.append(f"{name} must be a boolean")
        return None
    return value


def _str_list(value: Any, name: str, errors: list[str]) -> list[str]:
    items = _list(value, name, errors)
    out: list[str] = []
    for index, item in enumerate(items):
        parsed = _str(item, f"{name}[{index}]", errors)
        if parsed is not None:
            out.append(parsed)
    return out


def _str_set(value: Any, name: str, errors: list[str]) -> set[str]:
    return set(_str_list(value, name, errors))


def _refs(value: Any, name: str, errors: list[str]) -> list[Mapping[str, str]]:
    items = _list(value, name, errors)
    out: list[Mapping[str, str]] = []
    for index, raw in enumerate(items):
        ref_errors: list[str] = []
        ref_name = f"{name}[{index}]"
        ref = _mapping(raw, ref_name, ref_errors)
        _reject_unknown_fields(ref, REFERENCE_ALLOWED_FIELDS, ref_name, ref_errors)
        path = _str(ref.get("path"), f"{name}[{index}].path", ref_errors)
        symbol = _str(ref.get("symbol"), f"{name}[{index}].symbol", ref_errors)
        if not ref_errors and path is not None and symbol is not None:
            out.append({"path": path, "symbol": symbol})
        errors.extend(ref_errors)
    return out


def _canonical_matrix_sha256(matrix: Any, errors: list[str]) -> str | None:
    try:
        canonical = json.dumps(
            matrix,
            allow_nan=False,
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError):
        errors.append("matrix contains a value that cannot be canonicalized")
        return None
    return "sha256:" + hashlib.sha256(canonical).hexdigest()


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise MatrixInputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_nonfinite(value: str) -> Any:
    raise MatrixInputError(f"non-finite JSON value is forbidden: {value}")


def load_matrix(path: Path) -> tuple[Any | None, list[str]]:
    try:
        raw = _read_bounded_file(path, max_bytes=MAX_MATRIX_BYTES)
        text = raw.decode("utf-8")
        return (
            json.loads(
                text,
                object_pairs_hook=_reject_duplicate_keys,
                parse_constant=_reject_nonfinite,
            ),
            [],
        )
    except MatrixInputError as exc:
        return None, [f"matrix rejected: {exc}"]
    except UnicodeDecodeError:
        return None, ["matrix rejected: file is not UTF-8"]
    except json.JSONDecodeError as exc:
        return None, [f"matrix json invalid: {exc.msg}"]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    matrix, load_errors = load_matrix(args.matrix)
    if load_errors:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": load_errors,
            "matrix_sha256": None,
        }
    else:
        report = validate_matrix(matrix)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
