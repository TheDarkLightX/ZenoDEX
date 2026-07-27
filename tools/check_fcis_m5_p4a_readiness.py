#!/usr/bin/env python3
"""Validate the FCIS M5-P4A readiness packet without promoting authority.

An honest ``BLOCKED`` packet is structurally valid and exits successfully.
``--require-ready`` is the promotion gate and fails until every structural,
differential, and cross-consumer blocker is closed.
"""

# ruff: noqa: E402 -- the executable tool must add the repository root before src imports

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.state.canonical import canonical_json_bytes
from tools.run_fcis_m5_p4a_differential_replay import compare_observations_v1

_REVIEWED_START_SHA = "c344bac741c1d4a15511b77f8e2b60f93260a449"
_RECEIPT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_READINESS_RECEIPT_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-readiness-receipt/v1"
_ARTIFACTS = {
    "baseline": _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_LEGACY_BASELINE_V1.json",
    "differential": _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json",
    "mount_graph": _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_MOUNT_CALL_GRAPH_V1.json",
    "cross_language": _REPO_ROOT
    / "docs"
    / "research"
    / "FCIS_M5_P4A_CROSS_LANGUAGE_MATRIX_V1.json",
}
_GENERATOR_CHECKS = {
    "baseline": ("tools/build_fcis_m5_p4a_baseline.py", "--check"),
    "differential": ("tools/run_fcis_m5_p4a_differential_replay.py", "--check"),
    "mount_graph": ("tools/build_fcis_m5_p4a_call_graph_ledger.py", "--check"),
    "cross_language": (
        "tools/build_fcis_m5_p4a_cross_language_matrix.py",
        "--check",
    ),
}
_BASELINE_SCHEMA = "zenodex/fcis-m5-p4a-legacy-baseline/v1"
_DIFFERENTIAL_SCHEMA = "zenodex/fcis-m5-p4a-differential-replay/v1"
_MOUNT_GRAPH_SCHEMA = "zenodex/fcis-m5-p4a-mount-call-graph/v1"
_CROSS_LANGUAGE_SCHEMA = "zenodex/fcis-m5-p4a-cross-language-matrix/v1"
_MOUNT_STATUSES = frozenset(
    {
        "EXACT_READY",
        "MIGRATE_IN_P4B",
        "LEGACY_DIFFERENTIAL_ONLY",
        "P5_GATE_REQUIRED",
        "BLOCKER",
        "UNKNOWN",
    }
)
_PARITY_STATUSES = frozenset(
    {
        "PASS_EXACT_BYTES",
        "UNPROMOTED_SHADOW_ONLY",
        "MISSING_BLOCKER",
        "NOT_APPLICABLE_WITH_REASON",
    }
)
_CONSUMERS = frozenset(
    {
        "python_fcis",
        "rust_runtime",
        "tau_adapter",
        "proof_guest",
        "settlement_verifier",
    }
)
_COMMITTABLE_REJECT_FIELDS = frozenset(
    {
        "next_state_snapshot_bytes",
        "next_state_snapshot_root",
        "settlement_bytes",
        "patch_bytes",
        "commit_plan_bytes",
        "effects_bytes",
        "replay_bytes",
        "outbox_bytes",
        "outbox_identities",
        "bundle_bytes",
        "bundle_root",
    }
)
_OBSERVABLE_FIELDS = frozenset(
    {
        "algorithm_id",
        "algorithm_version",
        "bundle_bytes",
        "bundle_root",
        "codec_version",
        "commit_plan_bytes",
        "effects_bytes",
        "fee_allocation",
        "next_nonce_table_hash",
        "next_state_snapshot_bytes",
        "next_state_snapshot_root",
        "outbox_bytes",
        "outbox_identities",
        "patch_bytes",
        "receipt_bytes",
        "receipt_root",
        "rejection",
        "replay_bytes",
        "result_kind",
        "schema_version",
        "settlement_bytes",
        "snapshot_version",
        "support_root",
        "support_root_version",
        "total_swap_fees",
    }
)
_ALLOWED_TOOL_PATHS = frozenset(
    {
        "tools/build_fcis_m5_p4a_baseline.py",
        "tools/run_fcis_m5_p4a_differential_replay.py",
        "tools/build_fcis_m5_p4a_call_graph_ledger.py",
        "tools/build_fcis_m5_p4a_cross_language_matrix.py",
        "tools/check_fcis_m5_p4a_readiness.py",
        "tests/tools/test_check_fcis_m5_p4a_readiness.py",
    }
)


class DuplicateJsonKey(ValueError):
    """Raised when an evidence object repeats a key."""


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateJsonKey(key)
        result[key] = value
    return result


def _sha256(raw: bytes) -> str:
    return "0x" + hashlib.sha256(raw).hexdigest()


def _payload_without_hash(
    value: dict[str, object],
    hash_field: str = "artifact_sha256",
) -> bytes:
    payload = dict(value)
    payload.pop(hash_field, None)
    return canonical_json_bytes(payload)


def load_canonical_json_v1(path: Path) -> dict[str, object]:
    raw = path.read_bytes()
    value = json.loads(
        raw.decode("utf-8"),
        object_pairs_hook=_strict_object,
        parse_constant=lambda token: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON token: {token}")
        ),
    )
    if type(value) is not dict:
        raise ValueError(f"{path.name} must contain one object")
    result = cast(dict[str, object], value)
    if canonical_json_bytes(result) != raw:
        raise ValueError(f"{path.name} is not canonical JSON")
    return result


def _artifact_hash_errors(value: dict[str, object]) -> list[str]:
    claimed = value.get("artifact_sha256")
    if type(claimed) is not str:
        return ["missing or non-string artifact_sha256"]
    actual = _sha256(_payload_without_hash(value))
    if claimed != actual:
        return [f"artifact_sha256 mismatch: claimed={claimed}, actual={actual}"]
    return []


def _expect_exact_fields(
    value: dict[str, object],
    expected: set[str],
    label: str,
) -> list[str]:
    actual = set(value)
    if actual == expected:
        return []
    return [
        f"{label} fields changed: missing={sorted(expected - actual)}, "
        f"unknown={sorted(actual - expected)}"
    ]


def _dict_list(value: object, label: str) -> tuple[list[dict[str, object]], list[str]]:
    if type(value) is not list or any(type(row) is not dict for row in value):
        return [], [f"{label} must be a list of objects"]
    return cast(list[dict[str, object]], value), []


def validate_baseline_v1(value: dict[str, object]) -> list[str]:
    errors = _artifact_hash_errors(value)
    errors.extend(
        _expect_exact_fields(
            value,
            {
                "artifact_sha256",
                "command_inventory",
                "command_kinds_covered",
                "fixture_count",
                "fixtures",
                "generation_command",
                "generator_hash",
                "python_version",
                "reviewed_source_sha",
                "schema",
                "source_tree_hash",
            },
            "baseline",
        )
    )
    if value.get("schema") != _BASELINE_SCHEMA:
        errors.append("baseline schema mismatch")
    if value.get("reviewed_source_sha") != _REVIEWED_START_SHA:
        errors.append("baseline reviewed_source_sha mismatch")
    inventory, inventory_errors = _dict_list(value.get("command_inventory"), "command_inventory")
    fixtures, fixture_errors = _dict_list(value.get("fixtures"), "fixtures")
    errors.extend(inventory_errors)
    errors.extend(fixture_errors)
    inventory_kinds: list[str] = []
    mounted_kinds: set[str] = set()
    for row in inventory:
        command = row.get("command_kind")
        if type(command) is not str:
            errors.append("command inventory row lacks string command_kind")
            continue
        inventory_kinds.append(command)
        if row.get("classification") == "unknown":
            errors.append(f"command inventory leaves {command} UNKNOWN")
        if row.get("mounted") is True and row.get("supported") is True:
            mounted_kinds.add(command)
        evidence = row.get("source_evidence")
        if type(evidence) is not list or not evidence:
            errors.append(f"command inventory {command} lacks source evidence")
    if len(inventory_kinds) != len(set(inventory_kinds)):
        errors.append("command inventory contains duplicate command kinds")
    if value.get("fixture_count") != len(fixtures):
        errors.append("baseline fixture_count does not match fixtures")
    fixture_ids: set[str] = set()
    outcomes: dict[str, set[bool]] = defaultdict(set)
    for fixture in fixtures:
        fixture_id = fixture.get("fixture_id")
        command = fixture.get("command_kind")
        accepted = fixture.get("accepted")
        if type(fixture_id) is not str or fixture_id in fixture_ids:
            errors.append("baseline fixture IDs are missing or duplicated")
        else:
            fixture_ids.add(fixture_id)
        if type(command) is not str or type(accepted) is not bool:
            errors.append(f"fixture {fixture_id!r} lacks typed command/outcome")
            continue
        outcomes[command].add(accepted)
        for field in (
            "canonical_command_bytes",
            "canonical_command_hash",
            "execution_context_bytes",
            "execution_context_hash",
            "pre_state_root",
            "pre_state_snapshot_bytes",
            "pre_state_snapshot_root",
            "observable_projection",
            "rejection",
        ):
            if field not in fixture:
                errors.append(f"fixture {fixture_id} omits {field}")
    for command in sorted(mounted_kinds):
        if outcomes.get(command) != {False, True}:
            errors.append(f"mounted command {command} lacks accepted and rejected fixtures")
    covered = value.get("command_kinds_covered")
    if type(covered) is not list or set(cast(list[object], covered)) != set(outcomes):
        errors.append("command_kinds_covered does not equal fixture command kinds")
    return errors


def validate_differential_v1(
    value: dict[str, object],
    baseline: dict[str, object],
) -> list[str]:
    errors = _artifact_hash_errors(value)
    errors.extend(
        _expect_exact_fields(
            value,
            {
                "artifact_sha256",
                "baseline_artifact_sha256",
                "baseline_generator_hash",
                "baseline_source_tree_hash",
                "divergence_count",
                "fixture_count",
                "fixtures",
                "match_count",
                "observable_fields",
                "parity_complete",
                "reviewed_expected_difference_allowlist",
                "schema",
            },
            "differential",
        )
    )
    if value.get("schema") != _DIFFERENTIAL_SCHEMA:
        errors.append("differential schema mismatch")
    if value.get("baseline_artifact_sha256") != baseline.get("artifact_sha256"):
        errors.append("differential does not bind the baseline artifact")
    if value.get("baseline_generator_hash") != baseline.get("generator_hash"):
        errors.append("differential does not bind the baseline generator")
    if value.get("baseline_source_tree_hash") != baseline.get("source_tree_hash"):
        errors.append("differential does not bind the baseline source tree")
    if value.get("reviewed_expected_difference_allowlist") != []:
        errors.append("differential expected-difference allowlist must remain empty")
    observable_fields = value.get("observable_fields")
    if type(observable_fields) is not list or set(observable_fields) != _OBSERVABLE_FIELDS:
        errors.append("differential observable field contract changed")
    fixtures, fixture_errors = _dict_list(value.get("fixtures"), "differential fixtures")
    errors.extend(fixture_errors)
    baseline_fixtures, baseline_fixture_errors = _dict_list(
        baseline.get("fixtures"), "baseline fixtures"
    )
    errors.extend(baseline_fixture_errors)
    baseline_by_id = {
        cast(str, row["fixture_id"]): row
        for row in baseline_fixtures
        if type(row.get("fixture_id")) is str
    }
    seen: set[str] = set()
    matches = 0
    divergences = 0
    for fixture in fixtures:
        fixture_id = fixture.get("fixture_id")
        if type(fixture_id) is not str or fixture_id in seen:
            errors.append("differential fixture IDs are missing or duplicated")
            continue
        seen.add(fixture_id)
        baseline_fixture = baseline_by_id.get(fixture_id)
        if baseline_fixture is None:
            errors.append(f"differential fixture {fixture_id} is absent from baseline")
            continue
        if fixture.get("command_kind") != baseline_fixture.get("command_kind"):
            errors.append(f"differential fixture {fixture_id} changes command kind")
        binding = fixture.get("input_binding")
        if type(binding) is not dict:
            errors.append(f"differential fixture {fixture_id} lacks input binding")
        else:
            binding_object = cast(dict[str, object], binding)
            if binding_object.get("same_input_binding") is not True:
                errors.append(f"differential fixture {fixture_id} input binding differs")
            if not (
                binding_object.get("legacy")
                == binding_object.get("exact")
                == binding_object.get("expected")
            ):
                errors.append(f"differential fixture {fixture_id} input bytes differ")
        comparison = fixture.get("comparison")
        if type(comparison) is not dict:
            errors.append(f"differential fixture {fixture_id} lacks comparison")
            continue
        comparison_object = cast(dict[str, object], comparison)
        legacy = comparison_object.get("legacy")
        exact = comparison_object.get("exact")
        if type(legacy) is not dict or type(exact) is not dict:
            errors.append(f"differential fixture {fixture_id} observations malformed")
            continue
        legacy_object = cast(dict[str, object], legacy)
        exact_object = cast(dict[str, object], exact)
        if set(legacy_object) != _OBSERVABLE_FIELDS or set(exact_object) != _OBSERVABLE_FIELDS:
            errors.append(f"differential fixture {fixture_id} observable shape changed")
        recomputed = compare_observations_v1(legacy_object, exact_object)
        if comparison_object != recomputed:
            errors.append(f"differential fixture {fixture_id} comparison is stale")
        if recomputed["parity"] == "MATCH":
            matches += 1
        else:
            divergences += 1
        if exact_object.get("result_kind") == "reject":
            for field in _COMMITTABLE_REJECT_FIELDS:
                if exact_object.get(field) is not None:
                    errors.append(f"exact reject {fixture_id} exposes committable field {field}")
    if seen != set(baseline_by_id):
        errors.append("differential fixture set does not equal baseline fixture set")
    if value.get("fixture_count") != len(fixtures):
        errors.append("differential fixture_count mismatch")
    if value.get("match_count") != matches:
        errors.append("differential match_count mismatch")
    if value.get("divergence_count") != divergences:
        errors.append("differential divergence_count mismatch")
    if value.get("parity_complete") is not (divergences == 0):
        errors.append("differential parity_complete mismatch")
    return errors


def validate_mount_graph_v1(value: dict[str, object]) -> list[str]:
    errors = _artifact_hash_errors(value)
    if value.get("schema") != _MOUNT_GRAPH_SCHEMA:
        errors.append("mount graph schema mismatch")
    if value.get("reviewed_start_sha") != _REVIEWED_START_SHA:
        errors.append("mount graph reviewed_start_sha mismatch")
    rows, row_errors = _dict_list(value.get("violation_rows"), "violation_rows")
    sources, source_errors = _dict_list(value.get("source_rows"), "source_rows")
    errors.extend(row_errors)
    errors.extend(source_errors)
    checker_result = value.get("checker_result")
    checker_count: object = -1
    checked_path_count: object = -1
    if type(checker_result) is not dict:
        errors.append("mount graph checker_result malformed")
    else:
        checker_result_object = cast(dict[str, object], checker_result)
        checker_count = checker_result_object.get("violation_count")
        checked_path_count = checker_result_object.get("checked_path_count")
    if checker_count != len(rows):
        errors.append("mount graph violation count does not equal violation rows")
    if checked_path_count != len(sources):
        errors.append("mount graph checked path count does not equal source rows")
    identities: set[str] = set()
    recomputed_by_code: Counter[str] = Counter()
    recomputed_by_path: Counter[str] = Counter()
    status_counts: Counter[str] = Counter()
    source_paths = {cast(str, row["path"]) for row in sources if type(row.get("path")) is str}
    for row in rows:
        identity = row.get("violation_id")
        path = row.get("path")
        code = row.get("checker_code")
        status = row.get("status")
        if type(identity) is not str or identity in identities:
            errors.append("mount graph violation IDs are missing or duplicated")
        else:
            identities.add(identity)
        if type(path) is not str or path not in source_paths:
            errors.append("mount graph violation references unknown source path")
        if type(code) is not str:
            errors.append("mount graph violation lacks checker code")
        if type(status) is not str or status not in _MOUNT_STATUSES:
            errors.append("mount graph violation uses unknown status")
        elif status == "EXACT_READY":
            errors.append("unclosed checker violation cannot be EXACT_READY")
        if type(path) is str:
            recomputed_by_path[path] += 1
        if type(code) is str:
            recomputed_by_code[code] += 1
        if type(status) is str:
            status_counts[status] += 1
        for field in (
            "symbol",
            "authority_value_type",
            "read_write_effect_role",
            "mounted_reachability_evidence",
            "current_mechanism",
            "p4b_disposition",
            "owner",
            "verification_evidence",
        ):
            if field not in row:
                errors.append(f"mount graph violation row omits {field}")
    if value.get("violation_counts_by_code") != dict(sorted(recomputed_by_code.items())):
        errors.append("mount graph violation_counts_by_code mismatch")
    if value.get("violation_counts_by_path") != dict(sorted(recomputed_by_path.items())):
        errors.append("mount graph violation_counts_by_path mismatch")
    if value.get("status_counts") != dict(sorted(status_counts.items())):
        errors.append("mount graph status_counts mismatch")
    if value.get("ready_for_mount") is not (len(rows) == 0):
        errors.append("mount graph ready_for_mount mismatch")
    if value.get("graph_completeness") != "STATIC_IMPORT_AND_CALL_SYNTAX_ONLY":
        errors.append("mount graph overstates or changes completeness")
    closed = value.get("closed_statuses")
    if type(closed) is not list or set(closed) != _MOUNT_STATUSES:
        errors.append("mount graph closed status registry changed")
    return errors


def validate_cross_language_v1(
    value: dict[str, object],
    baseline: dict[str, object],
    mount_graph: dict[str, object],
) -> list[str]:
    errors = _artifact_hash_errors(value)
    if value.get("schema") != _CROSS_LANGUAGE_SCHEMA:
        errors.append("cross-language schema mismatch")
    if value.get("reviewed_start_sha") != _REVIEWED_START_SHA:
        errors.append("cross-language reviewed_start_sha mismatch")
    consumers = value.get("consumers")
    if type(consumers) is not list or set(consumers) != _CONSUMERS:
        errors.append("cross-language consumer registry changed")
    closed = value.get("closed_statuses")
    if type(closed) is not list or set(closed) != _PARITY_STATUSES:
        errors.append("cross-language status registry changed")
    rows, row_errors = _dict_list(value.get("rows"), "cross-language rows")
    errors.extend(row_errors)
    command_inventory, command_errors = _dict_list(
        baseline.get("command_inventory"), "command inventory"
    )
    source_rows, source_errors = _dict_list(mount_graph.get("source_rows"), "mount source rows")
    errors.extend(command_errors)
    errors.extend(source_errors)
    required_surfaces = {
        f"command:{row['command_kind']}"
        for row in command_inventory
        if type(row.get("command_kind")) is str
    }
    required_surfaces.update(
        f"authority_path:{row['path']}" for row in source_rows if type(row.get("path")) is str
    )
    identities: set[tuple[str, str]] = set()
    actual_by_surface: dict[str, set[str]] = defaultdict(set)
    statuses: Counter[str] = Counter()
    for row in rows:
        surface = row.get("surface_id")
        consumer = row.get("consumer")
        status = row.get("status")
        if type(surface) is not str or type(consumer) is not str:
            errors.append("cross-language row lacks typed identity")
            continue
        identity = (surface, consumer)
        if identity in identities:
            errors.append("cross-language matrix contains duplicate row")
        identities.add(identity)
        actual_by_surface[surface].add(consumer)
        if consumer not in _CONSUMERS:
            errors.append(f"cross-language row uses unknown consumer {consumer}")
        if type(status) is not str or status not in _PARITY_STATUSES:
            errors.append("cross-language row uses unknown status")
            continue
        statuses[status] += 1
        reason = row.get("reason")
        if type(reason) is not str or not reason:
            errors.append(f"cross-language row {identity} lacks reason")
        if status == "PASS_EXACT_BYTES":
            errors.append(
                f"P4A row {identity} claims PASS_EXACT_BYTES without a promoted consumer replay"
            )
        if status == "NOT_APPLICABLE_WITH_REASON" and not reason:
            errors.append(f"N/A row {identity} lacks reason")
    for surface in sorted(required_surfaces):
        if actual_by_surface.get(surface) != _CONSUMERS:
            errors.append(f"cross-language surface {surface} lacks full consumer coverage")
    if value.get("row_count") != len(rows):
        errors.append("cross-language row_count mismatch")
    if value.get("status_counts") != dict(sorted(statuses.items())):
        errors.append("cross-language status_counts mismatch")
    promoted = all(
        row.get("status") in {"PASS_EXACT_BYTES", "NOT_APPLICABLE_WITH_REASON"} for row in rows
    )
    if value.get("ready_for_mount") is not promoted:
        errors.append("cross-language ready_for_mount mismatch")
    if value.get("pass_exact_bytes_count") != statuses.get("PASS_EXACT_BYTES", 0):
        errors.append("cross-language exact pass count mismatch")
    return errors


def _run_git(*args: str) -> tuple[int, str, str]:
    result = subprocess.run(
        ["git", *args],
        cwd=_REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    return result.returncode, result.stdout, result.stderr


def _allowed_p4a_path(path: str) -> bool:
    return path in _ALLOWED_TOOL_PATHS or path.startswith("docs/research/FCIS_M5_P4A_")


def classify_changed_paths_v1(paths: set[str]) -> list[str]:
    return sorted(path for path in paths if not _allowed_p4a_path(path))


def _changed_paths() -> tuple[set[str], list[str]]:
    errors: list[str] = []
    returncode, _, stderr = _run_git("merge-base", "--is-ancestor", _REVIEWED_START_SHA, "HEAD")
    if returncode != 0:
        errors.append(f"reviewed start SHA is not an ancestor: {stderr.strip()}")
    paths: set[str] = set()
    for args in (
        ("diff", "--name-only", f"{_REVIEWED_START_SHA}..HEAD"),
        ("diff", "--name-only"),
        ("diff", "--cached", "--name-only"),
        ("ls-files", "--others", "--exclude-standard"),
    ):
        returncode, stdout, stderr = _run_git(*args)
        if returncode != 0:
            errors.append(f"git {' '.join(args)} failed: {stderr.strip()}")
            continue
        paths.update(line for line in stdout.splitlines() if line)
    return paths, errors


def _undeclared_artifacts() -> list[str]:
    declared = {path.resolve() for path in _ARTIFACTS.values()} | {_RECEIPT_PATH.resolve()}
    found = {
        path.resolve() for path in (_REPO_ROOT / "docs" / "research").glob("FCIS_M5_P4A_*.json")
    }
    return sorted(path.relative_to(_REPO_ROOT).as_posix() for path in found - declared)


def _regeneration_errors() -> list[str]:
    errors: list[str] = []
    for name, (tool, mode) in _GENERATOR_CHECKS.items():
        result = subprocess.run(
            [sys.executable, tool, mode],
            cwd=_REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        if result.returncode != 0:
            errors.append(
                f"{name} regeneration check failed: "
                f"{result.stdout.strip()} {result.stderr.strip()}".strip()
            )
    return errors


def _check_group(check_id: str, errors: list[str]) -> dict[str, object]:
    return {
        "check_id": check_id,
        "passed": not errors,
        "errors": errors,
    }


def _receipt_payload(value: dict[str, object]) -> bytes:
    return _payload_without_hash(value, "receipt_sha256")


def build_readiness_receipt_v1() -> dict[str, object]:
    groups: list[dict[str, object]] = []
    artifacts: dict[str, dict[str, object]] = {}
    artifact_errors: list[str] = []
    artifact_refs: list[dict[str, object]] = []
    for name, path in _ARTIFACTS.items():
        if not path.is_file():
            artifact_errors.append(f"missing {path.relative_to(_REPO_ROOT)}")
            continue
        try:
            value = load_canonical_json_v1(path)
        except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
            artifact_errors.append(f"invalid {path.name}: {exc}")
            continue
        artifacts[name] = value
        artifact_refs.append(
            {
                "name": name,
                "path": path.relative_to(_REPO_ROOT).as_posix(),
                "file_sha256": _sha256(path.read_bytes()),
            }
        )
    groups.append(_check_group("M5-P4A-CHECK-ARTIFACTS", artifact_errors))
    regeneration_errors = _regeneration_errors() if not artifact_errors else []
    groups.append(_check_group("M5-P4A-CHECK-REGENERATION", regeneration_errors))
    baseline_errors: list[str] = []
    differential_errors: list[str] = []
    mount_errors: list[str] = []
    cross_errors: list[str] = []
    baseline = artifacts.get("baseline")
    differential = artifacts.get("differential")
    mount_graph = artifacts.get("mount_graph")
    cross_language = artifacts.get("cross_language")
    if baseline is not None:
        baseline_errors = validate_baseline_v1(baseline)
    if baseline is not None and differential is not None:
        differential_errors = validate_differential_v1(differential, baseline)
    if mount_graph is not None:
        mount_errors = validate_mount_graph_v1(mount_graph)
    if baseline is not None and mount_graph is not None and cross_language is not None:
        cross_errors = validate_cross_language_v1(
            cross_language,
            baseline,
            mount_graph,
        )
    groups.extend(
        [
            _check_group("M5-P4A-CHECK-BASELINE", baseline_errors),
            _check_group("M5-P4A-CHECK-DIFFERENTIAL", differential_errors),
            _check_group("M5-P4A-CHECK-MOUNT-GRAPH", mount_errors),
            _check_group("M5-P4A-CHECK-CROSS-LANGUAGE", cross_errors),
        ]
    )
    changed, git_errors = _changed_paths()
    mutation_errors = [*git_errors]
    disallowed = classify_changed_paths_v1(changed)
    if disallowed:
        mutation_errors.append(f"P4A changed non-packet paths: {disallowed}")
    groups.append(_check_group("M5-P4A-CHECK-NO-AUTHORITY-SWITCH", mutation_errors))
    undeclared = _undeclared_artifacts()
    declaration_errors = [f"undeclared P4A JSON artifacts: {undeclared}"] if undeclared else []
    groups.append(_check_group("M5-P4A-CHECK-DECLARED-ARTIFACTS", declaration_errors))
    packet_complete = all(group["passed"] is True for group in groups)
    authority_violations = (
        len(cast(list[object], mount_graph.get("violation_rows", [])))
        if mount_graph is not None
        else -1
    )
    divergence_count = (
        cast(int, differential.get("divergence_count", -1))
        if differential is not None and type(differential.get("divergence_count")) is int
        else -1
    )
    missing_parity_rows = 0
    if cross_language is not None:
        rows, _ = _dict_list(cross_language.get("rows"), "rows")
        missing_parity_rows = sum(
            row.get("status") not in {"PASS_EXACT_BYTES", "NOT_APPLICABLE_WITH_REASON"}
            for row in rows
        )
    blockers: list[dict[str, object]] = []
    if authority_violations != 0:
        blockers.append(
            {
                "code": "FINAL_MOUNT_STRUCTURAL_VIOLATIONS",
                "count": authority_violations,
            }
        )
    if divergence_count != 0:
        blockers.append(
            {
                "code": "DIFFERENTIAL_PARITY_OPEN",
                "count": divergence_count,
            }
        )
    if missing_parity_rows != 0:
        blockers.append(
            {
                "code": "CROSS_CONSUMER_EXACT_BYTES_MISSING",
                "count": missing_parity_rows,
            }
        )
    mount_ready = packet_complete and not blockers
    receipt: dict[str, object] = {
        "schema": _SCHEMA,
        "reviewed_start_sha": _REVIEWED_START_SHA,
        "verdict": "READY" if mount_ready else "BLOCKED",
        "packet_complete": packet_complete,
        "mount_ready": mount_ready,
        "honest_blocked_outcome": packet_complete and not mount_ready,
        "authority_violations": authority_violations,
        "differential_divergences": divergence_count,
        "missing_cross_consumer_rows": missing_parity_rows,
        "check_violations": sum(group["passed"] is not True for group in groups),
        "blockers": blockers,
        "checks": groups,
        "artifact_references": sorted(artifact_refs, key=lambda row: cast(str, row["name"])),
        "changed_paths": sorted(changed),
        "nonclaims": [
            "P4A does not switch mounted authority.",
            "Static syntax evidence is not a complete runtime call graph.",
            "The reference evidence does not prove datastore linearizability or crash recovery.",
            "No Python/Rust/Tau/proof-guest/verifier exact-byte parity is promoted.",
            "Remote push state is not inferred by this local checker.",
        ],
    }
    receipt["receipt_sha256"] = _sha256(_receipt_payload(receipt))
    return receipt


def _write_receipt(receipt: dict[str, object]) -> None:
    _RECEIPT_PATH.parent.mkdir(parents=True, exist_ok=True)
    _RECEIPT_PATH.write_bytes(canonical_json_bytes(receipt))


def main() -> int:
    check_mode = "--check" in sys.argv
    require_ready = "--require-ready" in sys.argv
    receipt = build_readiness_receipt_v1()
    expected = canonical_json_bytes(receipt)
    if check_mode:
        if not _RECEIPT_PATH.is_file():
            print("ERROR: readiness receipt is missing", file=sys.stderr)
            return 1
        if _RECEIPT_PATH.read_bytes() != expected:
            print("ERROR: readiness receipt is stale", file=sys.stderr)
            return 1
    else:
        _write_receipt(receipt)
    if receipt["packet_complete"] is not True:
        print(
            f"ERROR: P4A packet validation failed (check_violations={receipt['check_violations']})",
            file=sys.stderr,
        )
        return 1
    if require_ready and receipt["mount_ready"] is not True:
        print(
            "BLOCKED: P4A is structurally valid but mount prerequisites remain "
            f"({receipt['blockers']})",
            file=sys.stderr,
        )
        return 1
    print(
        "OK: P4A packet is structurally valid "
        f"(verdict={receipt['verdict']}, blockers={receipt['blockers']})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
