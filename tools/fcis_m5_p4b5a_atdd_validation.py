"""Policy validation for the FCIS M5-P4B5A ATDD contract."""

from __future__ import annotations

from fnmatch import fnmatchcase
from typing import cast

from tools.fcis_m5_p4b5a_atdd_policy import (
    B1B2_DESIGN_GATE,
    FORBIDDEN_CHANGED_PATH_PATTERNS,
    INTEGRATION_ACCEPTANCE_ID,
    PATH_OWNERS,
    lifecycle_as_json,
)


def _string_list(value: object) -> list[str] | None:
    if type(value) is not list or any(type(item) is not str for item in value):
        return None
    return cast(list[str], value)


def _validate_lifecycle(value: object, required_ids: set[str]) -> list[str]:
    if type(value) is not dict:
        return ["CASE_LIFECYCLE_TYPE"]
    lifecycle = cast(dict[str, object], value)
    errors: list[str] = []
    expected = lifecycle_as_json()
    if lifecycle != expected:
        errors.append("CASE_LIFECYCLE")

    kind_names = (
        "precondition",
        "implementation",
        "phase_gate",
        "design_obligation",
    )
    kinds: dict[str, set[str]] = {}
    for name in kind_names:
        items = _string_list(lifecycle.get(name))
        if items is None:
            errors.append(f"CASE_LIFECYCLE_LIST:{name}")
            kinds[name] = set()
        else:
            kinds[name] = set(items)
    classified = set().union(*(kinds[name] for name in kind_names))
    if classified != required_ids:
        errors.append("CASE_LIFECYCLE_PARTITION")
    if sum(len(kinds[name]) for name in kind_names) != len(classified):
        errors.append("CASE_LIFECYCLE_OVERLAP")

    red_required = set(_string_list(lifecycle.get("red_required")) or [])
    for case_id in sorted(red_required - kinds["implementation"]):
        errors.append(f"RED_REQUIRED_NOT_IMPLEMENTATION:{case_id}")

    mutation_required = set(
        _string_list(lifecycle.get("mutation_kill_required")) or []
    )
    for case_id in sorted(mutation_required - kinds["implementation"]):
        errors.append(f"MUTATION_REQUIRED_NOT_IMPLEMENTATION:{case_id}")

    live = set(_string_list(lifecycle.get("live_evidence")) or [])
    planned = set(_string_list(lifecycle.get("planned_evidence")) or [])
    if live & planned or live | planned != required_ids:
        errors.append("EVIDENCE_STATUS_PARTITION")
    return errors


def _validate_b1b2_design_gate(value: object) -> list[str]:
    if value != B1B2_DESIGN_GATE:
        return ["B1B2_DESIGN_GATE"]
    return []


def _validate_path_ownership(
    value: object,
    *,
    assigned_id: str,
    changed_paths: tuple[str, ...],
) -> list[str]:
    errors: list[str] = []
    if value != (
        "tools/fcis_m5_p4b5a_atdd_policy.py#PATH_OWNERS"
    ):
        errors.append("PATH_OWNERSHIP")
    for path in sorted(set(changed_paths)):
        if any(fnmatchcase(path, pattern) for pattern in FORBIDDEN_CHANGED_PATH_PATTERNS):
            errors.append(f"CHANGED_PATH_FORBIDDEN:{path}")
            continue
        matching = [
            row
            for row in PATH_OWNERS
            if fnmatchcase(path, cast(str, row["pattern"]))
        ]
        if not matching:
            errors.append(f"CHANGED_PATH_UNOWNED:{path}")
            continue
        owners = {
            owner
            for row in matching
            for owner in cast(list[str], row["acceptance_ids"])
        }
        owners.add(INTEGRATION_ACCEPTANCE_ID)
        if assigned_id not in owners:
            errors.append(
                f"CHANGED_PATH_NOT_OWNED_BY_ASSIGNED_ID:{assigned_id}:{path}"
            )
    return errors


def validate_policy(
    matrix: dict[str, object],
    *,
    assigned_id: str,
    required_ids: set[str],
    changed_paths: tuple[str, ...],
) -> list[str]:
    """Validate lifecycle, phase promotion, and diff ownership policy."""

    errors = _validate_lifecycle(matrix.get("case_lifecycle"), required_ids)
    if assigned_id not in required_ids:
        errors.append(f"ASSIGNED_ID:{assigned_id}")
    errors.extend(_validate_b1b2_design_gate(matrix.get("b1b2_design_gate")))
    errors.extend(
        _validate_path_ownership(
            matrix.get("path_ownership_registry"),
            assigned_id=assigned_id,
            changed_paths=changed_paths,
        )
    )
    return errors
