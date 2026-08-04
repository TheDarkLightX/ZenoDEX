#!/usr/bin/env python3
"""Validate the FCIS M5-P4B5A ATDD contract without promoting authority."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MATRIX = (
    REPO_ROOT
    / "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/ACCEPTANCE_MATRIX.json"
)

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.fcis_m5_p4b5a_atdd_policy import (  # noqa: E402
    B1B2_PROMOTION_GATE,
    PATH_OWNERS,
)
from tools.fcis_m5_p4b5a_atdd_validation import (  # noqa: E402
    select_relevant_changed_paths,
    validate_policy,
)

SCHEMA = "zenodex/fcis-m5-p4b5a-atdd-contract/v1"
PHASE_ORDER = ["B1B-1", "B1B-2"]
ROOT_FIELDS = {
    "acceptance_cases",
    "b1b2_design_gate",
    "case_lifecycle",
    "contract_version",
    "normative_authority",
    "path_ownership_registry",
    "phase_order",
    "phases",
    "probity",
    "schema",
    "subagent_prompts",
}
NORMATIVE_AUTHORITY = {
    "document_path": (
        "docs/research/"
        "FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md"
    ),
    "document_sha256": (
        "cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5"
    ),
    "carrier_definition_path": (
        "docs/research/"
        "FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_1_20260729.md"
    ),
    "carrier_definition_sha256": (
        "a71752f138dc2de165dff78bd526d3ab734d900e6bbf0394832f6cb8b7a33226"
    ),
    "packet_commit": "1665e788a4c4daf43982262c307d0c04b914d89b",
    "packet_manifest_path": (
        "docs/research/prompts/"
        "fcis_m5_p4b5a_b1b_revision34_review_v1/SOURCE_MANIFEST.sha256"
    ),
    "packet_manifest_sha256": (
        "46c721c8dcc2082e8ea08e6cfb664e375cab2ff45b2dbf79b570093423017b9a"
    ),
    "target_commit": "a8b9d191b91a3258e3d7857784bbd6067a0463e1",
    "verdict": "APPROVE_B1B1_REVISION_3_4_UNMOUNTED",
}
B1B1_AUTHORIZED_SCOPE = {
    "FCISAuthorityHeaderV2",
    "DeploymentBootstrapAnchorClaimV2",
    "V1ToV2MigrationManifestV2",
    "canonical Python codecs and roots",
    "canonical Rust codecs and roots",
    "closed schemas and field registries",
    "limited structural-checker coverage",
    "shared positive and negative vectors",
}
B1B1_FORBIDDEN_SCOPE = {
    "AuthenticatedConfigurationUpdateCommandV2",
    "ConfigurationUpdateCommandClaimV2",
    "FCISCommittedStateV2",
    "PinnedDeploymentBootstrapVerifierV2",
    "StateBoundFeeDistributionConfigurationV2",
    "TransitionCauseV2",
    "V1ToV2MigrationCandidateV2",
    "V2CommitBundle",
    "V2Decision",
    "V2EvaluationCandidate",
    "configuration update",
    "outbox plan",
    "proof input",
    "publication",
    "receipt",
    "runtime mount",
    "successor-producing transition",
}
REQUIRED_CASE_IDS = {
    *(f"ATDD-B1B1-{index:03d}" for index in range(1, 13)),
    *(f"ATDD-B1B2-{index:03d}" for index in range(1, 9)),
}
ACCEPTANCE_FIELDS = {
    "counterexample",
    "evidence_commands",
    "evidence_level",
    "given",
    "id",
    "invariant",
    "nonclaims",
    "phase",
    "status",
    "then",
    "title",
    "when",
}
PROMPTS = {
    "b1b1_implementation": (
        "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/"
        "B1B1_IMPLEMENTATION_PROMPT.md"
    ),
    "b1b1_review": (
        "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/"
        "B1B1_REVIEW_PROMPT.md"
    ),
    "b1b2_design": (
        "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/"
        "B1B2_DESIGN_PROMPT.md"
    ),
    "b1b2_review": (
        "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/"
        "B1B2_REVIEW_PROMPT.md"
    ),
}
PROMPT_REQUIRED_TEXT = {
    "b1b1_implementation": (
        "APPROVE_B1B1_REVISION_3_4_UNMOUNTED",
        "Red -> Green -> Refactor -> Gate",
        "No runtime mount",
    ),
    "b1b1_review": (
        "falsification",
        "exact-head",
        "B1B-2 remains blocked",
    ),
    "b1b2_design": (
        "DESIGN ONLY",
        "execution_authorized = false",
        "store-current exact V1 state",
    ),
    "b1b2_review": (
        "APPROVE_B1B2_SOURCE_BOUND_MIGRATION_DESIGN_UNMOUNTED",
        "implementation remains unauthorized",
        "exact design manifest",
    ),
}


class DuplicateJsonMember(ValueError):
    """Raised when JSON repeats an object member."""


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateJsonMember(key)
        result[key] = value
    return result


def _load_matrix(path: Path) -> dict[str, object]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_strict_object,
        parse_constant=lambda token: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON token: {token}")
        ),
    )
    if type(value) is not dict:
        raise ValueError("matrix must contain one object")
    return cast(dict[str, object], value)


def _field_error(label: str, actual: set[str], expected: set[str]) -> str:
    missing = ",".join(sorted(expected - actual))
    unknown = ",".join(sorted(actual - expected))
    return f"{label}:missing={missing}:unknown={unknown}"


def _string_list(value: object) -> list[str] | None:
    if type(value) is not list or any(type(item) is not str for item in value):
        return None
    return cast(list[str], value)


def _validate_root(matrix: dict[str, object]) -> list[str]:
    errors: list[str] = []
    if set(matrix) != ROOT_FIELDS:
        errors.append(_field_error("ROOT_FIELDS", set(matrix), ROOT_FIELDS))
    if matrix.get("schema") != SCHEMA:
        errors.append("SCHEMA")
    if matrix.get("contract_version") != "1.0.0":
        errors.append("CONTRACT_VERSION")
    if matrix.get("phase_order") != PHASE_ORDER:
        order = _string_list(matrix.get("phase_order"))
        rendered = ",".join(order) if order is not None else "<invalid>"
        errors.append(f"PHASE_ORDER:{rendered}")
    return errors


def _validate_normative_authority(value: object) -> list[str]:
    if type(value) is not dict:
        return ["NORMATIVE_AUTHORITY_TYPE"]
    authority = cast(dict[str, object], value)
    errors = []
    if set(authority) != set(NORMATIVE_AUTHORITY):
        errors.append(
            _field_error(
                "NORMATIVE_AUTHORITY_FIELDS",
                set(authority),
                set(NORMATIVE_AUTHORITY),
            )
        )
    for field, expected in NORMATIVE_AUTHORITY.items():
        if authority.get(field) != expected:
            errors.append(f"NORMATIVE_AUTHORITY:{field}")
    return errors


def _validate_scope(
    value: object,
    expected: set[str],
    label: str,
) -> list[str]:
    items = _string_list(value)
    if items is None:
        return [f"{label}:TYPE"]
    actual = set(items)
    errors = []
    if len(actual) != len(items):
        errors.append(f"{label}:DUPLICATE")
    if actual != expected:
        errors.append(_field_error(label, actual, expected))
    return errors


def _validate_phases(value: object) -> list[str]:
    if type(value) is not dict:
        return ["PHASES_TYPE"]
    phases = cast(dict[str, object], value)
    errors: list[str] = []
    if set(phases) != set(PHASE_ORDER):
        errors.append(
            _field_error("PHASES_FIELDS", set(phases), set(PHASE_ORDER))
        )
        return errors
    b1b1 = phases["B1B-1"]
    b1b2 = phases["B1B-2"]
    phase_fields = {
        "authorized_scope",
        "execution_authorized",
        "forbidden_scope",
        "promotion_gate",
        "status",
    }
    for name, phase in (("B1B-1", b1b1), ("B1B-2", b1b2)):
        if type(phase) is not dict:
            errors.append(f"PHASE_TYPE:{name}")
            continue
        phase_map = cast(dict[str, object], phase)
        if set(phase_map) != phase_fields:
            errors.append(
                _field_error(f"PHASE_FIELDS:{name}", set(phase_map), phase_fields)
            )
    if type(b1b1) is dict:
        b1b1_map = cast(dict[str, object], b1b1)
        if b1b1_map.get("status") != "authorized_unmounted_implementation":
            errors.append("B1B1_STATUS")
        if b1b1_map.get("execution_authorized") is not True:
            errors.append("B1B1_EXECUTION_AUTHORITY")
        errors.extend(
            _validate_scope(
                b1b1_map.get("authorized_scope"),
                B1B1_AUTHORIZED_SCOPE,
                "B1B1_AUTHORIZED_SCOPE",
            )
        )
        errors.extend(
            _validate_scope(
                b1b1_map.get("forbidden_scope"),
                B1B1_FORBIDDEN_SCOPE,
                "B1B1_FORBIDDEN_SCOPE",
            )
        )
        if (
            b1b1_map.get("promotion_gate")
            != "independent exact-head implementation review"
        ):
            errors.append("B1B1_PROMOTION_GATE")
    if type(b1b2) is dict:
        b1b2_map = cast(dict[str, object], b1b2)
        if (
            b1b2_map.get("status")
            != "design_only_blocked_pending_b1b1_exact_head_approval"
            or b1b2_map.get("execution_authorized") is not False
        ):
            errors.append("B1B2_EXECUTION_PREMATURE")
        if b1b2_map.get("promotion_gate") != B1B2_PROMOTION_GATE:
            errors.append("B1B2_PROMOTION_GATE")
    return errors


def _validate_acceptance_cases(value: object) -> tuple[list[str], int, int]:
    if type(value) is not list:
        return ["ACCEPTANCE_CASES_TYPE"], 0, 0
    cases = cast(list[object], value)
    errors: list[str] = []
    ids: list[str] = []
    b1b1_count = 0
    b1b2_count = 0
    for index, item in enumerate(cases):
        if type(item) is not dict:
            errors.append(f"ACCEPTANCE_CASE_TYPE:{index}")
            continue
        case = cast(dict[str, object], item)
        case_id = case.get("id")
        label = case_id if type(case_id) is str else f"index-{index}"
        if set(case) != ACCEPTANCE_FIELDS:
            errors.append(
                _field_error(
                    f"ACCEPTANCE_FIELDS:{label}",
                    set(case),
                    ACCEPTANCE_FIELDS,
                )
            )
        if type(case_id) is not str or re.fullmatch(
            r"ATDD-B1B[12]-[0-9]{3}", case_id
        ) is None:
            errors.append(f"ACCEPTANCE_ID:{label}")
            continue
        ids.append(case_id)
        expected_phase = "B1B-1" if case_id.startswith("ATDD-B1B1-") else "B1B-2"
        if case.get("phase") != expected_phase:
            errors.append(f"ACCEPTANCE_PHASE:{case_id}")
        if expected_phase == "B1B-1":
            b1b1_count += 1
            if case.get("status") != "ready":
                errors.append(f"ACCEPTANCE_STATUS:{case_id}")
        else:
            b1b2_count += 1
            if case.get("status") != "design_only":
                errors.append(f"ACCEPTANCE_STATUS:{case_id}")
        for field in (
            "counterexample",
            "evidence_level",
            "given",
            "invariant",
            "then",
            "title",
            "when",
        ):
            field_value = case.get(field)
            if type(field_value) is not str or not field_value.strip():
                errors.append(f"ACCEPTANCE_VALUE:{case_id}:{field}")
        for field in ("evidence_commands", "nonclaims"):
            items = _string_list(case.get(field))
            if items is None or not items or any(not item.strip() for item in items):
                errors.append(f"ACCEPTANCE_LIST:{case_id}:{field}")
        commands = _string_list(case.get("evidence_commands")) or []
        for command in commands:
            if "PYTHONPATH=" in command:
                errors.append(f"EVIDENCE_HIDDEN_ENV:{case_id}:PYTHONPATH=")
    for case_id, count in sorted(Counter(ids).items()):
        if count > 1:
            errors.append(f"ACCEPTANCE_ID_DUPLICATE:{case_id}")
    actual_ids = set(ids)
    if actual_ids != REQUIRED_CASE_IDS:
        errors.append(
            _field_error(
                "ACCEPTANCE_IDS",
                actual_ids,
                REQUIRED_CASE_IDS,
            )
        )
    return errors, b1b1_count, b1b2_count


def _validate_prompts(value: object) -> list[str]:
    if type(value) is not dict:
        return ["SUBAGENT_PROMPTS_TYPE"]
    prompts = cast(dict[str, object], value)
    errors: list[str] = []
    if prompts != PROMPTS:
        errors.append("SUBAGENT_PROMPTS")
        return errors
    for role, relative in PROMPTS.items():
        path = REPO_ROOT / relative
        if not path.is_file():
            errors.append(f"PROMPT_MISSING:{role}")
            continue
        text = path.read_text(encoding="utf-8")
        for required in PROMPT_REQUIRED_TEXT[role]:
            if required not in text:
                errors.append(f"PROMPT_TEXT_MISSING:{role}:{required}")
    return errors


def _validate_probity(value: object) -> list[str]:
    expected_fields = {
        "authority",
        "install_authorized",
        "mode",
        "normative_gate",
    }
    if type(value) is not dict:
        return ["PROBITY_TYPE"]
    probity = cast(dict[str, object], value)
    errors: list[str] = []
    if set(probity) != expected_fields:
        errors.append(
            _field_error("PROBITY_FIELDS", set(probity), expected_fields)
        )
    if probity.get("authority") is not False:
        errors.append("PROBITY_MUST_REMAIN_NON_AUTHORITATIVE")
    if probity.get("install_authorized") is not False:
        errors.append("PROBITY_INSTALL_NOT_AUTHORIZED")
    if probity.get("mode") != "optional_isolated_pilot":
        errors.append("PROBITY_MODE")
    if (
        probity.get("normative_gate")
        != "repository ATDD matrix, deterministic checker, and executable tests"
    ):
        errors.append("PROBITY_NORMATIVE_GATE")
    return errors


def validate_matrix(
    matrix: dict[str, object],
    *,
    assigned_id: str,
    changed_paths: tuple[str, ...] = (),
) -> tuple[list[str], int, int]:
    errors = _validate_root(matrix)
    errors.extend(_validate_normative_authority(matrix.get("normative_authority")))
    errors.extend(_validate_phases(matrix.get("phases")))
    case_errors, b1b1_count, b1b2_count = _validate_acceptance_cases(
        matrix.get("acceptance_cases")
    )
    errors.extend(case_errors)
    errors.extend(_validate_prompts(matrix.get("subagent_prompts")))
    errors.extend(_validate_probity(matrix.get("probity")))
    errors.extend(
        validate_policy(
            matrix,
            assigned_id=assigned_id,
            required_ids=REQUIRED_CASE_IDS,
            changed_paths=changed_paths,
        )
    )
    return sorted(set(errors)), b1b1_count, b1b2_count


class GitDiffDiscoveryError(RuntimeError):
    """Raised when the complete changed-path set cannot be derived."""


def _run_git(repo_root: Path, arguments: list[str]) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *arguments],
        check=False,
        capture_output=True,
    )
    if completed.returncode != 0:
        raise GitDiffDiscoveryError(
            f"git {' '.join(arguments[:2])} failed:{completed.returncode}"
        )
    return completed.stdout


def _decode_nul_paths(raw: bytes) -> set[str]:
    if not raw:
        return set()
    if not raw.endswith(b"\0"):
        raise GitDiffDiscoveryError("git path output is not NUL terminated")
    paths: set[str] = set()
    for item in raw[:-1].split(b"\0"):
        try:
            path = item.decode("utf-8", errors="strict")
        except UnicodeDecodeError as exc:
            raise GitDiffDiscoveryError("git path is not UTF-8") from exc
        if not path or path.startswith("/") or ".." in Path(path).parts:
            raise GitDiffDiscoveryError("git returned a non-relative path")
        paths.add(path)
    return paths


def _existing_owned_evidence_paths(repo_root: Path) -> set[str]:
    paths: set[str] = set()
    for row in PATH_OWNERS:
        pattern = cast(str, row["pattern"])
        for candidate in repo_root.glob(pattern):
            if candidate.is_file() or candidate.is_symlink():
                paths.add(candidate.relative_to(repo_root).as_posix())
    return paths


def discover_changed_paths(repo_root: Path, diff_base: str) -> tuple[str, ...]:
    """Derive changes and reject ignored untracked evidence without caller input."""

    if diff_base != "HEAD" and re.fullmatch(r"[0-9a-f]{40}", diff_base) is None:
        raise GitDiffDiscoveryError("diff base must be HEAD or a lowercase full SHA")
    _run_git(
        repo_root,
        ["rev-parse", "--verify", "--quiet", f"{diff_base}^{{commit}}"],
    )
    tracked_changes = _decode_nul_paths(
        _run_git(
            repo_root,
            [
                "diff",
                "--name-only",
                "--diff-filter=ACDMRTUXB",
                "-z",
                diff_base,
                "--",
            ],
        )
    )
    untracked = _decode_nul_paths(
        _run_git(
            repo_root,
            ["ls-files", "--others", "--exclude-standard", "-z", "--"],
        )
    )
    tracked_files = _decode_nul_paths(
        _run_git(repo_root, ["ls-files", "-z", "--"])
    )
    ignored_owned = sorted(
        _existing_owned_evidence_paths(repo_root)
        - tracked_files
        - untracked
    )
    if ignored_owned:
        rendered = ",".join(ignored_owned)
        raise GitDiffDiscoveryError(
            f"owned evidence path is ignored and untracked:{rendered}"
        )
    return tuple(sorted(tracked_changes | untracked))


def resolve_merge_base(repo_root: Path, other_commit: str) -> str:
    """Resolve the exact event merge base from one trusted full commit ID."""

    if re.fullmatch(r"[0-9a-f]{40}", other_commit) is None:
        raise GitDiffDiscoveryError(
            "merge-base peer must be a lowercase full SHA"
        )
    _run_git(
        repo_root,
        ["rev-parse", "--verify", "--quiet", f"{other_commit}^{{commit}}"],
    )
    raw = _run_git(repo_root, ["merge-base", other_commit, "HEAD"])
    try:
        merge_base = raw.decode("ascii", errors="strict").strip()
    except UnicodeDecodeError as exc:
        raise GitDiffDiscoveryError("merge base is not ASCII") from exc
    if re.fullmatch(r"[0-9a-f]{40}", merge_base) is None:
        raise GitDiffDiscoveryError("git returned no unique full merge base")
    return merge_base


def _report(
    *,
    assigned_id: str,
    changed_path_count: int,
    errors: list[str],
    b1b1_count: int = 0,
    b1b2_count: int = 0,
) -> dict[str, Any]:
    return {
        "acceptance_case_count": b1b1_count + b1b2_count,
        "assigned_acceptance_id": assigned_id,
        "b1b1_case_count": b1b1_count,
        "b1b2_case_count": b1b2_count,
        "changed_path_count": changed_path_count,
        "errors": errors,
        "ok": not errors,
        "phase_order": PHASE_ORDER,
        "schema": SCHEMA,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
    parser.add_argument("--assigned-id", required=True)
    diff_source = parser.add_mutually_exclusive_group()
    diff_source.add_argument("--diff-base")
    diff_source.add_argument("--merge-base-with")
    args = parser.parse_args()
    try:
        diff_base = "HEAD"
        if args.merge_base_with is not None:
            diff_base = resolve_merge_base(REPO_ROOT, args.merge_base_with)
        elif args.diff_base is not None:
            diff_base = args.diff_base
        changed_paths = select_relevant_changed_paths(
            discover_changed_paths(REPO_ROOT, diff_base)
        )
    except GitDiffDiscoveryError as exc:
        report = _report(
            assigned_id=args.assigned_id,
            changed_path_count=0,
            errors=[f"DIFF_DISCOVERY:{exc}"],
        )
    else:
        try:
            matrix = _load_matrix(args.matrix)
        except DuplicateJsonMember as exc:
            report = _report(
                assigned_id=args.assigned_id,
                changed_path_count=len(changed_paths),
                errors=[f"MATRIX_INVALID:DuplicateJsonMember:{exc}"],
            )
        except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
            report = _report(
                assigned_id=args.assigned_id,
                changed_path_count=len(changed_paths),
                errors=[f"MATRIX_INVALID:{type(exc).__name__}"],
            )
        else:
            errors, b1b1_count, b1b2_count = validate_matrix(
                matrix,
                assigned_id=args.assigned_id,
                changed_paths=changed_paths,
            )
            report = _report(
                assigned_id=args.assigned_id,
                changed_path_count=len(changed_paths),
                errors=errors,
                b1b1_count=b1b1_count,
                b1b2_count=b1b2_count,
            )
    sys.stdout.write(json.dumps(report, sort_keys=True) + "\n")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
