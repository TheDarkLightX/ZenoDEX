#!/usr/bin/env python3
"""Validate the fail-closed ZRPF frontier decision graph.

The validator has two modes:

* structural mode accepts a graph that honestly marks candidates BLOCKED;
* admission mode exits 2 while any selected candidate has a dependency that is
  unproven, disproven, version-drifted, or otherwise different from PROVEN.

Only the Python standard library is used so this can run early in assurance CI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


SCHEMA = "zenodex/zrpf-frontier-decision-graph/v1"
SOURCE_SCHEMA = "research_kernel/report/v1"
DEPENDENCY_STATES = frozenset(
    {"PROVEN", "UNPROVEN", "DISPROVEN", "VERSION_DRIFTED"}
)
BLOCKING_STATES = frozenset({"UNPROVEN", "DISPROVEN", "VERSION_DRIFTED"})
PROMOTION_DECISIONS = frozenset({"ELIGIBLE", "BLOCKED"})
ASSUMPTION_FIELDS = (
    "dependency_id",
    "assumed_statement",
    "required_state",
    "version_requirement",
    "failure_effect",
    "rationale",
)
VERSION_FIELDS = ("component", "expected", "observed", "source_revision")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_SHA_RE = re.compile(r"^[0-9a-f]{40}$")


def _is_nonempty_string(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _validate_nonempty_string(
    obj: Mapping[str, Any], field: str, context: str, errors: list[str]
) -> None:
    if not _is_nonempty_string(obj.get(field)):
        errors.append(f"{context}.{field} must be a non-empty string")


def _validate_string_list(
    value: object,
    context: str,
    errors: list[str],
    *,
    nonempty: bool = False,
    sorted_unique: bool = False,
) -> list[str] | None:
    if not isinstance(value, list) or not all(_is_nonempty_string(v) for v in value):
        errors.append(f"{context} must be a list of non-empty strings")
        return None
    result = list(value)
    if nonempty and not result:
        errors.append(f"{context} must not be empty")
    if sorted_unique and result != sorted(set(result)):
        errors.append(f"{context} must be sorted and contain no duplicates")
    return result


def _duplicate_ids(items: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    duplicates: set[str] = set()
    for item in items:
        if item in seen:
            duplicates.add(item)
        seen.add(item)
    return sorted(duplicates)


def validate_graph(graph: object) -> list[str]:
    """Return deterministic structural and decision-consistency errors."""

    errors: list[str] = []
    if not isinstance(graph, dict):
        return ["root must be a JSON object"]

    if graph.get("schema") != SCHEMA:
        errors.append(f"schema must equal {SCHEMA!r}")
    _validate_nonempty_string(graph, "as_of", "root", errors)

    repository = graph.get("repository")
    if not isinstance(repository, dict):
        errors.append("root.repository must be an object")
    else:
        for field in (
            "full_name",
            "default_branch",
            "default_branch_sha",
            "integration_head_sha",
        ):
            _validate_nonempty_string(repository, field, "root.repository", errors)
        for field in ("default_branch_sha", "integration_head_sha"):
            value = repository.get(field)
            if isinstance(value, str) and not GIT_SHA_RE.fullmatch(value):
                errors.append(f"root.repository.{field} must be a 40-character git SHA")
        if not isinstance(repository.get("integration_pr"), int) or repository.get(
            "integration_pr", 0
        ) <= 0:
            errors.append("root.repository.integration_pr must be a positive integer")

    source_graph = graph.get("source_graph")
    if not isinstance(source_graph, dict):
        errors.append("root.source_graph must be an object")
    else:
        for field in ("path", "sha256", "schema", "run_id"):
            _validate_nonempty_string(source_graph, field, "root.source_graph", errors)
        digest = source_graph.get("sha256")
        if isinstance(digest, str) and not SHA256_RE.fullmatch(digest):
            errors.append("root.source_graph.sha256 must be 64 lowercase hex characters")
        if source_graph.get("schema") != SOURCE_SCHEMA:
            errors.append(f"root.source_graph.schema must equal {SOURCE_SCHEMA!r}")

    declared_states = _validate_string_list(
        graph.get("dependency_states"),
        "root.dependency_states",
        errors,
        nonempty=True,
        sorted_unique=False,
    )
    if declared_states is not None and set(declared_states) != DEPENDENCY_STATES:
        errors.append(
            "root.dependency_states must contain exactly "
            + ", ".join(sorted(DEPENDENCY_STATES))
        )

    dependency_items = graph.get("dependencies")
    if not isinstance(dependency_items, list) or not dependency_items:
        errors.append("root.dependencies must be a non-empty list")
        dependency_items = []

    dependency_ids: list[str] = []
    dependencies: dict[str, Mapping[str, Any]] = {}
    for index, item in enumerate(dependency_items):
        context = f"root.dependencies[{index}]"
        if not isinstance(item, dict):
            errors.append(f"{context} must be an object")
            continue
        for field in ("id", "statement", "state"):
            _validate_nonempty_string(item, field, context, errors)
        dependency_id = item.get("id")
        if isinstance(dependency_id, str) and dependency_id:
            dependency_ids.append(dependency_id)
            dependencies.setdefault(dependency_id, item)
        state = item.get("state")
        if state not in DEPENDENCY_STATES:
            errors.append(
                f"{context}.state must be one of {', '.join(sorted(DEPENDENCY_STATES))}"
            )
        _validate_string_list(
            item.get("evidence_refs"),
            f"{context}.evidence_refs",
            errors,
            nonempty=True,
        )
        version = item.get("version")
        if not isinstance(version, dict):
            errors.append(f"{context}.version must be an object")
        else:
            for field in VERSION_FIELDS:
                _validate_nonempty_string(version, field, f"{context}.version", errors)
            expected = version.get("expected")
            observed = version.get("observed")
            if state == "PROVEN" and expected != observed:
                errors.append(
                    f"{context} claims PROVEN but expected and observed versions differ"
                )
            if state == "VERSION_DRIFTED" and expected == observed:
                errors.append(
                    f"{context} claims VERSION_DRIFTED but expected and observed versions match"
                )

    for duplicate in _duplicate_ids(dependency_ids):
        errors.append(f"duplicate dependency id: {duplicate}")

    candidate_items = graph.get("candidates")
    if not isinstance(candidate_items, list) or not candidate_items:
        errors.append("root.candidates must be a non-empty list")
        candidate_items = []

    candidate_ids: list[str] = []
    for index, candidate in enumerate(candidate_items):
        context = f"root.candidates[{index}]"
        if not isinstance(candidate, dict):
            errors.append(f"{context} must be an object")
            continue
        for field in ("id", "origin", "content", "promotion_decision"):
            _validate_nonempty_string(candidate, field, context, errors)
        candidate_id = candidate.get("id")
        if isinstance(candidate_id, str) and candidate_id:
            candidate_ids.append(candidate_id)
        if not isinstance(candidate.get("selected"), bool):
            errors.append(f"{context}.selected must be a boolean")
        decision = candidate.get("promotion_decision")
        if decision not in PROMOTION_DECISIONS:
            errors.append(
                f"{context}.promotion_decision must be ELIGIBLE or BLOCKED"
            )

        declared_blockers = _validate_string_list(
            candidate.get("blockers"),
            f"{context}.blockers",
            errors,
            sorted_unique=True,
        )
        assumption_items = candidate.get("assumption_dependencies")
        if not isinstance(assumption_items, list) or not assumption_items:
            errors.append(f"{context}.assumption_dependencies must be a non-empty list")
            assumption_items = []

        referenced_ids: list[str] = []
        computed_blockers: set[str] = set()
        for assumption_index, assumption in enumerate(assumption_items):
            assumption_context = (
                f"{context}.assumption_dependencies[{assumption_index}]"
            )
            if not isinstance(assumption, dict):
                errors.append(f"{assumption_context} must be an object")
                continue
            for field in ASSUMPTION_FIELDS:
                _validate_nonempty_string(
                    assumption, field, assumption_context, errors
                )
            dependency_id = assumption.get("dependency_id")
            if isinstance(dependency_id, str) and dependency_id:
                referenced_ids.append(dependency_id)
            if assumption.get("required_state") != "PROVEN":
                errors.append(
                    f"{assumption_context}.required_state must be PROVEN; "
                    "selected-candidate admission cannot opt into a weaker state"
                )
            if assumption.get("failure_effect") != "BLOCK_PROMOTION":
                errors.append(
                    f"{assumption_context}.failure_effect must be BLOCK_PROMOTION"
                )
            dependency = dependencies.get(dependency_id) if isinstance(dependency_id, str) else None
            if dependency is None:
                if isinstance(dependency_id, str) and dependency_id:
                    errors.append(
                        f"{assumption_context} references unknown dependency {dependency_id!r}"
                    )
                continue
            if dependency.get("state") != "PROVEN":
                computed_blockers.add(dependency_id)

        for duplicate in _duplicate_ids(referenced_ids):
            errors.append(f"{context} references dependency {duplicate!r} more than once")

        expected_blockers = sorted(computed_blockers)
        if declared_blockers is not None and declared_blockers != expected_blockers:
            errors.append(
                f"{context}.blockers must equal computed blockers {expected_blockers!r}"
            )
        expected_decision = "BLOCKED" if expected_blockers else "ELIGIBLE"
        if decision in PROMOTION_DECISIONS and decision != expected_decision:
            errors.append(
                f"{context}.promotion_decision must be {expected_decision} from dependency states"
            )

        if candidate.get("selected") is True:
            for dependency_id in expected_blockers:
                state = dependencies[dependency_id].get("state")
                if state not in BLOCKING_STATES:
                    errors.append(
                        f"{context} has unexpected non-PROVEN dependency state {state!r}"
                    )

    for duplicate in _duplicate_ids(candidate_ids):
        errors.append(f"duplicate candidate id: {duplicate}")

    _validate_string_list(
        graph.get("non_claims"), "root.non_claims", errors, nonempty=True
    )
    return sorted(set(errors))


def selected_blockers(graph: Mapping[str, Any]) -> dict[str, list[str]]:
    """Return selected candidates with their declared blockers."""

    blocked: dict[str, list[str]] = {}
    candidates = graph.get("candidates", [])
    if not isinstance(candidates, list):
        return blocked
    for candidate in candidates:
        if not isinstance(candidate, dict) or candidate.get("selected") is not True:
            continue
        candidate_id = candidate.get("id")
        blockers = candidate.get("blockers")
        if isinstance(candidate_id, str) and isinstance(blockers, list) and blockers:
            blocked[candidate_id] = list(blockers)
    return dict(sorted(blocked.items()))


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_source_graph(
    decision_graph: Mapping[str, Any], source_path: Path
) -> list[str]:
    """Validate Research Kernel provenance and candidate synchronization."""

    errors: list[str] = []
    source_record = decision_graph.get("source_graph")
    if not isinstance(source_record, dict):
        return ["cannot validate source graph without root.source_graph"]
    if not source_path.is_file():
        return [f"source graph does not exist: {source_path}"]

    expected_digest = source_record.get("sha256")
    actual_digest = _sha256(source_path)
    if actual_digest != expected_digest:
        errors.append(
            f"source graph digest mismatch: expected {expected_digest}, got {actual_digest}"
        )
    try:
        source = json.loads(source_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        return errors + [f"cannot decode source graph: {exc}"]
    if not isinstance(source, dict):
        return errors + ["source graph root must be an object"]
    if source.get("schema") != source_record.get("schema"):
        errors.append("source graph schema does not match decision provenance")

    source_graph = source.get("graph")
    if not isinstance(source_graph, dict):
        return errors + ["source graph.graph must be an object"]
    if source_graph.get("run_id") != source_record.get("run_id"):
        errors.append("source graph run_id does not match decision provenance")
    atoms = source_graph.get("atoms")
    if not isinstance(atoms, list):
        return errors + ["source graph.graph.atoms must be a list"]
    hypotheses = {
        atom.get("id"): atom
        for atom in atoms
        if isinstance(atom, dict)
        and atom.get("type") == "HYPOTHESIS"
        and isinstance(atom.get("id"), str)
    }

    candidates = decision_graph.get("candidates", [])
    if not isinstance(candidates, list):
        return errors
    for candidate in candidates:
        if not isinstance(candidate, dict) or candidate.get("origin") != "research_kernel":
            continue
        candidate_id = candidate.get("id")
        source_atom = hypotheses.get(candidate_id)
        if source_atom is None:
            errors.append(
                f"research_kernel candidate {candidate_id!r} is absent from source graph"
            )
            continue
        if candidate.get("content") != source_atom.get("content"):
            errors.append(
                f"research_kernel candidate {candidate_id!r} content differs from source graph"
            )
        source_selected = bool(
            isinstance(source_atom.get("metadata"), dict)
            and source_atom["metadata"].get("selected_for_pr") is True
        )
        if candidate.get("selected") is not source_selected:
            errors.append(
                f"research_kernel candidate {candidate_id!r} selected flag differs from source graph"
            )
    return sorted(set(errors))


def _load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_source_path(
    graph: Mapping[str, Any], explicit: Path | None
) -> Path | None:
    if explicit is not None:
        return explicit
    source = graph.get("source_graph")
    if not isinstance(source, dict) or not isinstance(source.get("path"), str):
        return None
    return Path(source["path"])


def _emit_json(
    *,
    ok: bool,
    errors: Sequence[str],
    blocked: Mapping[str, Sequence[str]],
    admission: bool,
) -> None:
    print(
        json.dumps(
            {
                "ok": ok,
                "admission_requested": admission,
                "errors": list(errors),
                "selected_blockers": blocked,
            },
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", type=Path, help="decision graph JSON")
    parser.add_argument(
        "--source-graph",
        type=Path,
        help="Research Kernel source graph; defaults to source_graph.path",
    )
    parser.add_argument(
        "--admission",
        action="store_true",
        help="exit 2 while any selected candidate is BLOCKED",
    )
    parser.add_argument(
        "--json", action="store_true", help="emit one machine-readable JSON result"
    )
    args = parser.parse_args(argv)

    try:
        loaded = _load_json(args.graph)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        if args.json:
            _emit_json(ok=False, errors=[str(exc)], blocked={}, admission=args.admission)
        else:
            print(f"invalid decision graph: {exc}", file=sys.stderr)
        return 1

    errors = validate_graph(loaded)
    blocked: dict[str, list[str]] = {}
    if isinstance(loaded, dict):
        blocked = selected_blockers(loaded)
        source_path = _resolve_source_path(loaded, args.source_graph)
        if source_path is None:
            errors.append("source graph path cannot be resolved")
        else:
            errors.extend(validate_source_graph(loaded, source_path))
    errors = sorted(set(errors))

    if errors:
        if args.json:
            _emit_json(ok=False, errors=errors, blocked=blocked, admission=args.admission)
        else:
            for error in errors:
                print(f"ERROR: {error}", file=sys.stderr)
        return 1

    if args.admission and blocked:
        if args.json:
            _emit_json(ok=False, errors=[], blocked=blocked, admission=True)
        else:
            for candidate_id, candidate_blockers in blocked.items():
                print(
                    f"BLOCKED: {candidate_id}: {', '.join(candidate_blockers)}",
                    file=sys.stderr,
                )
        return 2

    if args.json:
        _emit_json(ok=True, errors=[], blocked=blocked, admission=args.admission)
    else:
        if blocked:
            print(
                "valid fail-closed graph; selected candidates remain blocked: "
                + ", ".join(blocked)
            )
        else:
            print("valid graph; all selected candidates are eligible")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

