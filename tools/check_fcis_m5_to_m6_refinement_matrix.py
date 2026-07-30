#!/usr/bin/env python3
"""Validate the FCIS M5-to-M6 theorem/runtime refinement matrix.

This checker is deliberately conservative. It validates the research ledger's
shape, exact pinned sources, assumption-to-runtime-producer coverage, status
evidence, cross references, canonical fingerprint, and Markdown completeness.
It does not execute Lean, Kani, Research Kernel, ESSO, Julia, SQLite, or the
ZenoDEX runtime and therefore cannot turn a GAP into authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "zenodex/fcis-m5-to-m6-refinement-matrix/v1"
STATUS_VALUES = {"PROVED", "IMPLEMENTED", "MOUNTED", "TESTED", "GAP"}
PRODUCER_STATUS_VALUES = STATUS_VALUES | {"NOT_APPLICABLE"}
GATE_ID_RE = re.compile(r"^(?:F|A|B|C|D|E|Z)-\d{2}$|^M6-\d{2}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")

REQUIRED_GATE_IDS = ['F-01', 'F-02', 'F-03', 'F-04', 'F-05', 'F-06', 'A-01', 'A-02', 'A-03', 'A-04', 'A-05', 'A-06', 'A-07', 'A-08', 'A-09', 'A-10', 'A-11', 'A-12', 'B-01', 'B-02', 'B-03', 'B-04', 'B-05', 'B-06', 'B-07', 'B-08', 'B-09', 'C-01', 'C-02', 'C-03', 'C-04', 'C-05', 'C-06', 'C-07', 'C-08', 'D-01', 'D-02', 'D-03', 'D-04', 'D-05', 'D-06', 'D-07', 'D-08', 'D-09', 'D-10', 'E-01', 'E-02', 'E-03', 'E-04', 'E-05', 'E-06', 'E-07', 'E-08', 'Z-01', 'Z-02', 'Z-03', 'Z-04', 'Z-05', 'Z-06', 'Z-07', 'M6-01', 'M6-02', 'M6-03', 'M6-04', 'M6-05', 'M6-06', 'M6-07', 'M6-08', 'M6-09', 'M6-10', 'M6-11']
PINNED_GIT_SOURCES = {'ZDX-B1B1-HEAD': '6c22f52c5e65f14b4501a62a049d231fd48aa2d3', 'ZDX-M5-REFERENCE': 'a2b570a8e5da043380ec1b3e43aab9932a42692f', 'ZDX-P4B3': '6c22f52c5e65f14b4501a62a049d231fd48aa2d3', 'ZDX-P4B5A-RESEARCH': '6771bff2d55ba08421b586e2db75441deb87f582', 'ZDX-NONCE-KANI': 'dab7e983eac92bb9edab13c59246d96b92214540', 'ZDX-NONCE-DRIFT': '73f18fa801cc2878257ecd4281e4b877da14caab', 'ZDX-LEAN-LEDGER': '3c5ee8b7487048a2dd0a370a64eeb1c294cd9c04', 'ZDX-RK-SYNTHESIS': '8e732fb15635fde35448ddef162b7dfd9a6b6560', 'ZDX-ZUSD-COVER': '206c287ccaea4a427c9c37679b99c5249a174d01', 'ZDX-ZUSD-FRESHNESS': '56a51be326487037919e1fd09e02724c013a5f31', 'ZDX-ZUSD-CAP': '6ba8e2606a2a4f6a1734c9019dcf4a2715516a45', 'ZFCIS-RC-HEAD': '9d0814ec769c0a36261477299df5dd5ecbcbf9f7'}

REQUIRED_TOP_LEVEL = {
    "schema",
    "title",
    "date",
    "repository",
    "matrix_branch_base",
    "scope",
    "target_runtime_obligation",
    "status_semantics",
    "status_counts",
    "source_baselines",
    "required_gate_ids",
    "gates",
    "composition_verdict",
    "research_method",
    "dependency_semantics",
    "matrix_fingerprint",
}

REQUIRED_GATE_FIELDS = {
    "id",
    "group",
    "title",
    "scope",
    "exact_safety_claim",
    "existing_proof_or_evidence",
    "theorem_assumptions",
    "runtime_assumption_producers",
    "authenticated_source",
    "current_state_and_commit_relation",
    "minimized_counterexample",
    "existing_executable_evidence",
    "missing_executable_evidence",
    "status",
    "status_evidence",
    "smallest_closing_artifact",
    "dependencies",
    "nonclaims",
    "status_rationale",
}

EXPECTED_GROUP_BY_PREFIX = {
    "F": "FOUNDATION",
    "A": "P4B5A",
    "B": "P4B5B",
    "C": "P4B5C",
    "D": "P4B5D",
    "E": "P4B5E",
    "Z": "ZUSD-P0",
    "M6": "M6",
}

FORBIDDEN_LOCAL_MARKERS = ("/tmp/", "/home/", "file://", "TBD", "TODO")


class DuplicateKeyError(ValueError):
    """Raised when JSON contains a duplicate object key."""


def _no_duplicate_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ValueError(f"cannot read matrix {path}: {exc}") from exc
    try:
        value = json.loads(raw, object_pairs_hook=_no_duplicate_object)
    except (json.JSONDecodeError, DuplicateKeyError) as exc:
        raise ValueError(f"invalid matrix JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError("matrix root must be a JSON object")
    return value


def canonical_fingerprint(matrix: dict[str, Any]) -> str:
    body = dict(matrix)
    body.pop("matrix_fingerprint", None)
    encoded = json.dumps(
        body,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _nonempty_string_list(value: Any) -> bool:
    return (
        isinstance(value, list)
        and bool(value)
        and all(_nonempty_string(item) for item in value)
    )


def _require_keys(
    obj: Any,
    required: Iterable[str],
    context: str,
    errors: list[str],
) -> bool:
    if not isinstance(obj, dict):
        errors.append(f"{context} must be an object")
        return False
    missing = sorted(set(required) - set(obj))
    if missing:
        errors.append(f"{context} missing fields: {', '.join(missing)}")
        return False
    return True


def _prefix(gate_id: str) -> str:
    return "M6" if gate_id.startswith("M6-") else gate_id.split("-", 1)[0]


def validate_matrix(matrix: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    _require_keys(matrix, REQUIRED_TOP_LEVEL, "matrix", errors)
    if matrix.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA!r}")

    if matrix.get("required_gate_ids") != REQUIRED_GATE_IDS:
        errors.append(
            "required_gate_ids must exactly equal the checker-pinned ordered gate set"
        )

    scope = matrix.get("scope")
    if isinstance(scope, dict):
        for key in (
            "runtime_implementation_authorized",
            "runtime_mount_authorized",
            "authority_switch_authorized",
            "production_behavior_changed",
        ):
            if scope.get(key) is not False:
                errors.append(f"scope.{key} must remain false for this research-only packet")
    else:
        errors.append("scope must be an object")

    target = matrix.get("target_runtime_obligation")
    for term in (
        "RuntimeAccept",
        "Authenticated",
        "DecodeCanonical",
        "StoreCurrent",
        "RuntimeResult=step",
        "ProjectLawsSatisfied",
        "AtomicCommit",
        "NoBypass",
    ):
        if not _nonempty_string(target) or term not in target:
            errors.append(f"target_runtime_obligation must contain {term!r}")

    status_semantics = matrix.get("status_semantics")
    if not isinstance(status_semantics, dict) or set(status_semantics) != STATUS_VALUES:
        errors.append("status_semantics must define exactly all five status values")
    elif not all(_nonempty_string(status_semantics[s]) for s in STATUS_VALUES):
        errors.append("every status semantic must be a nonempty string")

    sources = matrix.get("source_baselines")
    source_map: dict[str, dict[str, Any]] = {}
    if not isinstance(sources, list):
        errors.append("source_baselines must be a list")
        sources = []
    for index, source in enumerate(sources):
        context = f"source_baselines[{index}]"
        if not isinstance(source, dict):
            errors.append(f"{context} must be an object")
            continue
        source_id = source.get("id")
        if not _nonempty_string(source_id):
            errors.append(f"{context}.id must be nonempty")
            continue
        if source_id in source_map:
            errors.append(f"duplicate source id {source_id}")
        source_map[source_id] = source
        kind = source.get("kind")
        if kind == "git":
            repository = source.get("repository")
            commit = source.get("commit")
            if not _nonempty_string(repository) or repository.count("/") != 1:
                errors.append(f"{context}.repository must be owner/name")
            if not isinstance(commit, str) or not COMMIT_RE.fullmatch(commit):
                errors.append(f"{context}.commit must be a full lowercase 40-hex SHA")
        elif kind not in {"literature", "web"}:
            errors.append(f"{context}.kind must be git, literature, or web")

    for source_id, expected_commit in PINNED_GIT_SOURCES.items():
        source = source_map.get(source_id)
        if source is None:
            errors.append(f"missing checker-pinned source {source_id}")
        elif source.get("commit") != expected_commit:
            errors.append(
                f"source {source_id} commit changed: expected {expected_commit}, "
                f"found {source.get('commit')}"
            )

    gates = matrix.get("gates")
    if not isinstance(gates, list):
        errors.append("gates must be a list")
        gates = []

    seen_gate_ids: list[str] = []
    gate_map: dict[str, dict[str, Any]] = {}

    for index, gate in enumerate(gates):
        context = f"gates[{index}]"
        if not _require_keys(gate, REQUIRED_GATE_FIELDS, context, errors):
            continue
        gate_id = gate.get("id")
        if not isinstance(gate_id, str) or not GATE_ID_RE.fullmatch(gate_id):
            errors.append(f"{context}.id has invalid format")
            continue
        if gate_id in gate_map:
            errors.append(f"duplicate gate id {gate_id}")
        gate_map[gate_id] = gate
        seen_gate_ids.append(gate_id)

        expected_group = EXPECTED_GROUP_BY_PREFIX[_prefix(gate_id)]
        if gate.get("group") != expected_group:
            errors.append(
                f"{gate_id} group must be {expected_group}, found {gate.get('group')}"
            )

        for field in ("title", "scope", "exact_safety_claim", "status_rationale"):
            if not _nonempty_string(gate.get(field)):
                errors.append(f"{gate_id}.{field} must be a nonempty string")

        if len(str(gate.get("exact_safety_claim", ""))) < 80:
            errors.append(f"{gate_id} exact_safety_claim is too short to be auditable")

        status = gate.get("status")
        if status not in STATUS_VALUES:
            errors.append(f"{gate_id} has invalid status {status!r}")

        status_evidence = gate.get("status_evidence")
        if not _require_keys(
            status_evidence,
            ("proved", "implemented", "mounted", "tested", "gap"),
            f"{gate_id}.status_evidence",
            errors,
        ):
            status_evidence = {}
        else:
            for key in ("proved", "implemented", "mounted", "tested", "gap"):
                if not isinstance(status_evidence.get(key), bool):
                    errors.append(f"{gate_id}.status_evidence.{key} must be boolean")

        if status_evidence.get("gap") is not (status == "GAP"):
            errors.append(f"{gate_id} gap flag must be true exactly when status is GAP")
        if status_evidence.get("mounted") is not (status == "MOUNTED"):
            errors.append(
                f"{gate_id} mounted flag must be true exactly when status is MOUNTED"
            )
        if status == "PROVED" and not status_evidence.get("proved"):
            errors.append(f"{gate_id} status PROVED requires proved evidence")
        if status == "IMPLEMENTED" and not status_evidence.get("implemented"):
            errors.append(f"{gate_id} status IMPLEMENTED requires implementation evidence")
        if status == "TESTED":
            if not status_evidence.get("implemented") or not status_evidence.get("tested"):
                errors.append(
                    f"{gate_id} status TESTED requires implemented=true and tested=true"
                )
        if status == "MOUNTED":
            if not status_evidence.get("implemented") or not status_evidence.get("tested"):
                errors.append(
                    f"{gate_id} status MOUNTED requires implemented and tested evidence"
                )
            if isinstance(scope, dict) and scope.get("runtime_mount_authorized") is not True:
                errors.append(f"{gate_id} cannot be MOUNTED in a no-mount research packet")

        existing_exec = gate.get("existing_executable_evidence")
        missing_exec = gate.get("missing_executable_evidence")
        if not isinstance(existing_exec, list) or not all(
            _nonempty_string(item) for item in existing_exec
        ):
            errors.append(
                f"{gate_id}.existing_executable_evidence must be a list of nonempty strings"
            )
        if status_evidence.get("tested") and not existing_exec:
            errors.append(f"{gate_id} tested evidence requires executable evidence")
        if status == "GAP" and not _nonempty_string_list(missing_exec):
            errors.append(f"{gate_id} GAP requires missing executable evidence")
        elif not isinstance(missing_exec, list) or not all(
            _nonempty_string(item) for item in missing_exec
        ):
            errors.append(
                f"{gate_id}.missing_executable_evidence must be a list of strings"
            )

        proof_records = gate.get("existing_proof_or_evidence")
        if not isinstance(proof_records, list):
            errors.append(f"{gate_id}.existing_proof_or_evidence must be a list")
            proof_records = []
        for pindex, proof in enumerate(proof_records):
            pcontext = f"{gate_id}.existing_proof_or_evidence[{pindex}]"
            if not _require_keys(
                proof,
                ("kind", "source_id", "path", "symbol_or_section", "establishes"),
                pcontext,
                errors,
            ):
                continue
            if proof.get("source_id") not in source_map:
                errors.append(
                    f"{pcontext} references unknown source {proof.get('source_id')}"
                )
            for field in ("kind", "path", "establishes"):
                if not _nonempty_string(proof.get(field)):
                    errors.append(f"{pcontext}.{field} must be nonempty")

        if status_evidence.get("proved"):
            proof_words = " ".join(
                str(proof.get("kind", "")) + " " + str(proof.get("establishes", ""))
                for proof in proof_records
                if isinstance(proof, dict)
            ).lower()
            if not any(word in proof_words for word in ("lean", "kani", "proof", "theorem")):
                errors.append(
                    f"{gate_id} proved evidence lacks a theorem/proof/Kani/Lean record"
                )

        assumptions = gate.get("theorem_assumptions")
        producers = gate.get("runtime_assumption_producers")
        if not isinstance(assumptions, list) or not assumptions:
            errors.append(f"{gate_id} must declare at least one theorem/runtime assumption")
            assumptions = []
        if not isinstance(producers, list):
            errors.append(f"{gate_id}.runtime_assumption_producers must be a list")
            producers = []

        assumption_ids: list[str] = []
        for aindex, assumption in enumerate(assumptions):
            acontext = f"{gate_id}.theorem_assumptions[{aindex}]"
            if not _require_keys(assumption, ("id", "statement"), acontext, errors):
                continue
            aid = assumption.get("id")
            if not isinstance(aid, str) or not re.fullmatch(r"A[1-9][0-9]*", aid):
                errors.append(f"{acontext}.id must match A1, A2, ...")
            else:
                assumption_ids.append(aid)
            if not _nonempty_string(assumption.get("statement")):
                errors.append(f"{acontext}.statement must be nonempty")
        if len(assumption_ids) != len(set(assumption_ids)):
            errors.append(f"{gate_id} has duplicate assumption ids")

        producer_ids: list[str] = []
        for pindex, producer in enumerate(producers):
            pcontext = f"{gate_id}.runtime_assumption_producers[{pindex}]"
            if not _require_keys(
                producer,
                (
                    "assumption_id",
                    "required_runtime_producer",
                    "authenticated_source",
                    "current_evidence",
                    "status",
                ),
                pcontext,
                errors,
            ):
                continue
            producer_ids.append(str(producer.get("assumption_id")))
            if producer.get("status") not in PRODUCER_STATUS_VALUES:
                errors.append(f"{pcontext} has invalid status")
            for field in (
                "required_runtime_producer",
                "authenticated_source",
                "current_evidence",
            ):
                if not _nonempty_string(producer.get(field)):
                    errors.append(f"{pcontext}.{field} must be nonempty")

        if Counter(assumption_ids) != Counter(producer_ids):
            errors.append(
                f"{gate_id} assumptions and runtime producers must be a one-to-one ID match"
            )

        for relation_field in ("authenticated_source", "current_state_and_commit_relation"):
            relation = gate.get(relation_field)
            if not _require_keys(
                relation,
                ("required_relation", "current_evidence", "status"),
                f"{gate_id}.{relation_field}",
                errors,
            ):
                continue
            if relation.get("status") not in PRODUCER_STATUS_VALUES:
                errors.append(f"{gate_id}.{relation_field} has invalid status")
            if not _nonempty_string(relation.get("required_relation")):
                errors.append(f"{gate_id}.{relation_field}.required_relation empty")
            if not _nonempty_string(relation.get("current_evidence")):
                errors.append(f"{gate_id}.{relation_field}.current_evidence empty")

        cex = gate.get("minimized_counterexample")
        if _require_keys(
            cex,
            ("id", "description", "minimal_witness", "source_id"),
            f"{gate_id}.minimized_counterexample",
            errors,
        ):
            for field in ("id", "description", "minimal_witness", "source_id"):
                if not _nonempty_string(cex.get(field)):
                    errors.append(
                        f"{gate_id}.minimized_counterexample.{field} must be nonempty"
                    )
            if cex.get("source_id") not in source_map:
                errors.append(
                    f"{gate_id} counterexample references unknown source "
                    f"{cex.get('source_id')}"
                )

        closing = gate.get("smallest_closing_artifact")
        if _require_keys(
            closing,
            ("artifact_type", "suggested_path", "acceptance_condition"),
            f"{gate_id}.smallest_closing_artifact",
            errors,
        ):
            for field in ("artifact_type", "suggested_path", "acceptance_condition"):
                if not _nonempty_string(closing.get(field)):
                    errors.append(
                        f"{gate_id}.smallest_closing_artifact.{field} must be nonempty"
                    )

        dependencies = gate.get("dependencies")
        if not isinstance(dependencies, list) or not all(
            isinstance(dep, str) for dep in dependencies
        ):
            errors.append(f"{gate_id}.dependencies must be a string list")
        elif len(dependencies) != len(set(dependencies)):
            errors.append(f"{gate_id} has duplicate dependencies")

        if not isinstance(gate.get("nonclaims"), list) or not all(
            _nonempty_string(item) for item in gate.get("nonclaims", [])
        ):
            errors.append(f"{gate_id}.nonclaims must be a list of nonempty strings")

    if seen_gate_ids != REQUIRED_GATE_IDS:
        errors.append("gates must exactly match the checker-pinned ordered gate set")
    for gate_id, gate in gate_map.items():
        for dep in gate.get("dependencies", []):
            if dep == gate_id:
                errors.append(f"{gate_id} cannot depend on itself")
            elif dep not in gate_map:
                errors.append(f"{gate_id} dependency {dep} does not exist")

    calculated_counts = Counter(
        gate.get("status") for gate in gates if isinstance(gate, dict)
    )
    expected_counts = {status: calculated_counts.get(status, 0) for status in STATUS_VALUES}
    if matrix.get("status_counts") != expected_counts:
        errors.append(
            f"status_counts mismatch: expected {expected_counts}, "
            f"found {matrix.get('status_counts')}"
        )

    verdict = matrix.get("composition_verdict")
    if isinstance(verdict, dict):
        if verdict.get("status") != "GAP":
            errors.append("composition_verdict.status must remain GAP")
        if verdict.get("mounted_gate_count") != 0:
            errors.append("composition_verdict.mounted_gate_count must be zero")
        if not _nonempty_string(verdict.get("summary")):
            errors.append("composition_verdict.summary must be nonempty")
        if not _nonempty_string_list(verdict.get("highest_leverage_closure_sequence")):
            errors.append(
                "composition_verdict.highest_leverage_closure_sequence must be nonempty"
            )
    else:
        errors.append("composition_verdict must be an object")

    expected_fingerprint = canonical_fingerprint(matrix)
    if matrix.get("matrix_fingerprint") != expected_fingerprint:
        errors.append(
            "matrix_fingerprint mismatch: "
            f"expected {expected_fingerprint}, found {matrix.get('matrix_fingerprint')}"
        )

    serialized = json.dumps(matrix, ensure_ascii=False)
    for marker in FORBIDDEN_LOCAL_MARKERS:
        if marker in serialized:
            errors.append(f"matrix contains forbidden local/placeholder marker {marker!r}")

    return errors


def validate_markdown(
    matrix: dict[str, Any],
    markdown_path: Path,
) -> list[str]:
    errors: list[str] = []
    try:
        text = markdown_path.read_text(encoding="utf-8")
    except OSError as exc:
        return [f"cannot read Markdown {markdown_path}: {exc}"]

    fingerprint = matrix.get("matrix_fingerprint")
    if f"Matrix fingerprint: `{fingerprint}`" not in text:
        errors.append("Markdown does not contain the exact matrix fingerprint")
    gates = matrix.get("gates", [])
    if f"Gate count: `{len(gates)}`" not in text:
        errors.append("Markdown does not contain the exact gate count")

    for status, count in sorted(matrix.get("status_counts", {}).items()):
        marker = f"| {status} | {count} |"
        if marker not in text:
            errors.append(f"Markdown status table missing {marker}")

    for gate in gates:
        gate_id = gate["id"]
        title = gate["title"]
        heading = f"### {gate_id} — {title}"
        if heading not in text:
            errors.append(f"Markdown missing exact gate heading {heading!r}")

    for marker in FORBIDDEN_LOCAL_MARKERS:
        if marker in text:
            errors.append(f"Markdown contains forbidden local/placeholder marker {marker!r}")

    return errors


def emit_report(errors: list[str], as_json: bool) -> None:
    if as_json:
        print(
            json.dumps(
                {
                    "schema": "zenodex/fcis-m5-to-m6-refinement-matrix-check/v1",
                    "ok": not errors,
                    "error_count": len(errors),
                    "errors": errors,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return
    if errors:
        print(f"FCIS M5-to-M6 refinement matrix: FAIL ({len(errors)} errors)")
        for error in errors:
            print(f"- {error}")
    else:
        print("FCIS M5-to-M6 refinement matrix: PASS")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--matrix",
        type=Path,
        default=Path("docs/research/FCIS_M5_TO_M6_REFINEMENT_MATRIX.json"),
    )
    parser.add_argument(
        "--markdown",
        type=Path,
        default=Path("docs/research/FCIS_M5_TO_M6_REFINEMENT_MATRIX.md"),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit a machine-readable validation report",
    )
    parser.add_argument(
        "--skip-markdown",
        action="store_true",
        help="validate only the JSON matrix",
    )
    args = parser.parse_args()

    errors: list[str] = []
    try:
        matrix = load_json(args.matrix)
    except ValueError as exc:
        errors.append(str(exc))
        emit_report(errors, args.json)
        return 1

    errors.extend(validate_matrix(matrix))
    if not args.skip_markdown:
        errors.extend(validate_markdown(matrix, args.markdown))

    emit_report(errors, args.json)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
