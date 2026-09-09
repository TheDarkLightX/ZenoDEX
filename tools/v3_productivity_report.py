#!/usr/bin/env python3
"""Render a bounded, offline, source-recorded V3 productivity report.

The manifest is closed-schema metadata.  This tool only reads Git objects named
by pinned references and never executes a manifest-supplied command.  It checks
bytes, JSON-pointer observations, commit ranges, and the fixed V3 assessment
calculator.  Its output is advisory: it does not authenticate a model identity,
verify execution or billing, certify acceptance, close an obligation, or grant
release or value-movement authority.

Usage:
    python3 tools/v3_productivity_report.py MANIFEST [--root PATH]
        [--baseline-manifest-commit SHA]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import NoReturn, cast

if __package__:
    from tools import check_v3_progress as progress
    from tools import v3_progress_assessment_calc as assessment_calculator
else:
    import check_v3_progress as progress
    import v3_progress_assessment_calc as assessment_calculator

MANIFEST_SCHEMA = "zenodex/v3-productivity/v1"
REPORT_SCHEMA = "zenodex/v3-productivity-report/v1"
ADVISORY = (
    "Source-recorded advisory metadata only; it does not authenticate model identity, "
    "execution, billing, certified acceptance, obligation closure, qualification, "
    "release, or value-movement authority."
)
CLAIM_CEILING = (
    "Pinned references establish only source-byte integrity.",
    "Reported models and resources remain declarations; missing data remains unknown.",
    "Score percentages remain reviewer judgments and never qualify the product.",
)
ROLES = frozenset({"implementation", "review", "integration", "verification", "research"})
RUN_STATUSES = frozenset({"completed", "failed", "cancelled", "no_change", "unknown"})
RISKS = frozenset({"critical", "standard"})
BATCH_KINDS = frozenset({"implementation", "repair", "support", "review"})
DISPOSITIONS = frozenset(
    {"accepted_partial", "support_only", "rejected", "reopened", "unassessed"}
)
FINDING_STATUSES = frozenset({"confirmed", "repaired", "reopened"})
RESOURCE_FIELDS = ("input_tokens", "output_tokens", "elapsed_ms", "cost_microusd")
LINE_CATEGORIES = ("runtime", "proof", "tests", "tooling", "config", "data", "docs", "lockfile", "other")
TASK_IDS = frozenset(f"W{number:02d}" for number in range(14))
MAX_REFERENCE_BYTES = 4_194_304
RUNTIME_SUFFIXES = frozenset({".c", ".cc", ".cpp", ".go", ".h", ".hpp", ".java", ".js", ".jsx", ".kt", ".py", ".rs", ".sol", ".ts", ".tsx", ".zig"})
PROOF_SUFFIXES = frozenset({".als", ".ivy", ".lean", ".tau", ".tla"})
LOCK_NAMES = frozenset({"Cargo.lock", "Pipfile.lock", "poetry.lock", "yarn.lock"})


class ProductivityReject(ValueError):
    """A closed-schema, source-binding, or accounting failure."""

    def __init__(self, code: str, detail: str = "") -> None:
        super().__init__(detail)
        self.code = code
        self.detail = detail


def _reject(code: str, detail: str = "") -> NoReturn:
    raise ProductivityReject(code, detail)


def _require(condition: bool, code: str, detail: str = "") -> None:
    if not condition:
        _reject(code, detail)


def _object(value: object, fields: tuple[str, ...], code: str) -> dict[str, object]:
    _require(type(value) is dict and set(value) == set(fields), code, "closed field set")
    return cast(dict[str, object], value)


def _text(value: object, code: str, maximum: int = 4096) -> str:
    _require(type(value) is str and 0 < len(value) <= maximum, code, "text required")
    return cast(str, value)


def _strings(value: object, code: str, *, allow_empty: bool) -> list[str]:
    _require(type(value) is list, code, "list required")
    result = [_text(item, code) for item in cast(list[object], value)]
    _require((allow_empty or bool(result)) and len(result) == len(set(result)), code, "unique strings")
    return result


def _finite(value: object) -> None:
    if type(value) is float and not math.isfinite(value):
        _reject("NONFINITE_JSON")
    if type(value) is dict:
        for item in cast(dict[object, object], value).values():
            _finite(item)
    elif type(value) is list:
        for item in cast(list[object], value):
            _finite(item)


def _decode_json(raw: bytes, label: str) -> object:
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=progress._without_duplicate_keys,
            parse_constant=progress._reject_nonfinite,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as error:
        _reject("MALFORMED_JSON", f"{label}: {type(error).__name__}")
    try:
        _finite(value)
    except RecursionError:
        _reject("MALFORMED_JSON", label)
    return value


def _load_manifest(path: Path) -> dict[str, object]:
    try:
        data = progress._load_object(path, maximum=progress.MAX_JSON_BYTES, label="MANIFEST")
    except progress.ProgressReject as error:
        _reject(error.code, error.detail)
    _finite(data)
    return data


class _Sources:
    """Cache safe Git reads while recording every successful pinned reference."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self._blobs: dict[tuple[str, str], bytes] = {}
        self._json: dict[tuple[str, str], object] = {}
        self._commits: set[str] = set()
        self._unique_refs: set[tuple[str, str, str]] = set()
        self.ref_occurrences = 0
        self.pointer_observations = 0

    def require_commit(self, commit: str) -> None:
        if commit not in self._commits:
            progress._require_commit(self.root, commit)
            self._commits.add(commit)

    def reference(self, value: object, code: str) -> dict[str, str]:
        reference = _object(value, ("commit", "path", "sha256"), code)
        commit = progress._commit(reference["commit"], code)
        path = progress._safe_path(reference["path"], code)
        digest = progress._hash(reference["sha256"], code)
        self.require_commit(commit)
        key = (commit, path)
        if key not in self._blobs:
            blob = progress._git_blob(self.root, commit, path)
            _require(blob is not None, "MISSING_PINNED_BLOB", f"{commit}:{path}")
            _require(len(blob) <= MAX_REFERENCE_BYTES, "REFERENCE_SIZE", path)
            self._blobs[key] = blob
        _require(hashlib.sha256(self._blobs[key]).hexdigest() == digest, "STALE_PINNED_EVIDENCE", path)
        self.ref_occurrences += 1
        self._unique_refs.add((commit, path, digest))
        return {"commit": commit, "path": path, "sha256": digest}

    def nullable_reference(self, value: object, code: str) -> dict[str, str] | None:
        if value is None:
            return None
        return self.reference(value, code)

    def json_value(self, reference: dict[str, str], code: str) -> object:
        key = (reference["commit"], reference["path"])
        if key not in self._json:
            self._json[key] = _decode_json(self._blobs[key], code)
        return self._json[key]

    def declared_subject(self, reference: dict[str, str]) -> str | None:
        """Read an explicit JSON subject without treating storage as subject evidence."""
        if not reference["path"].endswith(".json"):
            return None
        try:
            value = self.json_value(reference, "SOURCE_CORRESPONDENCE_JSON")
        except (ProductivityReject, progress.ProgressReject):
            return None
        if type(value) is not dict:
            return None
        mapping = cast(dict[str, object], value)
        for field in ("subject", "subject_commit"):
            candidate = mapping.get(field)
            if type(candidate) is str:
                return candidate
        replay = mapping.get("mutation_replay")
        if type(replay) is dict and type(cast(dict[str, object], replay).get("subject_commit")) is str:
            return cast(str, cast(dict[str, object], replay)["subject_commit"])
        return None

    def integrity(self) -> dict[str, object]:
        return {
            "status": "ALL_REFERENCED_BLOBS_HASH_MATCH",
            "pinned_reference_occurrences": self.ref_occurrences,
            "unique_pinned_references": len(self._unique_refs),
            "json_pointer_observations_verified": self.pointer_observations,
        }


def _pointer_tokens(pointer: str) -> list[str]:
    if pointer == "":
        return []
    _require(pointer.startswith("/"), "JSON_POINTER", "RFC6901 pointer must start with slash")
    tokens: list[str] = []
    for encoded in pointer[1:].split("/"):
        decoded: list[str] = []
        index = 0
        while index < len(encoded):
            character = encoded[index]
            if character != "~":
                decoded.append(character)
                index += 1
                continue
            _require(index + 1 < len(encoded) and encoded[index + 1] in "01", "JSON_POINTER")
            decoded.append("~" if encoded[index + 1] == "0" else "/")
            index += 2
        tokens.append("".join(decoded))
    return tokens


def _resolve_pointer(value: object, pointer: str) -> object:
    current = value
    for token in _pointer_tokens(pointer):
        if type(current) is dict:
            mapping = cast(dict[str, object], current)
            _require(token in mapping, "JSON_POINTER_MISSING", pointer)
            current = mapping[token]
            continue
        if type(current) is list:
            _require(
                re.fullmatch(r"0|[1-9][0-9]*", token) is not None,
                "JSON_POINTER_INDEX",
                pointer,
            )
            index = int(token)
            items = cast(list[object], current)
            _require(index < len(items), "JSON_POINTER_MISSING", pointer)
            current = items[index]
            continue
        _reject("JSON_POINTER_MISSING", pointer)
    return current


def _observation(value: object, sources: _Sources, code: str) -> dict[str, object] | None:
    if value is None:
        return None
    observation = _object(value, ("value", "evidence", "json_pointer"), code)
    amount = observation["value"]
    _require(type(amount) is int and amount >= 0, "OBSERVATION_VALUE", code)
    evidence = sources.reference(observation["evidence"], code)
    _require(
        type(observation["json_pointer"]) is str and len(observation["json_pointer"]) <= 4096,
        "JSON_POINTER",
    )
    pointer = cast(str, observation["json_pointer"])
    observed = _resolve_pointer(sources.json_value(evidence, "OBSERVATION_JSON"), pointer)
    _require(
        type(observed) is int and observed >= 0 and observed == amount,
        "OBSERVATION_MISMATCH",
        pointer,
    )
    sources.pointer_observations += 1
    return {"value": amount, "evidence": evidence, "json_pointer": pointer}


def _resources(value: object, sources: _Sources) -> dict[str, dict[str, object] | None]:
    resources = _object(value, RESOURCE_FIELDS, "RUN_RESOURCES")
    return {field: _observation(resources[field], sources, "OBSERVATION") for field in RESOURCE_FIELDS}


def _run(value: object, sources: _Sources) -> dict[str, object]:
    run = _object(
        value,
        ("id", "model_id", "role", "status", "task_kind", "risk", "provenance", "resources"),
        "RUN_FIELDS",
    )
    model = run["model_id"]
    _require(model is None or type(model) is str, "MODEL_ID")
    model_id = None if model is None else _text(model, "MODEL_ID", 256)
    role = _text(run["role"], "RUN_ROLE", 32)
    status = _text(run["status"], "RUN_STATUS", 32)
    risk = _text(run["risk"], "RUN_RISK", 32)
    _require(role in ROLES, "RUN_ROLE", role)
    _require(status in RUN_STATUSES, "RUN_STATUS", status)
    _require(risk in RISKS, "RUN_RISK", risk)
    provenance = sources.nullable_reference(run["provenance"], "RUN_PROVENANCE")
    return {
        "id": _text(run["id"], "RUN_ID", 128),
        "model_id": model_id,
        "model_declaration": (
            "SOURCE_RECORDED" if model_id is not None and provenance is not None else "UNVERIFIED_DECLARATION"
        ),
        "role": role,
        "status": status,
        "task_kind": _text(run["task_kind"], "RUN_TASK_KIND", 256),
        "risk": risk,
        "provenance": provenance,
        "resources": _resources(run["resources"], sources),
    }


def _score_summary(report: dict[str, object]) -> dict[str, object]:
    sections = cast(dict[str, object], report["sections"])
    result: dict[str, object] = {"subject": report["subject"]}
    for name in ("full_v3", "formal_core"):
        section = cast(dict[str, object], sections[name])
        result[name] = {
            "lower_percent": section["low_percent"],
            "central_percent": section["central_percent"],
            "upper_percent": section["high_percent"],
        }
    return result


def _assessment_score(
    reference: dict[str, str], expected_subject: str, sources: _Sources, label: str
) -> dict[str, object]:
    data = sources.json_value(reference, "ASSESSMENT_JSON")
    try:
        report = assessment_calculator.assess(data)
    except ValueError as error:
        _reject(str(error) or "ASSESSMENT_INVALID", label)
    _require(report["subject"] == expected_subject, "ASSESSMENT_SUBJECT", label)
    return _score_summary(report)


def _score_delta(before: dict[str, object], after: dict[str, object]) -> dict[str, object]:
    result: dict[str, object] = {}
    for name in ("full_v3", "formal_core"):
        old = cast(dict[str, float], before[name])
        new = cast(dict[str, float], after[name])
        result[name] = {
            "lower_percent_points": round(new["lower_percent"] - old["lower_percent"], 3),
            "central_percent_points": round(new["central_percent"] - old["central_percent"], 3),
            "upper_percent_points": round(new["upper_percent"] - old["upper_percent"], 3),
        }
    return result


def _assessment(value: object, before_commit: str, after_commit: str, sources: _Sources) -> dict[str, object]:
    assessment = _object(value, ("before", "after", "review"), "ASSESSMENT_FIELDS")
    before = sources.nullable_reference(assessment["before"], "ASSESSMENT_BEFORE")
    after = sources.nullable_reference(assessment["after"], "ASSESSMENT_AFTER")
    review = sources.nullable_reference(assessment["review"], "ASSESSMENT_REVIEW")
    if before is None:
        _require(after is None and review is None, "ASSESSMENT_PARTIAL_REFS")
        return {
            "status": "NOT_RESCORED",
            "before": None,
            "after": None,
            "review": None,
            "before_scores": None,
            "after_scores": None,
            "delta": None,
        }
    before_scores = _assessment_score(before, before_commit, sources, "before")
    if after is None:
        _require(review is None, "ASSESSMENT_PARTIAL_REFS")
        return {
            "status": "NOT_RESCORED",
            "before": before,
            "after": None,
            "review": None,
            "before_scores": before_scores,
            "after_scores": None,
            "delta": None,
        }
    _require(review is not None, "ASSESSMENT_PARTIAL_REFS")
    after_scores = _assessment_score(after, after_commit, sources, "after")
    return {
        "status": "REVIEWED_DELTA",
        "before": before,
        "after": after,
        "review": review,
        "before_scores": before_scores,
        "after_scores": after_scores,
        "delta": _score_delta(before_scores, after_scores),
    }


def _classify(path: str) -> str:
    candidate = Path(path)
    name = candidate.name
    suffix = candidate.suffix.lower()
    if name in LOCK_NAMES or suffix == ".lock" or name in {"package-lock.json", "pnpm-lock.yaml"}:
        return "lockfile"
    if suffix in {".csv", ".json", ".jsonl", ".tsv"}:
        return "data"
    if suffix in PROOF_SUFFIXES:
        return "proof"
    if suffix in {".md", ".rst"}:
        return "docs"
    if path.startswith((".github/", "config/")) or name in {
        ".gitignore",
        "pyproject.toml",
        "pytest.ini",
        "setup.cfg",
    } or suffix in {".toml", ".yaml", ".yml"}:
        return "config"
    if "tests" in candidate.parts or path.startswith(("tests/", "test/")) or name.startswith("test_"):
        return "tests"
    if path.startswith(("tools/", "scripts/", "testing/")):
        return "tooling"
    if suffix in RUNTIME_SUFFIXES:
        return "runtime"
    if path.startswith("docs/"):
        return "docs"
    if path.startswith(("data/", "generated/")):
        return "data"
    return "other"


def _empty_categories() -> dict[str, dict[str, int]]:
    return {
        category: {
            "added": 0,
            "deleted": 0,
            "net": 0,
            "file_count": 0,
            "binary_file_count": 0,
        }
        for category in LINE_CATEGORIES
    }


def _ancestor(root: Path, before: str, after: str) -> bool:
    try:
        progress._run_git(root, ["merge-base", "--is-ancestor", before, after], "ANCESTOR_QUERY")
    except progress.ProgressReject:
        return False
    return True


def _changed_again(root: Path, before: str, after: str) -> list[dict[str, object]]:
    if before == after:
        return []
    raw = progress._run_git(
        root,
        ["log", "--format=", "--name-only", "-z", f"{before}..{after}", "--"],
        "GIT_LOG_FAILURE",
    )
    counts: Counter[str] = Counter()
    for item in raw.split(b"\0"):
        if not item:
            continue
        path = item.decode("utf-8", "strict")
        progress._safe_path(path, "GIT_PATH")
        counts[path] += 1
    return [
        {"path": path, "commit_occurrence_count": count}
        for path, count in sorted(counts.items())
        if count > 1
    ]


def _diff(root: Path, before: str, after: str) -> dict[str, object]:
    categories = _empty_categories()
    if before == after:
        return {
            "commit_count": 0,
            "changed_file_count": 0,
            "changed_again_paths": [],
            "binary_file_count": 0,
            "categories": categories,
            "files": [],
        }
    try:
        changes = progress._changed_paths(root, before, after)
    except progress.ProgressReject as error:
        if error.code != "EMPTY_GIT_CHANGE":
            raise
        changes = []
    count_text = progress._run_git(root, ["rev-list", "--count", f"{before}..{after}"], "GIT_LOG_FAILURE")
    count = count_text.decode("ascii", "strict").strip()
    _require(count.isdecimal(), "GIT_LOG_FAILURE", "commit count")
    raw = progress._run_git(
        root,
        ["diff", "--numstat", "-z", "--no-renames", before, after, "--"],
        "GIT_DIFF_FAILURE",
    )
    files: list[dict[str, object]] = []
    for row in raw.split(b"\0"):
        if not row:
            continue
        parts = row.decode("utf-8", "strict").split("\t", 2)
        _require(len(parts) == 3, "GIT_DIFF_FAILURE", "numstat row")
        added_text, deleted_text, path = parts
        progress._safe_path(path, "GIT_PATH")
        category = _classify(path)
        totals = categories[category]
        if added_text == "-" or deleted_text == "-":
            _require(added_text == "-" and deleted_text == "-", "GIT_DIFF_FAILURE", path)
            totals["file_count"] += 1
            totals["binary_file_count"] += 1
            files.append(
                {
                    "path": path,
                    "category": category,
                    "added": None,
                    "deleted": None,
                    "net": None,
                    "physical_lines": "UNAVAILABLE_FOR_BINARY_FILE",
                }
            )
            continue
        _require(added_text.isdecimal() and deleted_text.isdecimal(), "GIT_DIFF_FAILURE", path)
        added, deleted = int(added_text), int(deleted_text)
        totals["added"] += added
        totals["deleted"] += deleted
        totals["net"] += added - deleted
        totals["file_count"] += 1
        files.append(
            {
                "path": path,
                "category": category,
                "added": added,
                "deleted": deleted,
                "net": added - deleted,
                "physical_lines": "AVAILABLE",
            }
        )
    return {
        "commit_count": int(count),
        "changed_file_count": len(changes),
        "changed_again_paths": _changed_again(root, before, after),
        "binary_file_count": sum(values["binary_file_count"] for values in categories.values()),
        "categories": categories,
        "files": sorted(files, key=lambda item: cast(str, item["path"])),
    }


def _outcome(value: object, sources: _Sources) -> dict[str, object]:
    outcome = _object(value, ("disposition", "summary", "evidence"), "OUTCOME_FIELDS")
    disposition = _text(outcome["disposition"], "OUTCOME_DISPOSITION", 32)
    _require(disposition in DISPOSITIONS, "OUTCOME_DISPOSITION", disposition)
    evidence = sources.nullable_reference(outcome["evidence"], "OUTCOME_EVIDENCE")
    _require(
        evidence is not None or disposition in {"support_only", "unassessed"},
        "OUTCOME_EVIDENCE_REQUIRED",
        disposition,
    )
    return {"disposition": disposition, "summary": _text(outcome["summary"], "OUTCOME_SUMMARY"), "evidence": evidence}


def _findings(value: object, sources: _Sources) -> list[dict[str, object]]:
    _require(type(value) is list, "BATCH_FINDINGS", "list required")
    result: list[dict[str, object]] = []
    identifiers: set[str] = set()
    for raw in cast(list[object], value):
        finding = _object(raw, ("id", "status", "evidence"), "FINDING_FIELDS")
        identifier = _text(finding["id"], "FINDING_ID", 128)
        status = _text(finding["status"], "FINDING_STATUS", 32)
        _require(identifier not in identifiers, "DUPLICATE_FINDING", identifier)
        _require(status in FINDING_STATUSES, "FINDING_STATUS", status)
        identifiers.add(identifier)
        result.append(
            {
                "id": identifier,
                "status": status,
                "evidence": sources.reference(finding["evidence"], "FINDING_EVIDENCE"),
            }
        )
    return result


def _correspondence(
    field: str, reference: dict[str, str] | None, expected_commit: str, sources: _Sources
) -> dict[str, object]:
    if reference is None:
        return {
            "field": field,
            "status": "UNKNOWN",
            "expected_commit": expected_commit,
            "declared_subject": None,
            "stored_commit": None,
        }
    declared_subject = sources.declared_subject(reference)
    return {
        "field": field,
        "status": (
            "MATCHES_EXPECTED_SUBJECT"
            if declared_subject == expected_commit
            else "HISTORICAL_SOURCE"
            if declared_subject is not None
            else "UNKNOWN"
        ),
        "expected_commit": expected_commit,
        "declared_subject": declared_subject,
        "stored_commit": reference["commit"],
    }


def _batch(
    value: object,
    sources: _Sources,
    run_ids: set[str],
    earlier_batches: set[str],
) -> dict[str, object]:
    batch = _object(
        value,
        (
            "id",
            "before_commit",
            "after_commit",
            "kind",
            "obligation_ids",
            "run_ids",
            "outcome",
            "assessment",
            "findings",
            "supersedes",
        ),
        "BATCH_FIELDS",
    )
    identifier = _text(batch["id"], "BATCH_ID", 128)
    before = progress._commit(batch["before_commit"], "BATCH_COMMIT")
    after = progress._commit(batch["after_commit"], "BATCH_COMMIT")
    sources.require_commit(before)
    sources.require_commit(after)
    _require(_ancestor(sources.root, before, after), "BEFORE_NOT_ANCESTOR", identifier)
    kind = _text(batch["kind"], "BATCH_KIND", 32)
    _require(kind in BATCH_KINDS, "BATCH_KIND", kind)
    obligations = _strings(batch["obligation_ids"], "OBLIGATION_IDS", allow_empty=False)
    _require(set(obligations) <= TASK_IDS, "UNKNOWN_OBLIGATION_ID", identifier)
    references = _strings(batch["run_ids"], "BATCH_RUN_IDS", allow_empty=True)
    _require(set(references) <= run_ids, "UNKNOWN_RUN_ID", identifier)
    supersedes = batch["supersedes"]
    _require(supersedes is None or type(supersedes) is str, "SUPERSEDES")
    superseding_id = None if supersedes is None else _text(supersedes, "SUPERSEDES", 128)
    _require(superseding_id is None or superseding_id in earlier_batches, "SUPERSEDES", identifier)
    outcome = _outcome(batch["outcome"], sources)
    assessment = _assessment(batch["assessment"], before, after, sources)
    findings = _findings(batch["findings"], sources)
    source_rows = [
        _correspondence("outcome.evidence", cast(dict[str, str] | None, outcome["evidence"]), after, sources),
        _correspondence("assessment.before", cast(dict[str, str] | None, assessment["before"]), before, sources),
        _correspondence("assessment.after", cast(dict[str, str] | None, assessment["after"]), after, sources),
        _correspondence("assessment.review", cast(dict[str, str] | None, assessment["review"]), after, sources),
    ]
    source_rows.extend(
        _correspondence(
            f"findings[{finding['id']}].evidence",
            cast(dict[str, str], finding["evidence"]),
            after,
            sources,
        )
        for finding in findings
    )
    return {
        "id": identifier,
        "before_commit": before,
        "after_commit": after,
        "kind": kind,
        "obligation_ids": obligations,
        "run_ids": references,
        "outcome": outcome,
        "assessment": assessment,
        "findings": findings,
        "supersedes": superseding_id,
        "source_correspondence": source_rows,
        "diff": _diff(sources.root, before, after),
    }


def _positive(delta: dict[str, object]) -> bool:
    return any(
        cast(float, cast(dict[str, object], delta[name])[band]) > 0
        for name in ("full_v3", "formal_core")
        for band in ("lower_percent_points", "central_percent_points", "upper_percent_points")
    )


def _ranges_overlap(root: Path, first: tuple[str, str], second: tuple[str, str]) -> bool:
    if first == second or first[1] == second[0] or second[1] == first[0]:
        return False
    return _ancestor(root, first[0], second[1]) and _ancestor(root, second[0], first[1])


def _ranges_ordered(root: Path, first: tuple[str, str], second: tuple[str, str]) -> bool:
    return _ancestor(root, first[1], second[0]) or _ancestor(root, second[1], first[0])


def _sum_categories(diffs: list[dict[str, object]]) -> dict[str, dict[str, int]]:
    total = _empty_categories()
    for diff in diffs:
        categories = cast(dict[str, dict[str, int]], diff["categories"])
        for category in LINE_CATEGORIES:
            for field in ("added", "deleted", "net", "file_count", "binary_file_count"):
                total[category][field] += categories[category][field]
    return total


def _resource_rollup(runs: list[dict[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for field in RESOURCE_FIELDS:
        observed: list[tuple[str, int]] = []
        unknown: list[str] = []
        for run in runs:
            observation = cast(dict[str, object] | None, cast(dict[str, object], run["resources"])[field])
            if observation is None:
                unknown.append(cast(str, run["id"]))
            else:
                observed.append((cast(str, run["id"]), cast(int, observation["value"])))
        result[field] = {
            "source_recorded_value_sum": sum(amount for _, amount in observed) if observed else None,
            "observed_run_count": len(observed),
            "unknown_run_count": len(unknown),
        }
    return result


def _unique_resource_observations(runs: list[dict[str, object]]) -> None:
    """One source JSON value cannot be declared as multiple resource quantities."""
    seen: set[tuple[str, str, str, str]] = set()
    for run in runs:
        resources = cast(dict[str, dict[str, object] | None], run["resources"])
        for field in RESOURCE_FIELDS:
            observation = resources[field]
            if observation is None:
                continue
            evidence = cast(dict[str, str], observation["evidence"])
            identity = (
                evidence["commit"],
                evidence["path"],
                evidence["sha256"],
                cast(str, observation["json_pointer"]),
            )
            _require(identity not in seen, "DUPLICATE_RESOURCE_OBSERVATION", cast(str, run["id"]))
            seen.add(identity)


def _finding_event_is_later(
    root: Path, candidate: dict[str, object], prior: dict[str, object]
) -> bool:
    candidate_range = (cast(str, candidate["before_commit"]), cast(str, candidate["after_commit"]))
    prior_range = (cast(str, prior["before_commit"]), cast(str, prior["after_commit"]))
    return candidate_range != prior_range and _ancestor(root, prior_range[1], candidate_range[0])


def _active_finding_quality(
    active: list[dict[str, object]], root: Path
) -> tuple[Counter[str], dict[str, list[str]], list[dict[str, object]]]:
    dispositions: Counter[str] = Counter()
    events_by_id: dict[str, list[dict[str, object]]] = defaultdict(list)
    for position, batch in enumerate(active):
        outcome = cast(dict[str, object], batch["outcome"])
        if outcome["evidence"] is not None:
            dispositions[cast(str, outcome["disposition"])] += 1
        for finding in cast(list[dict[str, object]], batch["findings"]):
            identifier = cast(str, finding["id"])
            events_by_id[identifier].append(
                {
                    "batch_id": batch["id"],
                    "before_commit": batch["before_commit"],
                    "after_commit": batch["after_commit"],
                    "status": finding["status"],
                    "evidence": finding["evidence"],
                    "declaration_order": position,
                }
            )
    finding_ids: dict[str, list[str]] = {status: [] for status in FINDING_STATUSES}
    lifecycle: list[dict[str, object]] = []
    for identifier, events in sorted(events_by_id.items()):
        latest = [
            candidate
            for candidate in events
            if not any(
                _finding_event_is_later(root, other, candidate)
                for other in events
                if other is not candidate
            )
        ]
        latest_statuses = {cast(str, event["status"]) for event in latest}
        _require(len(latest_statuses) == 1, "DUPLICATE_ACTIVE_FINDING", identifier)
        active_status = latest_statuses.pop()
        finding_ids[active_status].append(identifier)
        lifecycle.append(
            {
                "id": identifier,
                "active_status": active_status,
                "events": [
                    {
                        "batch_id": event["batch_id"],
                        "status": event["status"],
                        "evidence": event["evidence"],
                    }
                    for event in events
                ],
            }
        )
    return dispositions, finding_ids, lifecycle


def _team(runs: list[dict[str, object]], batches: list[dict[str, object]], root: Path) -> dict[str, object]:
    superseded_ids = [cast(str, batch["supersedes"]) for batch in batches if batch["supersedes"] is not None]
    _require(len(superseded_ids) == len(set(superseded_ids)), "DUPLICATE_SUPERSESSION")
    for batch in batches:
        batch["active"] = batch["id"] not in superseded_ids
    active = [batch for batch in batches if batch["active"]]
    disposition_counts, finding_ids, finding_lifecycle = _active_finding_quality(active, root)

    ranges: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    for batch in active:
        ranges[(cast(str, batch["before_commit"]), cast(str, batch["after_commit"]))].append(batch)
    range_rows = [
        {"before_commit": pair[0], "after_commit": pair[1], "batch_ids": [batch["id"] for batch in members]}
        for pair, members in ranges.items()
    ]
    duplicate_ranges = [row for row in range_rows if len(cast(list[object], row["batch_ids"])) > 1]

    transition_rows: list[dict[str, object]] = []
    obligation_owner: set[tuple[tuple[str, str], str]] = set()
    positive_pairs: set[tuple[str, str]] = set()
    transition_pairs: set[tuple[str, str]] = set()
    for pair, members in ranges.items():
        scored = [
            batch
            for batch in members
            if cast(dict[str, object], batch["assessment"])["status"] == "REVIEWED_DELTA"
        ]
        if not scored:
            continue
        deltas = [cast(dict[str, object], cast(dict[str, object], batch["assessment"])["delta"]) for batch in scored]
        baseline = deltas[0]
        _require(all(delta == baseline for delta in deltas[1:]), "INCONSISTENT_SCORE_TRANSITION")
        if _positive(baseline):
            for batch in scored:
                outcome = cast(dict[str, object], batch["outcome"])
                _require(
                    outcome["disposition"] == "accepted_partial",
                    "NONPRODUCT_SCORE_CREDIT",
                    cast(str, batch["id"]),
                )
                _require(
                    batch["before_commit"] != batch["after_commit"],
                    "SAME_HEAD_SCORE_CREDIT",
                    cast(str, batch["id"]),
                )
            positive_pairs.add(pair)
        for batch in scored:
            for obligation in cast(list[str], batch["obligation_ids"]):
                key = (pair, obligation)
                _require(key not in obligation_owner, "DUPLICATE_OBLIGATION_TRANSITION", obligation)
                obligation_owner.add(key)
        transition_rows.append(
            {
                "before_commit": pair[0],
                "after_commit": pair[1],
                "batch_ids": [batch["id"] for batch in scored],
                "delta": baseline,
            }
        )
        transition_pairs.add(pair)
        for batch in scored:
            batch["team_score_transition"] = {"status": "REVIEWED_DELTA", "subject_pair": [pair[0], pair[1]]}
    for batch in batches:
        batch.setdefault("team_score_transition", {"status": cast(dict[str, object], batch["assessment"])["status"]})

    checkpoints: dict[str, dict[str, object]] = {}
    for batch in active:
        assessment = cast(dict[str, object], batch["assessment"])
        if assessment["status"] != "REVIEWED_DELTA":
            continue
        for subject, score in (
            (cast(str, batch["before_commit"]), cast(dict[str, object], assessment["before_scores"])),
            (cast(str, batch["after_commit"]), cast(dict[str, object], assessment["after_scores"])),
        ):
            prior = checkpoints.get(subject)
            _require(prior is None or prior == score, "INCONSISTENT_SCORE_CHECKPOINT", subject)
            checkpoints[subject] = score

    overlaps: list[dict[str, object]] = []
    divergent: list[dict[str, object]] = []
    range_pairs = list(ranges)
    for index, first in enumerate(range_pairs):
        for second in range_pairs[index + 1 :]:
            scored_pair = first in transition_pairs and second in transition_pairs
            afters_comparable = _ancestor(root, first[1], second[1]) or _ancestor(root, second[1], first[1])
            if not afters_comparable:
                divergent.append(
                    {
                        "first": {"before_commit": first[0], "after_commit": first[1]},
                        "second": {"before_commit": second[0], "after_commit": second[1]},
                        "score_transition_divergence": scored_pair,
                    }
                )
                _require(not scored_pair, "DIVERGENT_SCORE_TRANSITION")
            elif _ranges_overlap(root, first, second):
                overlaps.append(
                    {
                        "first": {"before_commit": first[0], "after_commit": first[1]},
                        "second": {"before_commit": second[0], "after_commit": second[1]},
                        "positive_score_credit_overlap": first in positive_pairs and second in positive_pairs,
                        "score_transition_overlap": scored_pair,
                    }
                )
                _require(not scored_pair, "OVERLAPPING_SCORE_TRANSITION")
            elif not _ranges_ordered(root, first, second):
                divergent.append(
                    {
                        "first": {"before_commit": first[0], "after_commit": first[1]},
                        "second": {"before_commit": second[0], "after_commit": second[1]},
                        "score_transition_divergence": scored_pair,
                    }
                )
                _require(not scored_pair, "DIVERGENT_SCORE_TRANSITION")

    unique_diffs = [cast(dict[str, object], members[0]["diff"]) for members in ranges.values()]
    team_lines: dict[str, object]
    if overlaps:
        team_lines = {
            "status": "NOT_AGGREGATED_OVERLAPPING_RANGES",
            "categories": None,
            "binary_file_count": None,
        }
    elif divergent:
        team_lines = {
            "status": "NOT_AGGREGATED_DIVERGENT_RANGES",
            "categories": None,
            "binary_file_count": None,
        }
    else:
        team_lines = {
            "status": "DEDUPLICATED_ACTIVE_RANGES",
            "categories": _sum_categories(unique_diffs),
            "binary_file_count": sum(cast(int, diff["binary_file_count"]) for diff in unique_diffs),
        }

    run_to_batches: dict[str, list[str]] = defaultdict(list)
    run_to_active_batches: dict[str, list[str]] = defaultdict(list)
    for batch in batches:
        for run_id in cast(list[str], batch["run_ids"]):
            run_to_batches[run_id].append(cast(str, batch["id"]))
            if batch["active"]:
                run_to_active_batches[run_id].append(cast(str, batch["id"]))
    models: dict[str | None, list[dict[str, object]]] = defaultdict(list)
    for run in runs:
        run["participation"] = {
            "referenced_batch_ids": run_to_batches[cast(str, run["id"])],
            "active_batch_ids": run_to_active_batches[cast(str, run["id"])],
        }
        models[cast(str | None, run["model_id"])].append(run)
    model_rows = [
        {
            "model_id": model_id,
            "label": "UNKNOWN_MODEL" if model_id is None else model_id,
            "run_ids": [run["id"] for run in grouped],
            "participation": {
                "referenced_batch_ids": sorted(
                    {
                        batch_id
                        for run in grouped
                        for batch_id in cast(dict[str, list[str]], run["participation"])["referenced_batch_ids"]
                    }
                ),
                "active_batch_ids": sorted(
                    {
                        batch_id
                        for run in grouped
                        for batch_id in cast(dict[str, list[str]], run["participation"])["active_batch_ids"]
                    }
                ),
            },
            "resources": _resource_rollup(grouped),
        }
        for model_id, grouped in sorted(models.items(), key=lambda item: (item[0] is None, item[0] or ""))
    ]
    declared_models = [run for run in runs if run["model_id"] is not None]
    sourced_models = [run for run in declared_models if run["provenance"] is not None]
    return {
        "active_batch_count": len(active),
        "superseded_batch_count": len(batches) - len(active),
        "active_quality": {
            "status": "SOURCE_RECORDED_DECLARATIONS",
            "not_certified_acceptance_or_closed_obligations": True,
            "evidence_backed_dispositions": dict(sorted(disposition_counts.items())),
            "finding_ids": {status: sorted(identifiers) for status, identifiers in finding_ids.items()},
            "finding_lifecycle": finding_lifecycle,
        },
        "score_transitions": transition_rows,
        "duplicate_active_ranges": duplicate_ranges,
        "overlapping_active_ranges": overlaps,
        "divergent_active_ranges": divergent,
        "line_metrics": team_lines,
        "resources": _resource_rollup(runs),
        "models": model_rows,
        "coverage": {
            "dispatch_inventory_reconciled": False,
            "batches_without_run_ids": sum(not cast(list[object], batch["run_ids"]) for batch in batches),
            "declared_model_run_count": len(declared_models),
            "declared_model_with_provenance_run_count": len(sourced_models),
            "unverified_model_declaration_run_count": len(runs) - len(sourced_models),
            "unknown_model_run_count": len(runs) - len(declared_models),
        },
    }


def _baseline_prefix(
    root: Path,
    manifest_path: Path,
    baseline_commit: str | None,
    current: dict[str, object],
    sources: _Sources,
) -> dict[str, object] | None:
    if baseline_commit is None:
        return {"status": "NOT_CHECKED"}
    commit = progress._commit(baseline_commit, "BASELINE_MANIFEST_COMMIT")
    sources.require_commit(commit)
    try:
        path = manifest_path.resolve(strict=True).relative_to(root.resolve(strict=True)).as_posix()
    except (OSError, ValueError) as error:
        _reject("BASELINE_MANIFEST_PATH", type(error).__name__)
    progress._safe_path(path, "BASELINE_MANIFEST_PATH")
    head = progress._commit(
        progress._run_git(root, ["rev-parse", "HEAD"], "BASELINE_HEAD").decode("ascii", "strict").strip(),
        "BASELINE_HEAD",
    )
    sources.require_commit(head)
    _require(_ancestor(root, commit, head), "BASELINE_NOT_ANCESTOR", path)
    history = [
        progress._commit(item, "BASELINE_MANIFEST_HISTORY")
        for item in progress._run_git(
            root,
            ["rev-list", f"{commit}..{head}", "--", path],
            "BASELINE_MANIFEST_HISTORY",
        )
        .decode("ascii", "strict")
        .splitlines()
        if item
    ]
    _require(len(history) <= 1, "BASELINE_NOT_CURRENT", path)
    if history:
        current_bytes = progress._read_regular(
            manifest_path,
            maximum=progress.MAX_JSON_BYTES,
            label="MANIFEST",
        )
        current_commit_bytes = progress._git_blob(root, history[0], path)
        _require(current_commit_bytes is not None, "MISSING_BASELINE_MANIFEST", path)
        _require(current_commit_bytes == current_bytes, "BASELINE_NOT_CURRENT", path)
    blob = progress._git_blob(root, commit, path)
    _require(blob is not None, "MISSING_BASELINE_MANIFEST", path)
    historical_value = _decode_json(blob, "BASELINE_MANIFEST")
    historical = _object(historical_value, ("schema", "runs", "batches"), "BASELINE_MANIFEST")
    _require(historical["schema"] == MANIFEST_SCHEMA, "BASELINE_MANIFEST_SCHEMA")
    _require(type(historical["runs"]) is list and type(historical["batches"]) is list, "BASELINE_MANIFEST")
    for field in ("runs", "batches"):
        previous = cast(list[object], historical[field])
        present = cast(list[object], current[field])
        _require(len(present) >= len(previous), "BASELINE_NOT_APPEND_ONLY", field)
        _require(
            progress._canonical(present[: len(previous)]) == progress._canonical(previous),
            "BASELINE_NOT_APPEND_ONLY",
            field,
        )
    return {"commit": commit, "path": path, "status": "PREFIX_PRESERVED"}


def collect(manifest_path: Path, root: Path, baseline_manifest_commit: str | None = None) -> dict[str, object]:
    """Validate one manifest and render its advisory, source-bound observations."""
    manifest = _load_manifest(manifest_path)
    _object(manifest, ("schema", "runs", "batches"), "TOP_LEVEL_FIELDS")
    _require(manifest["schema"] == MANIFEST_SCHEMA, "MANIFEST_SCHEMA")
    _require(type(manifest["runs"]) is list and type(manifest["batches"]) is list, "TOP_LEVEL_FIELDS")
    sources = _Sources(root.resolve(strict=True))
    progress._run_git(sources.root, ["rev-parse", "--show-toplevel"], "ROOT_NOT_GIT")
    runs = [_run(value, sources) for value in cast(list[object], manifest["runs"])]
    run_identifiers = [cast(str, run["id"]) for run in runs]
    _require(len(run_identifiers) == len(set(run_identifiers)), "DUPLICATE_RUN_ID")
    _unique_resource_observations(runs)
    batches: list[dict[str, object]] = []
    batch_identifiers: set[str] = set()
    for value in cast(list[object], manifest["batches"]):
        batch = _batch(value, sources, set(run_identifiers), batch_identifiers)
        _require(batch["id"] not in batch_identifiers, "DUPLICATE_BATCH_ID", cast(str, batch["id"]))
        batches.append(batch)
        batch_identifiers.add(cast(str, batch["id"]))
    baseline = _baseline_prefix(root, manifest_path, baseline_manifest_commit, manifest, sources)
    team = _team(runs, batches, sources.root)
    return {
        "schema": REPORT_SCHEMA,
        "advisory": ADVISORY,
        "claim_ceiling": list(CLAIM_CEILING),
        "ok": True,
        "source_integrity": sources.integrity(),
        "line_classification_convention": {
            "rust": "RUNTIME_INCLUDES_INLINE_CFG_TEST_MODULES",
            "unsupported_languages": "other",
            "product_credit": "LINE_CATEGORIES_NEVER_GRANT_CREDIT; DATA_AND_DOCS_LINE_COUNTS_CANNOT_EARN_PRODUCT_CREDIT",
        },
        "baseline_manifest": baseline,
        "runs": runs,
        "batches": batches,
        "team": team,
    }


class _Parser(argparse.ArgumentParser):
    def error(self, message: str) -> NoReturn:
        _reject("USAGE", message)


def _emit(value: dict[str, object]) -> None:
    print(json.dumps(value, indent=2, sort_keys=True, allow_nan=False))


def main(argv: list[str] | None = None) -> int:
    parser = _Parser(add_help=True)
    parser.add_argument("manifest")
    parser.add_argument("--root", default=str(progress.REPO_ROOT))
    parser.add_argument("--baseline-manifest-commit")
    try:
        arguments = parser.parse_args(sys.argv[1:] if argv is None else argv)
        _emit(
            collect(
                Path(arguments.manifest),
                Path(arguments.root),
                cast(str | None, arguments.baseline_manifest_commit),
            )
        )
    except ProductivityReject as error:
        _emit({"schema": REPORT_SCHEMA, "advisory": ADVISORY, "findings": [{"code": error.code}], "ok": False})
        return 2
    except progress.ProgressReject as error:
        _emit({"schema": REPORT_SCHEMA, "advisory": ADVISORY, "findings": [{"code": error.code}], "ok": False})
        return 2
    except OSError:
        _emit({"schema": REPORT_SCHEMA, "advisory": ADVISORY, "findings": [{"code": "INPUT_READ"}], "ok": False})
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
