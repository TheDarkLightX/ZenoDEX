#!/usr/bin/env python3
"""Classify ZKPF changes and require a complete review-intent packet."""
from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable, Sequence

CONFIG_SCHEMA = "zenodex/zkpf_change_classification/v1"
PACKET_SCHEMA = "zenodex/zkpf_change_review_packet/v1"
REPORT_SCHEMA = "zenodex/zkpf_change_review_report/v1"
MAX_JSON_BYTES = 128 * 1024
MAX_JSON_DEPTH = 128
MAX_CHANGED_PATHS = 4096
MAX_CHANGED_FILE_BYTES = 64 * 1024 * 1024
_RULE_ID_RE = re.compile(r"^[a-z][a-z0-9_]{0,63}$")
_TOKEN_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:/@+-]{1,255}$")
_ALLOWED_CLASSES = frozenset(
    {"ordinary", "soundness", "authority", "release", "performance", "operations"}
)
_CONFIG_FIELDS = frozenset({"schema", "excluded_globs", "rules"})
_RULE_FIELDS = frozenset(
    {
        "id",
        "change_class",
        "globs",
        "required_reviewer_roles",
        "minimum_confidence_bps",
        "requires_invariant_ids",
        "requires_paper_references",
        "requires_negative_controls",
        "requires_benchmark_evidence",
    }
)
_PACKET_FIELDS = frozenset(
    {
        "schema",
        "config_sha256",
        "change_set_sha256",
        "changed_path_count",
        "affected_classes",
        "affected_rule_ids",
        "reviewer_roles",
        "confidence_bps",
        "invariant_ids",
        "paper_references",
        "test_commands",
        "negative_controls",
        "benchmark_evidence",
        "divergence_records",
        "review_state",
        "approval_channel",
        "authority",
    }
)
_FALSE_AUTHORITY = {
    "production_authority": False,
    "proof_authority": False,
    "release_authority": False,
    "settlement_authority": False,
}


class ChangeReviewError(ValueError):
    pass


@dataclass(frozen=True, slots=True)
class Rule:
    id: str
    change_class: str
    globs: tuple[str, ...]
    required_reviewer_roles: tuple[str, ...]
    minimum_confidence_bps: int
    requires_invariant_ids: bool
    requires_paper_references: bool
    requires_negative_controls: bool
    requires_benchmark_evidence: bool


@dataclass(frozen=True, slots=True)
class ClassificationConfig:
    rules: tuple[Rule, ...]
    excluded_globs: tuple[str, ...]
    raw: bytes

    @property
    def digest(self) -> str:
        return hashlib.sha256(self.raw).hexdigest()


@dataclass(frozen=True, slots=True)
class ChangedPath:
    status: str
    path: str


@dataclass(frozen=True, slots=True)
class ChangeSet:
    paths: tuple[ChangedPath, ...]
    digest: str


@dataclass(frozen=True, slots=True)
class Requirements:
    classes: tuple[str, ...]
    rule_ids: tuple[str, ...]
    reviewer_roles: tuple[str, ...]
    minimum_confidence_bps: int
    requires_invariant_ids: bool
    requires_paper_references: bool
    requires_negative_controls: bool
    requires_benchmark_evidence: bool


def canonical_json_bytes(value: object) -> bytes:
    text = json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )
    return (text + "\n").encode("ascii")


def _reject_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ChangeReviewError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_float(value: str) -> object:
    raise ChangeReviewError(f"floating-point JSON number forbidden: {value}")


def _reject_constant(value: str) -> object:
    raise ChangeReviewError(f"non-finite JSON number forbidden: {value}")


def _check_depth(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in (0x5B, 0x7B):
            depth += 1
            if depth > MAX_JSON_DEPTH:
                raise ChangeReviewError("JSON nesting exceeds limit")
        elif byte in (0x5D, 0x7D):
            depth -= 1
            if depth < 0:
                raise ChangeReviewError("JSON nesting is malformed")
    if in_string or depth != 0:
        raise ChangeReviewError("JSON structure is incomplete")


def strict_json_loads(raw: bytes) -> object:
    if type(raw) is not bytes or not raw or len(raw) > MAX_JSON_BYTES:
        raise ChangeReviewError("JSON input must be nonempty bounded bytes")
    _check_depth(raw)
    try:
        text = raw.decode("ascii")
        value = json.loads(
            text,
            object_pairs_hook=_reject_pairs,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
        )
    except ChangeReviewError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise ChangeReviewError("JSON input is invalid") from exc
    if canonical_json_bytes(value) != raw:
        raise ChangeReviewError("JSON input is not canonical")
    return value


def _safe_path(value: object, *, label: str, allow_glob: bool) -> str:
    if type(value) is not str or not value or len(value.encode("utf-8")) > 512:
        raise ChangeReviewError(f"{label} must be a bounded nonempty path")
    if "\\" in value or "\0" in value or value.startswith("/"):
        raise ChangeReviewError(f"{label} is not repository relative")
    normalized = re.sub(r"[*?\[\]]", "x", value) if allow_glob else value
    parts = PurePosixPath(normalized).parts
    if not parts or any(part in {"", ".", ".."} for part in parts):
        raise ChangeReviewError(f"{label} is not repository relative")
    return value


def _strings(
    value: object,
    *,
    label: str,
    allow_empty: bool,
    globs: bool = False,
) -> tuple[str, ...]:
    if not isinstance(value, list) or (not allow_empty and not value):
        raise ChangeReviewError(f"{label} must be a bounded list")
    output: list[str] = []
    for item in value:
        if type(item) is not str or not item or len(item.encode("utf-8")) > 1024:
            raise ChangeReviewError(f"{label} entries must be bounded strings")
        output.append(_safe_path(item, label=label, allow_glob=True) if globs else item)
    if output != sorted(output) or len(output) != len(set(output)):
        raise ChangeReviewError(f"{label} must be sorted and unique")
    return tuple(output)


def parse_config(raw: bytes) -> ClassificationConfig:
    value = strict_json_loads(raw)
    if type(value) is not dict or frozenset(value) != _CONFIG_FIELDS:
        raise ChangeReviewError("classification config field set mismatch")
    if value.get("schema") != CONFIG_SCHEMA:
        raise ChangeReviewError("classification config schema mismatch")
    excluded = _strings(
        value.get("excluded_globs"),
        label="excluded_globs",
        allow_empty=True,
        globs=True,
    )
    rows = value.get("rules")
    if not isinstance(rows, list) or not rows or len(rows) > 128:
        raise ChangeReviewError("classification rules must be a nonempty bounded list")
    rules: list[Rule] = []
    for index, row in enumerate(rows):
        if type(row) is not dict or frozenset(row) != _RULE_FIELDS:
            raise ChangeReviewError(f"rule[{index}] field set mismatch")
        rule_id = row.get("id")
        change_class = row.get("change_class")
        confidence = row.get("minimum_confidence_bps")
        if type(rule_id) is not str or _RULE_ID_RE.fullmatch(rule_id) is None:
            raise ChangeReviewError(f"rule[{index}] id is invalid")
        if change_class not in _ALLOWED_CLASSES:
            raise ChangeReviewError(f"rule {rule_id} class is invalid")
        if type(confidence) is not int or not 0 <= confidence <= 10_000:
            raise ChangeReviewError(f"rule {rule_id} confidence is invalid")
        booleans: dict[str, bool] = {}
        for field in (
            "requires_invariant_ids",
            "requires_paper_references",
            "requires_negative_controls",
            "requires_benchmark_evidence",
        ):
            candidate = row.get(field)
            if type(candidate) is not bool:
                raise ChangeReviewError(f"rule {rule_id} {field} must be Boolean")
            booleans[field] = candidate
        rules.append(
            Rule(
                id=rule_id,
                change_class=change_class,
                globs=_strings(
                    row.get("globs"),
                    label=f"{rule_id}.globs",
                    allow_empty=False,
                    globs=True,
                ),
                required_reviewer_roles=_strings(
                    row.get("required_reviewer_roles"),
                    label=f"{rule_id}.required_reviewer_roles",
                    allow_empty=change_class == "ordinary",
                ),
                minimum_confidence_bps=confidence,
                requires_invariant_ids=booleans["requires_invariant_ids"],
                requires_paper_references=booleans["requires_paper_references"],
                requires_negative_controls=booleans["requires_negative_controls"],
                requires_benchmark_evidence=booleans[
                    "requires_benchmark_evidence"
                ],
            )
        )
    if [rule.id for rule in rules] != sorted(rule.id for rule in rules):
        raise ChangeReviewError("classification rules must be sorted by id")
    if len(rules) != len({rule.id for rule in rules}):
        raise ChangeReviewError("classification rule ids must be unique")
    return ClassificationConfig(tuple(rules), excluded, raw)


def _matches(path: str, pattern: str) -> bool:
    prefix_candidate = pattern[:-3] if pattern.endswith("/**") else pattern
    if pattern.endswith("/**") and not any(
        marker in prefix_candidate for marker in ("*", "?", "[")
    ):
        prefix = prefix_candidate.rstrip("/")
        return path == prefix or path.startswith(prefix + "/")
    return fnmatch.fnmatchcase(path, pattern)


def _parse_name_status(raw: bytes) -> tuple[ChangedPath, ...]:
    fields = raw.decode("utf-8", errors="strict").split("\0")
    if fields and fields[-1] == "":
        fields.pop()
    rows: list[ChangedPath] = []
    cursor = 0
    while cursor < len(fields):
        status = fields[cursor]
        cursor += 1
        if status.startswith(("R", "C")):
            if cursor + 1 >= len(fields):
                raise ChangeReviewError("git rename record is truncated")
            old = _safe_path(fields[cursor], label="old changed path", allow_glob=False)
            new = _safe_path(fields[cursor + 1], label="new changed path", allow_glob=False)
            cursor += 2
            if status.startswith("R"):
                rows.append(ChangedPath("D", old))
            rows.append(ChangedPath("A", new))
        else:
            if cursor >= len(fields) or status not in {"A", "M", "D", "T"}:
                raise ChangeReviewError(f"unsupported git change status: {status}")
            path = _safe_path(fields[cursor], label="changed path", allow_glob=False)
            cursor += 1
            rows.append(ChangedPath(status, path))
    output = tuple(sorted(set(rows), key=lambda row: (row.path, row.status)))
    if len(output) > MAX_CHANGED_PATHS:
        raise ChangeReviewError("changed path count exceeds limit")
    return output


def _run_git(repository: Path, arguments: Sequence[str]) -> bytes:
    completed = subprocess.run(
        ["git", "-c", "core.quotepath=false", *arguments],
        cwd=repository,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
        env={"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "LC_ALL": "C"},
    )
    if completed.returncode != 0 or completed.stderr:
        raise ChangeReviewError("git change-set discovery failed")
    return completed.stdout


def git_change_set(
    config: ClassificationConfig,
    repository: Path,
    base: str,
    head: str,
) -> ChangeSet:
    exclusions = [f":(exclude,glob){pattern}" for pattern in config.excluded_globs]
    range_spec = f"{base}...{head}"
    paths = _parse_name_status(
        _run_git(
            repository,
            [
                "diff",
                "--name-status",
                "--find-renames=100%",
                "-z",
                range_spec,
                "--",
                ".",
                *exclusions,
            ],
        )
    )
    diff = _run_git(
        repository,
        [
            "diff",
            "--binary",
            "--full-index",
            "--no-ext-diff",
            range_spec,
            "--",
            ".",
            *exclusions,
        ],
    )
    return ChangeSet(paths, hashlib.sha256(diff).hexdigest())


def _read_changed_file(repository: Path, relative: str) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(repository / relative, flags)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_nlink != 1
            or before.st_size < 0
            or before.st_size > MAX_CHANGED_FILE_BYTES
        ):
            raise ChangeReviewError("changed path is not a bounded single-link regular file")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                raise ChangeReviewError("changed file changed while being read")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise ChangeReviewError("changed file exceeded its observed size")
        after = os.fstat(descriptor)

        def identity(value: os.stat_result) -> tuple[int, ...]:
            return (
                value.st_dev,
                value.st_ino,
                value.st_mode,
                value.st_nlink,
                value.st_size,
                value.st_mtime_ns,
                value.st_ctime_ns,
            )

        if identity(before) != identity(after):
            raise ChangeReviewError("changed file changed while being read")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def explicit_change_set(
    config: ClassificationConfig,
    repository: Path,
    paths: Iterable[str],
) -> ChangeSet:
    normalized = sorted(
        {
            _safe_path(path.strip(), label="changed path", allow_glob=False)
            for path in paths
            if path.strip()
            and not any(_matches(path.strip(), pattern) for pattern in config.excluded_globs)
        }
    )
    if len(normalized) > MAX_CHANGED_PATHS:
        raise ChangeReviewError("changed path count exceeds limit")
    hasher = hashlib.sha256()
    changed: list[ChangedPath] = []
    for relative in normalized:
        raw = _read_changed_file(repository, relative)
        digest = hashlib.sha256(raw).hexdigest()
        hasher.update(f"M\0{relative}\0{digest}\n".encode("utf-8"))
        changed.append(ChangedPath("M", relative))
    return ChangeSet(tuple(changed), hasher.hexdigest())


def classify(
    config: ClassificationConfig,
    change_set: ChangeSet,
) -> tuple[list[dict[str, object]], Requirements]:
    classifications: list[dict[str, object]] = []
    matched: dict[str, Rule] = {}
    for changed in change_set.paths:
        rules = [
            rule
            for rule in config.rules
            if any(_matches(changed.path, pattern) for pattern in rule.globs)
        ]
        matched.update({rule.id: rule for rule in rules})
        classifications.append(
            {
                "status": changed.status,
                "path": changed.path,
                "rule_ids": [rule.id for rule in rules],
                "classes": sorted({rule.change_class for rule in rules} or {"ordinary"}),
            }
        )
    protected = [rule for rule in matched.values() if rule.change_class != "ordinary"]
    requirements = Requirements(
        classes=tuple(sorted({rule.change_class for rule in protected})),
        rule_ids=tuple(sorted(rule.id for rule in protected)),
        reviewer_roles=tuple(
            sorted({role for rule in protected for role in rule.required_reviewer_roles})
        ),
        minimum_confidence_bps=max(
            (rule.minimum_confidence_bps for rule in protected),
            default=0,
        ),
        requires_invariant_ids=any(rule.requires_invariant_ids for rule in protected),
        requires_paper_references=any(
            rule.requires_paper_references for rule in protected
        ),
        requires_negative_controls=any(
            rule.requires_negative_controls for rule in protected
        ),
        requires_benchmark_evidence=any(
            rule.requires_benchmark_evidence for rule in protected
        ),
    )
    return classifications, requirements


def _packet_list(
    value: object,
    *,
    label: str,
    allow_empty: bool,
    tokens: bool = False,
) -> tuple[str, ...]:
    output = _strings(value, label=label, allow_empty=allow_empty)
    if tokens and any(_TOKEN_RE.fullmatch(item) is None for item in output):
        raise ChangeReviewError(f"{label} contains a malformed token")
    return output


def validate_packet(
    raw: bytes,
    *,
    config: ClassificationConfig,
    change_set: ChangeSet,
    requirements: Requirements,
) -> dict[str, object]:
    value = strict_json_loads(raw)
    if type(value) is not dict or frozenset(value) != _PACKET_FIELDS:
        raise ChangeReviewError("review packet field set mismatch")
    if value.get("schema") != PACKET_SCHEMA:
        raise ChangeReviewError("review packet schema mismatch")
    if value.get("config_sha256") != config.digest:
        raise ChangeReviewError("review packet config digest mismatch")
    if value.get("change_set_sha256") != change_set.digest:
        raise ChangeReviewError("review packet change-set digest mismatch")
    if value.get("changed_path_count") != len(change_set.paths):
        raise ChangeReviewError("review packet changed-path count mismatch")
    classes = _packet_list(
        value.get("affected_classes"),
        label="affected_classes",
        allow_empty=False,
        tokens=True,
    )
    rule_ids = _packet_list(
        value.get("affected_rule_ids"),
        label="affected_rule_ids",
        allow_empty=False,
        tokens=True,
    )
    roles = _packet_list(
        value.get("reviewer_roles"),
        label="reviewer_roles",
        allow_empty=False,
        tokens=True,
    )
    if classes != requirements.classes or rule_ids != requirements.rule_ids:
        raise ChangeReviewError("review packet classification mismatch")
    if not set(requirements.reviewer_roles).issubset(roles):
        raise ChangeReviewError("review packet omits a required reviewer role")
    confidence = value.get("confidence_bps")
    if (
        type(confidence) is not int
        or confidence < requirements.minimum_confidence_bps
        or confidence > 10_000
    ):
        raise ChangeReviewError("review packet confidence is below the required floor")
    summary = {
        "invariant_ids": list(
            _packet_list(
                value.get("invariant_ids"),
                label="invariant_ids",
                allow_empty=not requirements.requires_invariant_ids,
                tokens=True,
            )
        ),
        "paper_references": list(
            _packet_list(
                value.get("paper_references"),
                label="paper_references",
                allow_empty=not requirements.requires_paper_references,
            )
        ),
        "test_commands": list(
            _packet_list(
                value.get("test_commands"),
                label="test_commands",
                allow_empty=False,
            )
        ),
        "negative_controls": list(
            _packet_list(
                value.get("negative_controls"),
                label="negative_controls",
                allow_empty=not requirements.requires_negative_controls,
            )
        ),
        "benchmark_evidence": list(
            _packet_list(
                value.get("benchmark_evidence"),
                label="benchmark_evidence",
                allow_empty=not requirements.requires_benchmark_evidence,
            )
        ),
        "divergence_records": list(
            _packet_list(
                value.get("divergence_records"),
                label="divergence_records",
                allow_empty=True,
            )
        ),
        "reviewer_roles": list(roles),
        "confidence_bps": confidence,
    }
    if value.get("review_state") != "ready_for_human_review":
        raise ChangeReviewError("review packet is not ready for human review")
    if value.get("approval_channel") != "github_required_review":
        raise ChangeReviewError("review packet approval channel is unsupported")
    if value.get("authority") != _FALSE_AUTHORITY:
        raise ChangeReviewError("review packet attempted to promote authority")
    return summary


def packet_skeleton(
    *,
    config: ClassificationConfig,
    change_set: ChangeSet,
    requirements: Requirements,
) -> dict[str, object]:
    return {
        "schema": PACKET_SCHEMA,
        "config_sha256": config.digest,
        "change_set_sha256": change_set.digest,
        "changed_path_count": len(change_set.paths),
        "affected_classes": list(requirements.classes),
        "affected_rule_ids": list(requirements.rule_ids),
        "reviewer_roles": list(requirements.reviewer_roles),
        "confidence_bps": requirements.minimum_confidence_bps,
        "invariant_ids": ["TODO.REPLACE"] if requirements.requires_invariant_ids else [],
        "paper_references": (
            ["TODO: replace with a paper or normative specification anchor"]
            if requirements.requires_paper_references
            else []
        ),
        "test_commands": ["TODO: add an exact command"],
        "negative_controls": (
            ["TODO: add a named reject case"]
            if requirements.requires_negative_controls
            else []
        ),
        "benchmark_evidence": (
            ["TODO: add a before/after benchmark artifact"]
            if requirements.requires_benchmark_evidence
            else []
        ),
        "divergence_records": [],
        "review_state": "draft",
        "approval_channel": "github_required_review",
        "authority": dict(_FALSE_AUTHORITY),
    }


def required_packet_path(review_root: Path, digest: str) -> Path:
    return review_root / f"{digest}.json"


def _read_review_packet(review_root: Path, filename: str) -> bytes:
    if "/" in filename or filename.startswith("."):
        raise ChangeReviewError("review packet filename is invalid")
    directory_flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    file_flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    directory = os.open(review_root, directory_flags)
    try:
        descriptor = os.open(filename, file_flags, dir_fd=directory)
        try:
            before = os.fstat(descriptor)
            if (
                not stat.S_ISREG(before.st_mode)
                or before.st_nlink != 1
                or not 0 < before.st_size <= MAX_JSON_BYTES
            ):
                raise ChangeReviewError("review packet is not a bounded single-link regular file")
            raw = os.read(descriptor, before.st_size + 1)
            after = os.fstat(descriptor)
            if len(raw) != before.st_size or (
                before.st_dev,
                before.st_ino,
                before.st_mode,
                before.st_nlink,
                before.st_size,
                before.st_mtime_ns,
                before.st_ctime_ns,
            ) != (
                after.st_dev,
                after.st_ino,
                after.st_mode,
                after.st_nlink,
                after.st_size,
                after.st_mtime_ns,
                after.st_ctime_ns,
            ):
                raise ChangeReviewError("review packet changed while being read")
            return raw
        finally:
            os.close(descriptor)
    finally:
        os.close(directory)


def build_report(
    *,
    config: ClassificationConfig,
    change_set: ChangeSet,
    review_root: Path,
    require_review: bool,
) -> tuple[dict[str, object], bool]:
    classifications, requirements = classify(config, change_set)
    packet_path = required_packet_path(review_root, change_set.digest)
    packet_required = bool(requirements.classes)
    packet_valid = False
    packet_error: str | None = None
    packet_summary: dict[str, object] | None = None
    if packet_required and packet_path.exists():
        try:
            packet_summary = validate_packet(
                _read_review_packet(review_root, packet_path.name),
                config=config,
                change_set=change_set,
                requirements=requirements,
            )
            packet_valid = True
        except (OSError, ChangeReviewError) as exc:
            packet_error = str(exc)
    elif packet_required:
        packet_error = "required review packet is absent"
    accepted = not require_review or not packet_required or packet_valid
    report = {
        "schema": REPORT_SCHEMA,
        "accepted": accepted,
        "config_sha256": config.digest,
        "change_set_sha256": change_set.digest,
        "changed_paths": classifications,
        "requirements": {
            "affected_classes": list(requirements.classes),
            "affected_rule_ids": list(requirements.rule_ids),
            "reviewer_roles": list(requirements.reviewer_roles),
            "minimum_confidence_bps": requirements.minimum_confidence_bps,
            "requires_invariant_ids": requirements.requires_invariant_ids,
            "requires_paper_references": requirements.requires_paper_references,
            "requires_negative_controls": requirements.requires_negative_controls,
            "requires_benchmark_evidence": requirements.requires_benchmark_evidence,
        },
        "packet_required": packet_required,
        "packet_path": packet_path.as_posix(),
        "packet_valid": packet_valid,
        "packet_error": packet_error,
        "packet_summary": packet_summary,
        "authority": dict(_FALSE_AUTHORITY),
    }
    return report, accepted


def _write_new(path: Path, raw: bytes) -> None:
    if path.exists():
        raise ChangeReviewError("review packet output must begin absent")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.rename(temporary, path)
    except Exception:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--config",
        type=Path,
        default=Path("config/proof_profiles/zkpf_change_classification_v1.json"),
    )
    parser.add_argument("--repository", type=Path, default=Path("."))
    parser.add_argument("--base")
    parser.add_argument("--head")
    parser.add_argument("--changed-path", action="append", default=[])
    parser.add_argument("--review-root", type=Path, default=Path("reviews/zkpf"))
    parser.add_argument("--require-review", action="store_true")
    parser.add_argument("--emit-skeleton", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)
    try:
        config = parse_config(args.config.read_bytes())
        if args.base or args.head:
            if not args.base or not args.head or args.changed_path:
                raise ChangeReviewError(
                    "use either explicit changed paths or an exact base/head pair"
                )
            change_set = git_change_set(
                config,
                args.repository,
                args.base,
                args.head,
            )
        else:
            change_set = explicit_change_set(config, args.repository, args.changed_path)
        _, requirements = classify(config, change_set)
        if args.emit_skeleton is not None:
            if not requirements.classes:
                raise ChangeReviewError("this change set needs no review packet")
            _write_new(
                args.emit_skeleton,
                canonical_json_bytes(
                    packet_skeleton(
                        config=config,
                        change_set=change_set,
                        requirements=requirements,
                    )
                ),
            )
        report, accepted = build_report(
            config=config,
            change_set=change_set,
            review_root=args.review_root,
            require_review=args.require_review,
        )
        if args.pretty:
            print(json.dumps(report, indent=2, sort_keys=True))
        else:
            sys.stdout.buffer.write(canonical_json_bytes(report))
        return 0 if accepted else 1
    except (OSError, ChangeReviewError, subprocess.SubprocessError) as exc:
        print(f"error: ZKPF change review failed closed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
