#!/usr/bin/env python3
"""Fail-closed checker, renderer, and regenerator for the whole-program plan.

The tracked plan is ``docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V1.json`` with
its rendered companion ``docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V1.md``.
The plan restores the six-phase Modular Whole-Economy Zeno Recursive Proof
Fabric program as exact task rows with live statuses. This tool decides
whether the plan is internally consistent and whether its recorded live-gate
observations still describe the checked-out tree.

Security boundary: the plan file is candidate-controlled data and never
selects code to run. Executable gates live only in
``tools.live_gate_registry_v1``; a plan gate may mirror one registry entry,
validation requires exact equality of argv, checker path, output format,
projection, and timeout, and execution runs only from an immutable effect
plan built after every full row and the exact registry set validated.
Children run in their own session with an explicit environment (``PATH``,
``HOME``, and ``PYTHONPATH`` are never inherited; user site is disabled).
Gate and supervisor interpreters start with ``-I`` and receive the
descriptor-bound repository import root only after startup, so tracked
``sitecustomize.py`` cannot widen their path. A fail-closed preflight also
requires ``root/external/ESSO`` to be safely resolved as absent. Descendants
that outlive their parent are reparented to the dedicated supervisor and
killed. The environment is explicit rather than fully hermetic. Every JSON value in the
plan is typed-checked before any membership test, so a hostile type in any
field is a finding, never an exception. All JSON input is decoded through
``tools.bounded_json_v1``. The repository root is one persistent
descriptor-backed capability (``ConfinedRootV1``) for the complete
validate-plan-execute-report invocation: the pathname is opened one
component at a time with ``O_NOFOLLOW`` (a symlink anywhere in it is
refused, never resolved), the descriptor is kept for the whole invocation,
and every git call, status and snapshot listing, stat, read, replacement,
checker hash, and child process addresses that inode, so a pathname swapped
to another directory or an inode reused after deletion never redirects any
step; a mount or bind mount inside the tree is refused. Both plan artifacts
and every referenced file are read without following symlinks anywhere in
their path. Before ordinary decoding, the exact ``HEAD:path`` blobs are read,
both worktree artifacts are captured in held write-sealed descriptors, and
only byte-identical held snapshots are decoded and rendered. Regeneration
replaces the artifacts atomically inside their confined directory. Execution
contexts and live-gate effects are immutable trusted-process records, not
unforgeable capabilities: every consumer rechecks their root, exact HEAD,
artifact digests, full cleanliness, source snapshot, and bounded write-sealed
checker/supervisor snapshots before use. Validation runs under exactly one of three closed
profiles: ordinary (full cleanliness, every comparison), pre-regeneration
(regeneration cleanliness, structure only), post-regeneration (regeneration
cleanliness, every comparison).

JSON contract (stdout, ``--json`` or any failure)::

    {
      "schema": "zenodex/whole-program-plan-check/v1",
      "ok": bool,
      "findings": [{"rule_id": str, "subject": str, "evidence": str}],
      "task_count": int,
      "closed_task_count": int,
      "vm_gate_status": {"VM-01": "PARTIAL", ...},
      "authority": {"production_authority": "NONE", ...},
      "executed_live_gates": int
    }

Subject binding is non-circular: the plan records the program base commit
(which must be an ancestor of, or equal to, HEAD) and a source-snapshot digest
over HEAD's committed tree entries except the two plan artifacts. Cleanliness
is recomputed from git status and required before structural success and
before any gate executes; the recorded Boolean is never trusted. Every
ordinary check and every execution uses ``FULL`` scope, in which both plan
artifacts are sealed and must byte-match their exact pre-read ``HEAD:path``
blobs; only the ``--refresh`` and
``--render`` phase, which rewrites those two files, uses ``REGENERATION``
scope that ignores exactly those two paths. A commit cannot contain its own
identifier, so the candidate SHA is never recorded; a fresh detached checkout
of the candidate reproduces the digest exactly, a superseded provisional commit
fails lineage, and any edit after regeneration is reported as
``scoped_worktree_dirty`` or ``source_snapshot_drift``.

Modes: default structural validation; ``--execute`` re-runs every registry
gate and compares projected observations and exit codes; ``--refresh
--observed-at YYYY-MM-DD`` regenerates observations and the subject binding
(evidence pins are recomputed only for tasks named with ``--repin-evidence``);
``--render`` rewrites the generated markdown block.

Exit codes: 0 valid plan, 1 findings, 2 unreadable input or invalid
invocation. The checker grants no authority; the authority ceiling is a closed
constant.
"""

from __future__ import annotations

import argparse
import copy
import datetime
import enum
import hashlib
import json
import os
import re
import stat
import sys
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final, NoReturn, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
if not __package__ and str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.bounded_json_v1 import (  # noqa: E402
    PLAN_JSON_LIMITS_V1,
    BoundedJsonError,
    decode_bounded_json_v1,
)
from tools.live_gate_registry_v1 import (  # noqa: E402
    LIVE_GATE_REGISTRY,
    AnchoredDirectoryV1,
    AnchoredFileV1,
    AnchorRefused,
    LiveGateObservationV1,
    LiveGateSpecV1,
    SupervisorCodeV1,
    bind_supervisor_code_v1,
    git_bytes_v1,
    git_v1,
    observe_live_gate_v1,
)
from tools.whole_program_artifact_binding_v1 import (  # noqa: E402
    MAX_PLAN_MARKDOWN_BYTES_V1,
    PLAN_JSON_ARTIFACT_PATH_V1,
    PLAN_MARKDOWN_ARTIFACT_PATH_V1,
    BoundPlanArtifactsV1,
    PlanArtifactBindingFindingV1,
    bind_plan_artifacts_v1,
)
from tools.whole_program_artifact_binding_v1 import (  # noqa: E402
    PLAN_ARTIFACT_SPECS_V1 as _BOUND_PLAN_ARTIFACT_SPECS_V1,
)

PLAN_JSON_PATH: Final = Path(PLAN_JSON_ARTIFACT_PATH_V1)
PLAN_MARKDOWN_PATH: Final = Path(PLAN_MARKDOWN_ARTIFACT_PATH_V1)
CLOSURE_LEDGER_PATH: Final = Path("docs/research/ZENODEX_VALUE_MOVEMENT_CLOSURE_STATUS_V1.json")
SCHEMA_V1: Final = "zenodex/whole-program-plan/v1"
CHECK_SCHEMA_V1: Final = "zenodex/whole-program-plan-check/v1"
MAX_PLAN_MARKDOWN_BYTES: Final = MAX_PLAN_MARKDOWN_BYTES_V1
PLAN_ARTIFACT_SPECS_V1: Final = _BOUND_PLAN_ARTIFACT_SPECS_V1
PHASE_IDS: Final[tuple[str, ...]] = ("P1", "P2", "P3", "P4", "P5", "P6")
VM_GATE_IDS: Final[tuple[str, ...]] = tuple(f"VM-{index:02d}" for index in range(1, 13))
VM_GATE_STATUSES: Final = frozenset({"GAP", "PARTIAL", "PASS"})
TASK_STATUSES: Final = frozenset(
    {"OPEN", "IN_PROGRESS", "BLOCKED_EXTERNAL", "DEFERRED_SEMANTIC_DECISION", "DONE_BOUNDED", "DONE"}
)
CLOSED_TASK_STATUSES: Final = frozenset({"DONE_BOUNDED", "DONE"})
FINDING_STATUSES: Final = frozenset({"OPEN", "CONTAINED", "CLOSED", "HISTORICAL"})
FINDING_SEVERITIES: Final = frozenset({"High", "Medium-High", "Medium", "Low", "Info"})
EVIDENCE_KINDS: Final = frozenset({"checker", "test", "doc", "manifest", "commit", "external"})
FILE_EVIDENCE_KINDS: Final = frozenset({"checker", "test", "doc", "manifest"})
TASK_ID_RE: Final = re.compile(r"P[1-6]-T[0-9]{2}\Z")
FINDING_ID_RE: Final = re.compile(r"(?:F-[0-9]{2}|H[1-9]|I[1-9]|B-[0-9]{2})\Z")
POLICY_ID_RE: Final = re.compile(r"UP-[0-9]{2}\Z")
HEAVY_GATE_ID_RE: Final = re.compile(r"HG-[0-9]{2}\Z")
COMMIT_RE: Final = re.compile(r"[0-9a-f]{40}\Z")
SHA256_RE: Final = re.compile(r"[0-9a-f]{64}\Z")
DATE_RE: Final = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}\Z")
MUTATION_KILLER_RE: Final = re.compile(r"(tests/[A-Za-z0-9_/.-]+\.py)::(test_[A-Za-z0-9_]+)\Z")
ABSOLUTE_PATH_TOKEN_RE: Final = re.compile(r"(?:^|[\s\"'=(,])(?:/|~/|[A-Za-z]:\\)")
REQUIRED_AUTHORITY: Final[Mapping[str, object]] = {
    "claim_authority": "NONE",
    "production_authority": "NONE",
    "production_ready": False,
    "release_ready": False,
}
TOP_LEVEL_FIELDS: Final = frozenset(
    {
        "schema", "program", "subject", "authority", "semantic_anchors", "phases", "tasks",
        "vm_gate_status", "finding_registry", "unresolved_policies", "live_gates",
        "external_gates", "heavy_gates_requiring_runpod", "test_execution_receipt",
        "regeneration", "nonclaims",
    }
)
SUBJECT_FIELDS: Final = frozenset(
    {
        "branch", "base_commit", "source_snapshot_sha256", "source_snapshot_file_count",
        "observed_at", "scoped_worktree_clean",
    }
)
PLAN_ARTIFACT_PATHS: Final = frozenset({PLAN_JSON_PATH.as_posix(), PLAN_MARKDOWN_PATH.as_posix()})
MAX_SOURCE_LISTING_BYTES: Final = 8 * 1024 * 1024
MAX_HASHED_FILE_BYTES: Final = 64 * 1024 * 1024
ZERO_OID: Final = "0" * 40
PHASE_FIELDS: Final = frozenset({"phase_id", "title", "original_plan_section", "objective"})
TASK_FIELDS: Final = frozenset(
    {
        "task_id", "phase_id", "title", "status", "depends_on", "vm_gates", "findings", "evidence",
        "claims_vm_improvement", "ripr_counterexample", "mutation_killers",
        "semantic_decisions_avoided", "nonclaims", "notes",
    }
)
EVIDENCE_FIELDS: Final = frozenset({"kind", "reference", "sha256"})
VM_GATE_FIELDS: Final = frozenset({"gate_id", "status", "decisive_remaining_condition", "tasks"})
FINDING_FIELDS: Final = frozenset({"finding_id", "title", "severity", "status", "source"})
POLICY_FIELDS: Final = frozenset({"policy_id", "statement", "source", "implementation_rule"})
LIVE_GATE_FIELDS: Final = frozenset(
    {
        "gate_id", "command", "checker_path", "checker_sha256", "output_format",
        "observed_projection", "observed", "exit_code", "timeout_seconds", "purpose",
    }
)
EXTERNAL_GATE_FIELDS: Final = frozenset({"gate_id", "location", "purpose", "executed_by_checker"})
HEAVY_GATE_FIELDS: Final = frozenset({"gate_id", "command", "reason", "workspace", "last_recorded_evidence"})
RECEIPT_FIELDS: Final = frozenset(
    {"command", "passed", "failed", "duration_seconds", "failed_tests", "evidence_authority", "interpreter", "subject_commit"}
)
REGENERATION_FIELDS: Final = frozenset(
    {"refresh_command", "render_command", "check_command", "execute_command", "evidence_repin_rule"}
)
GENERATED_BEGIN: Final = (
    "<!-- BEGIN GENERATED PLAN TABLES: regenerate with "
    "python3 tools/check_whole_program_plan_v1.py --render -->"
)
GENERATED_END: Final = "<!-- END GENERATED PLAN TABLES -->"
NONCLAIMS: Final[tuple[str, ...]] = (
    "a valid plan records statuses and pins evidence; it grants no production, settlement, or publication authority",
    "live-gate observations describe the checked-out tree at the recorded subject as deterministic local evidence under a "
    "trusted git store and trusted transitive code; top-level checker and supervisor execution uses immutable sealed snapshots, "
    "while a transitive dependency or git-metadata change reverted before the post-execution checks is not detected",
    "evidence hash pins prove byte identity, not semantic sufficiency, of the referenced artifacts",
    "task closure statuses are bounded by each task's declared nonclaims",
    "a live-gate observation attests the sealed top-level checker and supervisor bytes, the registry argv, the explicit "
    "environment, the anchored working directory, and the committed source snapshot before and after execution; modules the checker imports are "
    "resolved by name from the bound root during execution and are not attested (a dependency swapped and restored between "
    "the two snapshot checks is not detected); transitive repository code is trusted, not attested",
    "gate containment covers descendants of a gate that outlive it under a live dedicated supervisor; a gate that kills its "
    "supervisor or double-forks into a new session before losing it is outside the sandbox claim and yields a typed "
    "parent-side failure naming possible orphans, never a success",
    "git runs with a descriptor-bound working directory and disables replacement-object resolution, but remaining git metadata, "
    "refs, worktree administrative paths, commondir, and the object store are not separately descriptor-bound or attested and can be raced by a same-host adversary (in a "
    "linked worktree the .git file indirection may point outside the anchored root), so lineage, status, and "
    "source_snapshot are deterministic local evidence under a trusted git store, not an adversarially immutable repository "
    "snapshot",
    "ExecutionContextV1 and LiveGateEffectV1 are caller-constructible same-process Python values used as trusted-process "
    "conventions; they are not unforgeable capabilities and do not defend against code already executing in the checker process",
)


class PlanCheckModeV1(enum.Enum):
    STRUCTURAL = "structural"
    EXECUTE = "execute"


class CleanlinessScopeV1(enum.Enum):
    """Which paths must match the committed subject.

    ``FULL`` is every ordinary check and execution: the whole worktree,
    including both plan artifacts, must be clean. ``REGENERATION`` is only the
    ``--refresh``/``--render`` phase that rewrites the two plan artifacts, so
    those two paths alone may differ.
    """

    FULL = "full"
    REGENERATION = "regeneration"


class PlanValidationKindV1(enum.Enum):
    """The three closed validation profiles.

    ``ORDINARY`` is every public check: ``FULL`` cleanliness and every
    comparison. ``PRE_REGENERATION`` runs before any gate executes or any
    artifact byte is written: ``REGENERATION`` cleanliness, complete structure,
    but it skips only the values regeneration is about to rewrite (live-gate
    observations, exit codes, and checker digests; the source-snapshot
    comparison; the recorded cleanliness flag; the generated markdown block;
    and evidence digests of tasks explicitly named for re-pin).
    ``POST_REGENERATION`` is the report issued right after the artifacts were
    rewritten and before they are committed: ``REGENERATION`` cleanliness with
    every comparison. No other combination exists.
    """

    ORDINARY = "ordinary"
    PRE_REGENERATION = "pre_regeneration"
    POST_REGENERATION = "post_regeneration"


@dataclass(frozen=True, slots=True)
class PlanValidationProfileV1:
    """One closed validation kind plus the tasks whose evidence is being re-pinned.

    Cleanliness scope derives from the kind and is never caller-selected;
    re-pin tasks are accepted only with ``PRE_REGENERATION``.
    """

    kind: PlanValidationKindV1
    repin_tasks: frozenset[str] = frozenset()

    def __post_init__(self) -> None:
        if type(self.kind) is not PlanValidationKindV1:
            raise ValueError("validation kind must be one of the closed profiles")
        if type(self.repin_tasks) is not frozenset or not all(type(item) is str for item in self.repin_tasks):
            raise ValueError("re-pin tasks must be a frozenset of task ids")
        if self.repin_tasks and self.kind is not PlanValidationKindV1.PRE_REGENERATION:
            raise ValueError("evidence re-pin is only meaningful before regeneration")

    @property
    def cleanliness(self) -> CleanlinessScopeV1:
        return CleanlinessScopeV1.FULL if self.kind is PlanValidationKindV1.ORDINARY else CleanlinessScopeV1.REGENERATION

    @property
    def compares_regenerable(self) -> bool:
        return self.kind is not PlanValidationKindV1.PRE_REGENERATION

    @classmethod
    def pre_regeneration(cls, repin_tasks: Iterable[str] = ()) -> PlanValidationProfileV1:
        return cls(PlanValidationKindV1.PRE_REGENERATION, frozenset(repin_tasks))


ORDINARY_VALIDATION_PROFILE_V1: Final = PlanValidationProfileV1(PlanValidationKindV1.ORDINARY)
POST_REGENERATION_PROFILE_V1: Final = PlanValidationProfileV1(PlanValidationKindV1.POST_REGENERATION)
NARRATIVE_BASE_DEFECT_RANGE_RE: Final = re.compile(r"`B-01` through `B-(\d{2})`")
MAX_TREE_PATH_COMPONENTS: Final = 64
TREE_MODE_TYPES: Final[Mapping[str, str]] = {
    "100644": "blob",
    "100755": "blob",
    "120000": "blob",
    "160000": "commit",
}


@dataclass(frozen=True, slots=True)
class PlanFinding:
    rule_id: str
    subject: str
    evidence: str

    def __post_init__(self) -> None:
        for field in ("rule_id", "subject", "evidence"):
            value = getattr(self, field)
            if type(value) is not str:
                raise TypeError(
                    f"PlanFinding.{field} must be an exact string, received "
                    f"{type(value).__name__}"
                )

    def to_dict(self) -> dict[str, str]:
        return {"evidence": self.evidence, "rule_id": self.rule_id, "subject": self.subject}


def _plan_finding_is_closed_v1(value: object) -> bool:
    """Defend the report boundary from same-process forged dataclass fields."""

    return type(value) is PlanFinding and all(
        type(getattr(value, field, None)) is str
        for field in ("rule_id", "subject", "evidence")
    )


MAX_PUBLIC_PLAN_DEPTH_V1: Final = 64
MAX_PUBLIC_PLAN_NODES_V1: Final = 100_000


def _owned_plan_value_v1(
    value: object,
    *,
    path: str,
    depth: int,
    node_count: list[int],
) -> tuple[object | None, PlanFinding | None]:
    """Copy an exact JSON subset into checker-owned builtins.

    Public callers may supply Python subclasses with hostile equality or
    iteration. The checker accepts only exact builtins, refuses floats, and
    owns a recursive copy before any semantic validator or report projection
    observes the value.
    """

    node_count[0] += 1
    if depth > MAX_PUBLIC_PLAN_DEPTH_V1 or node_count[0] > MAX_PUBLIC_PLAN_NODES_V1:
        return None, PlanFinding(
            "plan_value_not_owned",
            path,
            "public plan exceeds the owned-value depth or node bound",
        )
    if value is None or type(value) in (str, int, bool):
        return value, None
    if type(value) is list:
        owned_items: list[object] = []
        try:
            snapshot = tuple(value)
        except (MemoryError, RuntimeError) as exc:
            return None, PlanFinding(
                "plan_value_not_owned", path, f"list snapshot refused: {type(exc).__name__}"
            )
        for index, item in enumerate(snapshot):
            owned, finding = _owned_plan_value_v1(
                item,
                path=f"{path}[{index}]",
                depth=depth + 1,
                node_count=node_count,
            )
            if finding is not None:
                return None, finding
            owned_items.append(owned)
        return owned_items, None
    if type(value) is dict:
        owned_mapping: dict[str, object] = {}
        try:
            snapshot = tuple(value.items())
        except (MemoryError, RuntimeError) as exc:
            return None, PlanFinding(
                "plan_value_not_owned", path, f"mapping snapshot refused: {type(exc).__name__}"
            )
        for key, item in snapshot:
            if type(key) is not str:
                return None, PlanFinding(
                    "plan_value_not_owned",
                    path,
                    f"mapping key must be an exact string, received {type(key).__name__}",
                )
            owned, finding = _owned_plan_value_v1(
                item,
                path=f"{path}.{key}",
                depth=depth + 1,
                node_count=node_count,
            )
            if finding is not None:
                return None, finding
            owned_mapping[key] = owned
        return owned_mapping, None
    return None, PlanFinding(
        "plan_value_not_owned",
        path,
        f"expected an exact JSON scalar, list, or mapping, received {type(value).__name__}",
    )


def _owned_plan_v1(value: object) -> tuple[dict[str, object] | None, list[PlanFinding]]:
    owned, finding = _owned_plan_value_v1(
        value, path="plan", depth=0, node_count=[0]
    )
    if finding is not None:
        return None, [finding]
    if type(owned) is not dict:
        return None, [
            PlanFinding(
                "plan_value_not_owned", "plan", "top-level plan must be an exact mapping"
            )
        ]
    return owned, []


def _mode_or_findings_v1(mode: object) -> tuple[PlanCheckModeV1 | None, list[PlanFinding]]:
    """Require one exact closed mode before opening artifacts or deciding execution."""

    if type(mode) is PlanCheckModeV1:
        return mode, []
    return None, [
        PlanFinding(
            "plan_check_mode_invalid",
            "mode",
            f"expected PlanCheckModeV1, received {type(mode).__name__}",
        )
    ]


def _profile_or_findings_v1(
    profile: object,
) -> tuple[PlanValidationProfileV1 | None, list[PlanFinding]]:
    """Require one exact closed profile before it controls validation comparisons."""

    if type(profile) is not PlanValidationProfileV1:
        return None, [
            PlanFinding(
                "validation_profile_invalid",
                "profile",
                f"expected PlanValidationProfileV1, received {type(profile).__name__}",
            )
        ]
    if (
        type(profile.kind) is not PlanValidationKindV1
        or type(profile.repin_tasks) is not frozenset
        or not all(type(task_id) is str for task_id in profile.repin_tasks)
        or (profile.repin_tasks and profile.kind is not PlanValidationKindV1.PRE_REGENERATION)
    ):
        return None, [
            PlanFinding(
                "validation_profile_invalid",
                "profile",
                "profile fields do not encode one closed validation profile",
            )
        ]
    return profile, []


@dataclass(frozen=True, slots=True)
class PlanVocabularyV1:
    """Identifier sets a task row may reference, plus tasks whose evidence is being re-pinned."""

    finding_ids: frozenset[str]
    policy_ids: frozenset[str]
    repin_task_ids: frozenset[str] = frozenset()


@dataclass(frozen=True, slots=True)
class RowContractV1:
    """Shape contract for one identified registry list inside the plan."""

    subject: str
    fields: frozenset[str]
    id_field: str
    id_pattern: re.Pattern[str]
    checks: tuple[FieldCheck, ...]
    rule_prefix: str


class PlanUnreadable(ValueError):
    """The plan or one of its companions cannot be decoded within bounds."""


class PlanCliUsageError(ValueError):
    """A command-line invocation cannot select a closed plan-checker operation."""


class _ClosedPlanArgumentParser(argparse.ArgumentParser):
    """Convert parser failures into the same closed JSON-report path as every other refusal."""

    def error(self, message: str) -> NoReturn:
        raise PlanCliUsageError(message)


Predicate = Callable[[object], bool]
FieldCheck = tuple[str, Predicate, str]


def _is_nonempty_str(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _as_str_list(value: object) -> list[str] | None:
    if isinstance(value, list) and all(isinstance(item, str) for item in value):
        return list(value)
    return None


def _is_str_list(value: object) -> bool:
    return _as_str_list(value) is not None


def _is_unique_str_list(value: object) -> bool:
    items = _as_str_list(value)
    return items is not None and len(set(items)) == len(items)


def _is_sorted_str_list(value: object) -> bool:
    items = _as_str_list(value)
    return items is not None and items == sorted(items)


def _is_bool(value: object) -> bool:
    return type(value) is bool


def _is_int(value: object) -> bool:
    return type(value) is int


def _is_nonneg_int(value: object) -> bool:
    return type(value) is int and value >= 0


def _is_commit(value: object) -> bool:
    return isinstance(value, str) and COMMIT_RE.fullmatch(value) is not None


def _is_sha256(value: object) -> bool:
    return isinstance(value, str) and SHA256_RE.fullmatch(value) is not None


def _is_date(value: object) -> bool:
    """A real calendar date written exactly as ``YYYY-MM-DD``."""

    if not isinstance(value, str) or DATE_RE.fullmatch(value) is None:
        return False
    try:
        datetime.date.fromisoformat(value)
    except ValueError:
        return False
    return True


def _is_repo_relative(value: object) -> bool:
    if not _is_nonempty_str(value):
        return False
    path = Path(str(value))
    return not path.is_absolute() and ".." not in path.parts


def _is_location_without_absolute_path(value: object) -> bool:
    """External gate locations are logical names; machine-specific absolute paths are rejected."""

    return isinstance(value, str) and ABSOLUTE_PATH_TOKEN_RE.search(value) is None


def _matches(pattern: re.Pattern[str]) -> Predicate:
    return lambda value: isinstance(value, str) and pattern.fullmatch(value) is not None


def _in(universe: Iterable[str]) -> Predicate:
    members = frozenset(universe)
    return lambda value: isinstance(value, str) and value in members


def _subset_of(universe: Iterable[str]) -> Predicate:
    members = frozenset(universe)

    def predicate(value: object) -> bool:
        items = _as_str_list(value)
        return items is not None and set(items) <= members

    return predicate


def _shape(value: object, expected: frozenset[str], *, rule: str, subject: str) -> PlanFinding | None:
    if isinstance(value, Mapping) and set(value) == expected:
        return None
    return PlanFinding(rule, subject, ",".join(sorted(expected)))


def _check_fields(value: Mapping[str, Any], checks: Sequence[FieldCheck], subject: str) -> list[PlanFinding]:
    return [PlanFinding(rule, subject, field) for field, predicate, rule in checks if not predicate(value[field])]


_FILE_FLAGS: Final = os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK


class ConfinementError(OSError):
    """A confined path operation was refused before any file was touched."""


class RootUnavailable(PlanUnreadable):
    """The repository root could not be bound (symlink component, missing, not a directory, mount policy)."""


class ConfinedRootV1:
    """One persistent descriptor-backed root capability for a complete invocation.

    ``bind`` opens the lexically absolute pathname one component at a time
    with ``O_NOFOLLOW`` (a symlink anywhere in the root path is refused, never
    resolved) and keeps that descriptor for the whole invocation. Every git
    call, status and snapshot listing, stat, read, replacement, checker hash,
    and child process works through this descriptor, so a pathname swapped
    to another directory, or an inode reused after the root was deleted, can
    never redirect any step. Effects are bound to the capability object
    itself and refuse any other root.
    """

    __slots__ = ("path", "anchored")

    def __init__(self, path: Path, anchored: AnchoredDirectoryV1) -> None:
        self.path = path
        self.anchored = anchored

    @classmethod
    def bind(cls, root: Path | ConfinedRootV1) -> ConfinedRootV1:
        if isinstance(root, ConfinedRootV1):
            return root
        path = Path(os.path.abspath(root))
        try:
            anchored = AnchoredDirectoryV1.open(path)
        except OSError as exc:
            raise RootUnavailable(f"repository root refused: {exc}") from exc
        return cls(path, anchored)

    @property
    def device(self) -> int:
        return self.anchored.device

    @property
    def inode(self) -> int:
        return self.anchored.inode

    @property
    def is_open(self) -> bool:
        return self.anchored.is_open

    def close(self) -> None:
        self.anchored.close()

    def __enter__(self) -> ConfinedRootV1:
        return self

    def __exit__(self, *_exc: object) -> None:
        self.close()


RootLike = Path | ConfinedRootV1


class _UseRoot:
    """Reuse the caller's persistent capability unchanged, or bind an ad-hoc one for exactly this operation."""

    __slots__ = ("root", "bound", "owned")

    def __init__(self, root: RootLike) -> None:
        self.root = root
        self.bound: ConfinedRootV1 | None = None
        self.owned = False

    def __enter__(self) -> ConfinedRootV1:
        if isinstance(self.root, ConfinedRootV1):
            self.bound = self.root
        else:
            self.bound = ConfinedRootV1.bind(self.root)
            self.owned = True
        return self.bound

    def __exit__(self, *_exc: object) -> None:
        if self.owned and self.bound is not None:
            self.bound.close()


def _git_bytes(root: RootLike, args: Sequence[str], *, max_output_bytes: int) -> bytes | None:
    """Trusted git addressed through the bound root descriptor; ``None`` on any refusal or bound breach."""

    try:
        with _UseRoot(root) as bound:
            return git_bytes_v1(bound.anchored, args, max_output_bytes=max_output_bytes)
    except (OSError, PlanUnreadable):
        return None


def _git(root: RootLike, args: Sequence[str]) -> tuple[int, str]:
    """Trusted git addressed through the bound root descriptor; ``(-1, "")`` on any refusal or bound breach."""

    try:
        with _UseRoot(root) as bound:
            return git_v1(bound.anchored, args)
    except (OSError, PlanUnreadable):
        return -1, ""


@dataclass(frozen=True, slots=True)
class ConfinedReadV1:
    """Bytes of one regular file reached without following any symlink; ``reason`` names the refusal."""

    data: bytes | None
    reason: str


def _confined_parts(relative: Path) -> tuple[str, ...] | None:
    parts = relative.parts
    if relative.is_absolute() or not parts or any(part in {"", ".", ".."} or "/" in part for part in parts):
        return None
    return parts


def _open_confined(root: ConfinedRootV1, relative: Path, flags: int, mode: int = 0o644) -> int:
    """Open ``root/relative`` through the persistent root descriptor; no component may be a symlink or cross a mount."""

    parts = _confined_parts(relative)
    if parts is None:
        raise ValueError(f"{relative.as_posix()} is not a canonical repository-relative path")
    return root.anchored.open_entry(parts, flags, mode)


def _refusal(relative: Path, exc: BaseException) -> str:
    if isinstance(exc, (ConfinementError, PlanUnreadable, AnchorRefused)):
        return str(exc)
    return f"{relative.as_posix()} is not reachable without following a symlink: {type(exc).__name__}"


def _root_unavailable(exc: RootUnavailable) -> list[PlanFinding]:
    return [PlanFinding("root_unavailable", "root", str(exc))]


def _read_descriptor(descriptor: int, max_bytes: int) -> ConfinedReadV1:
    info = os.fstat(descriptor)
    if not stat.S_ISREG(info.st_mode):
        return ConfinedReadV1(None, "not a regular file")
    if info.st_size > max_bytes:
        return ConfinedReadV1(None, f"exceeds {max_bytes} bytes")
    chunks: list[bytes] = []
    remaining = max_bytes + 1
    while remaining > 0:
        chunk = os.read(descriptor, min(remaining, 1024 * 1024))
        if not chunk:
            break
        chunks.append(chunk)
        remaining -= len(chunk)
    data = b"".join(chunks)
    return ConfinedReadV1(None, f"exceeds {max_bytes} bytes") if len(data) > max_bytes else ConfinedReadV1(data, "")


def read_confined_file_v1(root: RootLike, relative: Path, *, max_bytes: int) -> ConfinedReadV1:
    """Read a regular file through the bound root descriptor with no symlink following anywhere in the path."""

    try:
        with _UseRoot(root) as bound:
            try:
                descriptor = _open_confined(bound, relative, os.O_RDONLY)
            except FileNotFoundError:
                return ConfinedReadV1(None, "missing")
            except (OSError, ValueError) as exc:
                return ConfinedReadV1(None, _refusal(relative, exc))
            try:
                return _read_descriptor(descriptor, max_bytes)
            except OSError as exc:
                return ConfinedReadV1(None, f"unreadable: {type(exc).__name__}")
            finally:
                os.close(descriptor)
    except PlanUnreadable as exc:
        return ConfinedReadV1(None, str(exc))


def replace_confined_file_v1(root: RootLike, relative: Path, data: bytes) -> str:
    """Atomically replace a regular file through the bound root descriptor; returns ``""`` or the refusal reason.

    The new bytes are written to a fresh ``O_EXCL`` temporary entry in the
    same confined directory and renamed over the target; rename never follows
    the target, so a symlink swapped in at any moment is replaced, never
    written through. The existing target must be a regular file or absent.
    """

    parts = _confined_parts(relative)
    if parts is None:
        return f"{relative.as_posix()} is not a canonical repository-relative path"
    name = parts[-1]
    temporary = f".{name}.{os.getpid()}.tmp"
    try:
        with _UseRoot(root) as bound:
            directory = bound.anchored.walk(parts)
    except (OSError, PlanUnreadable) as exc:
        return _refusal(relative, exc)
    try:
        try:
            existing = os.stat(name, dir_fd=directory, follow_symlinks=False)
        except FileNotFoundError:
            existing = None
        if existing is not None and not stat.S_ISREG(existing.st_mode):
            return f"{relative.as_posix()} is not a regular file"
        descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | _FILE_FLAGS, 0o644, dir_fd=directory)
        try:
            view = memoryview(data)
            while view:
                written = os.write(descriptor, view)
                view = view[written:]
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        os.rename(temporary, name, src_dir_fd=directory, dst_dir_fd=directory)
        os.fsync(directory)
        return ""
    except OSError as exc:
        try:
            os.unlink(temporary, dir_fd=directory)
        except OSError:
            pass
        return f"cannot replace {relative.as_posix()}: {type(exc).__name__}"
    finally:
        os.close(directory)


def _confined_stat(root: ConfinedRootV1, relative: Path) -> os.stat_result | None:
    """Stat of the entry itself (no symlink followed anywhere) through the bound root, or ``None``."""

    try:
        descriptor = _open_confined(root, relative, os.O_PATH)
    except (OSError, ValueError):
        return None
    try:
        return os.fstat(descriptor)
    finally:
        os.close(descriptor)


def _is_regular_file(root: ConfinedRootV1, relative: str) -> bool:
    """Whether ``relative`` is a regular file reached through the bound root without following any symlink."""

    info = _confined_stat(root, Path(relative))
    return info is not None and stat.S_ISREG(info.st_mode)


def _sha256_file(root: ConfinedRootV1, relative: str) -> str | None:
    """SHA-256 of a regular file hashed from a descriptor opened through the bound root; ``None`` when refused."""

    if _confined_parts(Path(relative)) is None:
        return None
    try:
        with root.anchored.open_file(relative) as checker:
            return checker.sha256
    except OSError:
        return None


def _decode_plan_json_bytes_v1(data: bytes, *, name: str) -> Mapping[str, Any]:
    """Decode one already bounded artifact byte string into a plan mapping."""

    try:
        value = decode_bounded_json_v1(data, name=name, limits=PLAN_JSON_LIMITS_V1)
    except BoundedJsonError as exc:
        raise PlanUnreadable(f"cannot read {name}: {exc}") from exc
    if not isinstance(value, Mapping):
        raise PlanUnreadable(f"{name} root must be an object")
    return value


def _read_bounded_json_file(root: ConfinedRootV1, relative: Path, *, name: str) -> Mapping[str, Any]:
    read = read_confined_file_v1(root, relative, max_bytes=PLAN_JSON_LIMITS_V1.max_bytes)
    if read.data is None:
        raise PlanUnreadable(f"cannot read {name}: {read.reason}")
    return _decode_plan_json_bytes_v1(read.data, name=name)


def _decode_plan_markdown_bytes_v1(data: bytes) -> str:
    try:
        return data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise PlanUnreadable(
            f"plan markdown is not valid UTF-8 at byte {exc.start}"
        ) from exc


def _decode_bound_plan_artifacts_v1(
    artifacts: BoundPlanArtifactsV1,
) -> tuple[Mapping[str, Any], str]:
    """Decode only the held exact-HEAD artifact snapshots."""

    plan_bytes = artifacts.bytes_for(PLAN_JSON_PATH.as_posix())
    markdown_bytes = artifacts.bytes_for(PLAN_MARKDOWN_PATH.as_posix())
    if plan_bytes is None or markdown_bytes is None:
        raise PlanUnreadable("bound plan artifact pair is incomplete")
    plan = _decode_plan_json_bytes_v1(plan_bytes, name=f"plan {PLAN_JSON_PATH.name}")
    markdown = _decode_plan_markdown_bytes_v1(markdown_bytes)
    return plan, markdown


def load_plan_v1(root: RootLike) -> Mapping[str, Any]:
    """Load the tracked plan JSON through the bound root descriptor within the closed decode bounds."""

    with _UseRoot(root) as bound:
        return _read_bounded_json_file(bound, PLAN_JSON_PATH, name=f"plan {PLAN_JSON_PATH.name}")


def read_plan_markdown_v1(root: RootLike) -> str | None:
    """UTF-8 text of the tracked markdown companion, ``None`` when absent, ``PlanUnreadable`` otherwise."""

    with _UseRoot(root) as bound:
        read = read_confined_file_v1(bound, PLAN_MARKDOWN_PATH, max_bytes=MAX_PLAN_MARKDOWN_BYTES)
    if read.data is None:
        if read.reason == "missing":
            return None
        raise PlanUnreadable(f"cannot read plan markdown: {read.reason}")
    return _decode_plan_markdown_bytes_v1(read.data)


def _tree_entry(root: ConfinedRootV1, relative: Path) -> tuple[str, str] | None:
    """``(mode, type)`` of ``relative`` in HEAD, or ``None`` when absent or unreadable."""

    listing = _git_bytes(root, ["ls-tree", "-z", "HEAD", "--", relative.as_posix()], max_output_bytes=4096)
    if not listing:
        return None
    entry, _reason = _parse_tree_record(listing.split(b"\0", 1)[0])
    return (entry[1], entry[2]) if entry is not None and os.fsdecode(entry[0]) == relative.as_posix() else None


def plan_artifact_findings_v1(root: RootLike) -> list[PlanFinding]:
    """Both plan artifacts must be committed regular blobs and regular worktree files (no symlink, dir, FIFO, or device).

    Both checks address the bound root inode: git runs anchored to it and the
    worktree entry is stat'ed through a no-follow walk from it.
    """

    try:
        with _UseRoot(root) as bound:
            return _artifact_findings(bound)
    except RootUnavailable as exc:
        return _root_unavailable(exc)


def _artifact_findings(bound: ConfinedRootV1) -> list[PlanFinding]:
    findings: list[PlanFinding] = []
    for relative in (PLAN_JSON_PATH, PLAN_MARKDOWN_PATH):
        committed = _tree_entry(bound, relative)
        if committed is None:
            findings.append(PlanFinding("plan_artifact_not_committed", relative.as_posix(), "absent from HEAD"))
        elif committed != ("100644", "blob"):
            findings.append(PlanFinding("plan_artifact_committed_not_regular", relative.as_posix(), " ".join(committed)))
        info = _confined_stat(bound, relative)
        if info is None:
            findings.append(PlanFinding("plan_artifact_not_regular_file", relative.as_posix(), "missing or not reachable without following a symlink"))
        elif not stat.S_ISREG(info.st_mode):
            findings.append(PlanFinding("plan_artifact_not_regular_file", relative.as_posix(), stat.filemode(info.st_mode)))
    return findings


def _validate_top_level(plan: Mapping[str, Any]) -> list[PlanFinding]:
    shape = _shape(plan, TOP_LEVEL_FIELDS, rule="plan_field_set_not_closed", subject="plan")
    if shape is not None:
        return [shape]
    checks: tuple[FieldCheck, ...] = (
        ("schema", lambda value: value == SCHEMA_V1, "plan_schema_mismatch"),
        ("program", _is_nonempty_str, "plan_program_missing"),
        ("authority", lambda value: isinstance(value, Mapping) and dict(value) == dict(REQUIRED_AUTHORITY), "authority_ceiling_violated"),
        ("nonclaims", lambda value: _is_str_list(value) and bool(value), "nonclaims_missing"),
        ("regeneration", _is_regeneration_contract, "regeneration_contract_incomplete"),
    )
    return _check_fields(plan, checks, "plan")


def _is_regeneration_contract(value: object) -> bool:
    return isinstance(value, Mapping) and set(value) == REGENERATION_FIELDS and all(_is_nonempty_str(item) for item in value.values())


def lineage_findings_v1(root: RootLike, commit: str, subject: str) -> list[PlanFinding]:
    """Require ``commit`` to exist and to be an ancestor of, or equal to, HEAD (git anchored to the bound root)."""

    if _git(root, ["cat-file", "-e", f"{commit}^{{commit}}"])[0] != 0:
        return [PlanFinding("subject_commit_unknown", subject, commit)]
    head_code, head = _git(root, ["rev-parse", "HEAD"])
    if head_code != 0:
        return [PlanFinding("subject_head_unavailable", subject, "git rev-parse HEAD failed")]
    if _git(root, ["merge-base", "--is-ancestor", commit, head])[0] != 0:
        return [PlanFinding("subject_commit_not_in_lineage", subject, f"{commit} is not an ancestor of HEAD {head}")]
    return []


@dataclass(frozen=True, slots=True)
class SourceSnapshotV1:
    """Digest of HEAD's committed tree entries excluding the two plan artifacts."""

    sha256: str
    entry_count: int


def _canonical_tree_path(raw_path: bytes) -> str | None:
    """Decode one tree path and require the canonical nonempty repository-relative form."""

    try:
        path = raw_path.decode("utf-8", errors="strict")
    except UnicodeDecodeError:
        return None
    if not path or path.startswith("/") or "\\" in path or any(ord(char) < 32 or ord(char) == 127 for char in path):
        return None
    parts = path.split("/")
    if any(part in {"", ".", ".."} for part in parts) or len(parts) > MAX_TREE_PATH_COMPONENTS:
        return None
    return path


def _parse_tree_record(record: bytes) -> tuple[tuple[bytes, str, str, str] | None, str]:
    """Parse one ``ls-tree -z`` record; return ``(entry, "")`` or ``(None, reason)``."""

    try:
        metadata, raw_path = record.split(b"\t", 1)
        mode, object_type, oid = metadata.decode("ascii").split(" ")
    except (ValueError, UnicodeDecodeError):
        return None, "record is not <mode> <type> <oid>\\t<path>"
    if _canonical_tree_path(raw_path) is None:
        return None, "path is not canonical repository-relative"
    if TREE_MODE_TYPES.get(mode) != object_type:
        return None, f"mode/type pair {mode} {object_type} is not supported"
    if not _is_commit(oid) or oid == ZERO_OID:
        return None, "object id is not a nonzero lowercase 40-hex id"
    return (raw_path, mode, object_type, oid), ""


def snapshot_entries_from_listing_v1(listing: bytes) -> tuple[list[tuple[bytes, str, str, str]], list[PlanFinding]]:
    """Validate every ``ls-tree`` record; malformed or unsupported records are typed findings."""

    findings: list[PlanFinding] = []
    entries: list[tuple[bytes, str, str, str]] = []
    seen_paths: set[bytes] = set()
    for record in listing.split(b"\0"):
        if not record:
            continue
        entry, reason = _parse_tree_record(record)
        if entry is None:
            findings.append(PlanFinding("source_snapshot_entry_malformed", record[:80].decode("utf-8", errors="replace"), reason))
            continue
        if entry[0] in seen_paths:
            findings.append(PlanFinding("source_snapshot_entry_duplicate", os.fsdecode(entry[0]), "path listed twice"))
            continue
        seen_paths.add(entry[0])
        if os.fsdecode(entry[0]) in PLAN_ARTIFACT_PATHS:
            continue
        entries.append(entry)
    return entries, findings


def source_snapshot_v1(root: RootLike) -> tuple[SourceSnapshotV1 | None, list[PlanFinding]]:
    """Digest HEAD's committed tree except the plan artifacts, reading no worktree file.

    The plan binds this digest instead of the candidate commit SHA: a commit
    cannot contain its own identifier, but a fresh detached checkout of the
    candidate reproduces exactly these committed objects. Cleanliness is checked
    separately so the committed tree is also the working tree. Every record must
    carry an exact mode/type pair, a nonzero object id, and a canonical path;
    anything else is a typed finding, never skipped. Git is anchored to the
    bound root inode.
    """

    listing = _git_bytes(
        root, ["ls-tree", "-r", "-z", "--full-tree", "HEAD"], max_output_bytes=MAX_SOURCE_LISTING_BYTES
    )
    if listing is None:
        return None, [PlanFinding("source_snapshot_unavailable", "subject", "git ls-tree HEAD failed")]
    entries, findings = snapshot_entries_from_listing_v1(listing)
    if findings:
        return None, findings
    digest = hashlib.sha256()
    for raw_path, mode, object_type, oid in sorted(entries):
        digest.update(b"\0".join((mode.encode("ascii"), object_type.encode("ascii"), oid.encode("ascii"), raw_path)) + b"\0")
    return SourceSnapshotV1(digest.hexdigest(), len(entries)), []


def _status_entry_path(record: bytes) -> str | None:
    if record.startswith(b"1 "):
        parts = record.split(b" ", 8)
        return os.fsdecode(parts[8]) if len(parts) == 9 else None
    if record.startswith(b"u "):
        parts = record.split(b" ", 10)
        return os.fsdecode(parts[10]) if len(parts) == 11 else None
    if record.startswith(b"? "):
        return os.fsdecode(record[2:])
    return None


def scoped_worktree_dirty_paths_v1(root: RootLike, scope: CleanlinessScopeV1) -> list[str] | None:
    """Every modified, unmerged, or untracked path that must match the committed subject.

    ``REGENERATION`` scope ignores only the two plan artifacts; ``FULL`` scope
    ignores nothing. Returns ``None`` when git fails or emits a malformed record.
    Git is anchored to the bound root inode.
    """

    status = _git_bytes(
        root,
        ["status", "--porcelain=v2", "-z", "--untracked-files=all", "--no-renames"],
        max_output_bytes=MAX_SOURCE_LISTING_BYTES,
    )
    if status is None:
        return None
    excluded = PLAN_ARTIFACT_PATHS if scope is CleanlinessScopeV1.REGENERATION else frozenset()
    dirty: set[str] = set()
    for record in status.split(b"\0"):
        if not record:
            continue
        path = _status_entry_path(record)
        if path is None:
            return None
        if path not in excluded:
            dirty.add(path)
    return sorted(dirty)


def _cleanliness_findings(root: RootLike, recorded_clean: object, profile: PlanValidationProfileV1) -> list[PlanFinding]:
    dirty = scoped_worktree_dirty_paths_v1(root, profile.cleanliness)
    if dirty is None:
        return [PlanFinding("scoped_worktree_status_unavailable", "subject", "git status failed or returned a malformed record")]
    findings: list[PlanFinding] = []
    if dirty:
        findings.append(PlanFinding("scoped_worktree_dirty", "subject.scoped_worktree_clean", ",".join(dirty[:8])))
    if profile.compares_regenerable and recorded_clean is not (not dirty):
        findings.append(PlanFinding("scoped_worktree_clean_misrecorded", "subject.scoped_worktree_clean", f"recorded={recorded_clean} observed={not dirty}"))
    return findings


def _snapshot_findings(root: RootLike, subject: Mapping[str, Any]) -> list[PlanFinding]:
    snapshot, findings = source_snapshot_v1(root)
    if snapshot is None:
        return findings
    recorded = (subject["source_snapshot_sha256"], subject["source_snapshot_file_count"])
    if (snapshot.sha256, snapshot.entry_count) != recorded:
        return [PlanFinding("source_snapshot_drift", "subject.source_snapshot_sha256", f"recorded={recorded[0]}/{recorded[1]} observed={snapshot.sha256}/{snapshot.entry_count}")]
    return []


def subject_state_findings_v1(
    root: RootLike,
    subject: Mapping[str, Any],
    profile: PlanValidationProfileV1 = ORDINARY_VALIDATION_PROFILE_V1,
) -> list[PlanFinding]:
    """Recomputed lineage, cleanliness in the profile's scope, and committed-tree snapshot checks.

    Every git call is anchored to the bound root inode, so a pathname swapped
    to a clean twin during these checks cannot launder a dirty root.
    """

    try:
        with _UseRoot(root) as bound:
            findings = lineage_findings_v1(bound, str(subject["base_commit"]), "subject.base_commit")
            findings.extend(_cleanliness_findings(bound, subject["scoped_worktree_clean"], profile))
            if profile.compares_regenerable:
                findings.extend(_snapshot_findings(bound, subject))
            else:
                findings.extend(source_snapshot_v1(bound)[1])
            return findings
    except RootUnavailable as exc:
        return _root_unavailable(exc)


def _validate_subject(plan: Mapping[str, Any], root: ConfinedRootV1, profile: PlanValidationProfileV1) -> list[PlanFinding]:
    subject = plan["subject"]
    shape = _shape(subject, SUBJECT_FIELDS, rule="subject_field_set_not_closed", subject="subject")
    if shape is not None:
        return [shape]
    checks: tuple[FieldCheck, ...] = (
        ("branch", _is_nonempty_str, "subject_branch_missing"),
        ("base_commit", _is_commit, "subject_commit_malformed"),
        ("source_snapshot_sha256", _is_sha256, "subject_snapshot_malformed"),
        ("source_snapshot_file_count", _is_nonneg_int, "subject_snapshot_malformed"),
        ("observed_at", _is_date, "subject_observed_at_malformed"),
        ("scoped_worktree_clean", _is_bool, "subject_clean_flag_malformed"),
    )
    findings = _check_fields(subject, checks, "subject")
    return findings if findings else subject_state_findings_v1(root, subject, profile)


def _validate_semantic_anchors(plan: Mapping[str, Any], root: ConfinedRootV1) -> list[PlanFinding]:
    try:
        ledger = _read_bounded_json_file(root, CLOSURE_LEDGER_PATH, name="closure ledger")
    except PlanUnreadable as exc:
        return [PlanFinding("closure_ledger_unreadable", CLOSURE_LEDGER_PATH.as_posix(), str(exc))]
    expected = ledger.get("semantic_anchors")
    observed = plan["semantic_anchors"]
    if not isinstance(expected, Mapping) or not isinstance(observed, Mapping):
        return [PlanFinding("semantic_anchor_shape", "semantic_anchors", "must be objects")]
    expected_keys = set(expected)
    observed_keys = set(observed)
    if expected_keys != observed_keys:
        missing = sorted(expected_keys - observed_keys)
        extra = sorted(observed_keys - expected_keys)
        evidence = ";".join(
            part
            for part in (
                f"missing={','.join(missing)}" if missing else "",
                f"extra={','.join(extra)}" if extra else "",
            )
            if part
        )
        return [PlanFinding("semantic_anchor_drift", "semantic_anchors", evidence)]
    drift = sorted(key for key in expected_keys if expected[key] != observed[key])
    return [PlanFinding("semantic_anchor_drift", "semantic_anchors", ",".join(drift))] if drift else []


def _validate_phases(plan: Mapping[str, Any]) -> list[PlanFinding]:
    phases = plan["phases"]
    if not isinstance(phases, list):
        return [PlanFinding("phases_malformed", "phases", "must be a list")]
    checks: tuple[FieldCheck, ...] = (
        ("phase_id", _is_nonempty_str, "phase_text_missing"),
        ("title", _is_nonempty_str, "phase_text_missing"),
        ("objective", _is_nonempty_str, "phase_text_missing"),
        ("original_plan_section", lambda value: type(value) is int and value > 0, "phase_section_malformed"),
    )
    findings: list[PlanFinding] = []
    for index, phase in enumerate(phases):
        label = f"phases[{index}]"
        shape = _shape(phase, PHASE_FIELDS, rule="phase_field_set_not_closed", subject=label)
        findings.extend([shape] if shape is not None else _check_fields(phase, checks, label))
    ids = [str(phase.get("phase_id")) for phase in phases if isinstance(phase, Mapping)]
    if tuple(ids) != PHASE_IDS:
        findings.append(PlanFinding("phase_ids_not_canonical", "phases", ",".join(ids)))
    return findings


@dataclass(frozen=True, slots=True)
class EvidenceContextV1:
    """How one task's evidence rows are judged."""

    closed: bool
    compare_digests: bool


def _file_evidence_findings(item: Mapping[str, Any], *, label: str, context: EvidenceContextV1, root: ConfinedRootV1) -> list[PlanFinding]:
    reference, digest = str(item["reference"]), item["sha256"]
    if not _is_repo_relative(reference):
        return [PlanFinding("evidence_path_not_repo_relative", label, reference)]
    if not _is_regular_file(root, reference):
        return [PlanFinding("evidence_missing", label, reference)]
    if digest is None:
        return [PlanFinding("closed_task_evidence_unpinned", label, reference)] if context.closed else []
    if not _is_sha256(digest):
        return [PlanFinding("evidence_hash_malformed", label, str(digest))]
    if context.compare_digests and _sha256_file(root, reference) != digest:
        return [PlanFinding("evidence_hash_drift", label, reference)]
    return []


def _validate_evidence_item(item: object, *, label: str, context: EvidenceContextV1, root: ConfinedRootV1) -> list[PlanFinding]:
    shape = _shape(item, EVIDENCE_FIELDS, rule="evidence_field_set_not_closed", subject=label)
    if shape is not None or not isinstance(item, Mapping):
        return [shape] if shape is not None else []
    kind, reference, digest = item["kind"], item["reference"], item["sha256"]
    if not _in(EVIDENCE_KINDS)(kind) or not _is_nonempty_str(reference):
        return [PlanFinding("evidence_kind_or_reference_invalid", label, f"{_text(kind)}:{_text(reference)}")]
    if kind in FILE_EVIDENCE_KINDS:
        return _file_evidence_findings(item, label=label, context=context, root=root)
    findings = [PlanFinding("evidence_hash_not_applicable", label, str(kind))] if digest is not None else []
    if kind == "commit" and not _is_commit(reference):
        findings.append(PlanFinding("evidence_commit_malformed", label, str(reference)))
    elif kind == "commit" and _git(root, ["cat-file", "-e", f"{reference}^{{commit}}"])[0] != 0:
        findings.append(PlanFinding("evidence_commit_unknown", label, str(reference)))
    elif kind == "commit" and _git(
        root, ["merge-base", "--is-ancestor", str(reference), "HEAD"]
    )[0] != 0:
        findings.append(
            PlanFinding(
                "evidence_commit_outside_subject_lineage",
                label,
                str(reference),
            )
        )
    return findings


def _validate_mutation_killers(task_id: str, killers: Sequence[str], root: ConfinedRootV1) -> list[PlanFinding]:
    findings: list[PlanFinding] = []
    for killer in killers:
        match = MUTATION_KILLER_RE.fullmatch(killer)
        if match is None:
            findings.append(PlanFinding("mutation_killer_reference_malformed", task_id, killer))
            continue
        source = read_confined_file_v1(root, Path(match.group(1)), max_bytes=MAX_HASHED_FILE_BYTES).data
        if source is None or f"def {match.group(2)}(".encode("utf-8") not in source:
            findings.append(PlanFinding("mutation_killer_missing", task_id, killer))
    return findings


def _text(value: object) -> str:
    """Short deterministic rendering of any JSON value for a finding's evidence field."""

    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"))[:120]


def _vm_claim_findings(task: Mapping[str, Any]) -> list[PlanFinding]:
    task_id = str(task["task_id"])
    checks = (
        (bool(task["vm_gates"]), "vm_claim_without_gate", "claim names no VM gate"),
        (_is_nonempty_str(task["ripr_counterexample"]), "vm_claim_without_ripr_counterexample", "RIPR counterexample required"),
        (bool(task["mutation_killers"]), "vm_claim_without_mutation_killer", "mutation killer required"),
        (task["status"] in CLOSED_TASK_STATUSES, "vm_claim_on_open_task", str(task["status"])),
    )
    return [PlanFinding(rule, task_id, evidence) for satisfied, rule, evidence in checks if not satisfied]


def _validate_task_semantics(task: Mapping[str, Any], root: ConfinedRootV1, compare_digests: bool) -> list[PlanFinding]:
    task_id, status = str(task["task_id"]), str(task["status"])
    closed = status in CLOSED_TASK_STATUSES
    conditions = (
        (status == "DEFERRED_SEMANTIC_DECISION" and not task["semantic_decisions_avoided"], "deferred_task_without_policy", "name the unresolved policy"),
        (closed and not task["nonclaims"], "closed_task_without_nonclaims", "closed status requires nonclaims"),
        (closed and not task["evidence"], "closed_task_without_evidence", "closed status requires evidence"),
    )
    findings = [PlanFinding(rule, task_id, evidence) for violated, rule, evidence in conditions if violated]
    if task["claims_vm_improvement"]:
        findings.extend(_vm_claim_findings(task))
    findings.extend(_validate_mutation_killers(task_id, task["mutation_killers"], root))
    context = EvidenceContextV1(closed=closed, compare_digests=compare_digests)
    for index, item in enumerate(task["evidence"]):
        findings.extend(_validate_evidence_item(item, label=f"{task_id}.evidence[{index}]", context=context, root=root))
    return findings


def _validate_task(task: object, *, index: int, root: ConfinedRootV1, vocabulary: PlanVocabularyV1) -> list[PlanFinding]:
    label = f"tasks[{index}]"
    shape = _shape(task, TASK_FIELDS, rule="task_field_set_not_closed", subject=label)
    if shape is not None or not isinstance(task, Mapping):
        return [shape] if shape is not None else []
    task_id = task["task_id"]
    if not _matches(TASK_ID_RE)(task_id):
        return [PlanFinding("task_id_malformed", label, str(task_id))]
    checks: tuple[FieldCheck, ...] = (
        ("phase_id", lambda value: value in PHASE_IDS and str(task_id).startswith(f"{value}-"), "task_phase_mismatch"),
        ("title", _is_nonempty_str, "task_text_missing"),
        ("notes", _is_nonempty_str, "task_text_missing"),
        ("status", _in(TASK_STATUSES), "task_status_unknown"),
        ("depends_on", _is_unique_str_list, "task_dependencies_malformed"),
        ("vm_gates", _subset_of(VM_GATE_IDS), "task_vm_gate_unknown"),
        ("findings", _subset_of(vocabulary.finding_ids), "task_finding_unknown"),
        ("semantic_decisions_avoided", _subset_of(vocabulary.policy_ids), "task_policy_unknown"),
        ("nonclaims", _is_str_list, "task_nonclaims_malformed"),
        ("claims_vm_improvement", _is_bool, "task_claim_flag_malformed"),
        ("ripr_counterexample", lambda value: value is None or _is_nonempty_str(value), "ripr_counterexample_malformed"),
        ("evidence", lambda value: isinstance(value, list), "task_evidence_malformed"),
        ("mutation_killers", _is_str_list, "mutation_killers_malformed"),
    )
    findings = _check_fields(task, checks, str(task_id))
    compare_digests = str(task_id) not in vocabulary.repin_task_ids
    return findings if findings else _validate_task_semantics(task, root, compare_digests)


def _dependency_edge_findings(task_id: str, dep: str, status: object, by_id: Mapping[str, Mapping[str, Any]]) -> list[PlanFinding]:
    if dep == task_id:
        return [PlanFinding("task_depends_on_itself", task_id, dep)]
    if dep not in by_id:
        return [PlanFinding("task_dependency_unknown", task_id, dep)]
    findings: list[PlanFinding] = []
    if dep > task_id:
        findings.append(PlanFinding("task_dependency_not_ordered", task_id, f"{dep} must precede {task_id}"))
    allowed = {"DONE": frozenset({"DONE"}), "DONE_BOUNDED": CLOSED_TASK_STATUSES}.get(status) if isinstance(status, str) else None
    dep_status = by_id[dep].get("status")
    if allowed is not None and not _in(allowed)(dep_status):
        findings.append(PlanFinding("done_task_with_open_dependency", task_id, f"{dep}:{_text(dep_status)}"))
    return findings


def _known_dependencies(by_id: Mapping[str, Mapping[str, Any]], node: str) -> list[str]:
    deps = _as_str_list(by_id[node].get("depends_on"))
    return [dep for dep in deps if dep in by_id] if deps is not None else []


def _cycle_findings(by_id: Mapping[str, Mapping[str, Any]]) -> list[PlanFinding]:
    findings: list[PlanFinding] = []
    color: dict[str, int] = {}
    for start in sorted(by_id):
        if color.get(start, 0):
            continue
        color[start] = 1
        path = [start]
        stack = [iter(_known_dependencies(by_id, start))]
        while stack:
            child = next(stack[-1], None)
            if child is None:
                color[path.pop()] = 2
                stack.pop()
                continue
            state = color.get(child, 0)
            if state == 1:
                findings.append(PlanFinding("task_dependency_cycle", child, "->".join([*path, child])))
            elif state == 0:
                color[child] = 1
                path.append(child)
                stack.append(iter(_known_dependencies(by_id, child)))
    return findings


def _validate_dependencies(tasks: Sequence[Mapping[str, Any]]) -> list[PlanFinding]:
    ids = [str(task.get("task_id")) for task in tasks]
    findings = [PlanFinding("task_id_duplicate", task_id, "duplicate task id") for task_id in sorted({i for i in ids if ids.count(i) > 1})]
    if ids != sorted(ids):
        findings.append(PlanFinding("tasks_not_in_canonical_order", "tasks", "sort by task_id"))
    by_id = {str(task["task_id"]): task for task in tasks if isinstance(task.get("task_id"), str)}
    for task_id, task in by_id.items():
        for dep in _as_str_list(task.get("depends_on")) or []:
            findings.extend(_dependency_edge_findings(task_id, dep, task.get("status"), by_id))
    findings.extend(_cycle_findings(by_id))
    return findings


def _derived_gate_tasks(tasks: Sequence[Mapping[str, Any]]) -> dict[str, list[str]]:
    derived: dict[str, list[str]] = {gate: [] for gate in VM_GATE_IDS}
    for task in tasks:
        task_id = task.get("task_id")
        for gate in _as_str_list(task.get("vm_gates")) or []:
            if gate in derived and isinstance(task_id, str):
                derived[gate].append(task_id)
    return {gate: sorted(members) for gate, members in derived.items()}


def _validate_vm_gate_entry(entry: object, *, label: str, derived: Mapping[str, list[str]], status_by_task: Mapping[str, object]) -> list[PlanFinding]:
    shape = _shape(entry, VM_GATE_FIELDS, rule="vm_gate_field_set_not_closed", subject=label)
    if shape is not None or not isinstance(entry, Mapping):
        return [shape] if shape is not None else []
    gate_id = entry["gate_id"]
    if not isinstance(gate_id, str) or gate_id not in derived:
        return [PlanFinding("vm_gate_unknown", label, _text(gate_id))]
    expected_tasks = derived[gate_id]
    checks: tuple[FieldCheck, ...] = (
        ("status", _in(VM_GATE_STATUSES), "vm_gate_status_unknown"),
        ("decisive_remaining_condition", _is_nonempty_str, "vm_gate_condition_missing"),
        ("tasks", lambda value: value == expected_tasks, "vm_gate_task_map_drift"),
    )
    findings = _check_fields(entry, checks, gate_id)
    if not expected_tasks:
        findings.append(PlanFinding("vm_gate_without_task", gate_id, "every gate needs at least one task"))
    open_tasks = [task_id for task_id in expected_tasks if status_by_task.get(task_id) != "DONE"]
    if entry["status"] == "PASS" and (open_tasks or not expected_tasks):
        findings.append(PlanFinding("vm_gate_pass_with_open_tasks", gate_id, ",".join(open_tasks) or "no tasks"))
    return findings


def _validate_vm_gate_status(plan: Mapping[str, Any], tasks: Sequence[Mapping[str, Any]]) -> list[PlanFinding]:
    entries = plan["vm_gate_status"]
    if not isinstance(entries, list):
        return [PlanFinding("vm_gate_status_malformed", "vm_gate_status", "must be a list")]
    derived = _derived_gate_tasks(tasks)
    status_by_task = {str(task["task_id"]): task.get("status") for task in tasks if isinstance(task.get("task_id"), str)}
    findings: list[PlanFinding] = []
    for index, entry in enumerate(entries):
        findings.extend(_validate_vm_gate_entry(entry, label=f"vm_gate_status[{index}]", derived=derived, status_by_task=status_by_task))
    seen = [str(entry.get("gate_id")) for entry in entries if isinstance(entry, Mapping)]
    if tuple(seen) != VM_GATE_IDS:
        findings.append(PlanFinding("vm_gate_ids_not_canonical", "vm_gate_status", ",".join(seen)))
    return findings


def _validate_rows(rows: object, contract: RowContractV1) -> tuple[list[PlanFinding], list[Mapping[str, Any]]]:
    """Validate an identified row list; returns findings and the well-formed rows."""

    if not isinstance(rows, list) or not rows:
        return [PlanFinding(f"{contract.rule_prefix}_malformed", contract.subject, "must be a nonempty list")], []
    findings: list[PlanFinding] = []
    well_formed: list[Mapping[str, Any]] = []
    seen: set[str] = set()
    for index, row in enumerate(rows):
        label = f"{contract.subject}[{index}]"
        shape = _shape(row, contract.fields, rule=f"{contract.rule_prefix}_field_set_not_closed", subject=label)
        if shape is not None or not isinstance(row, Mapping):
            findings.extend([shape] if shape is not None else [])
            continue
        row_id = row[contract.id_field]
        if not _matches(contract.id_pattern)(row_id):
            findings.append(PlanFinding(f"{contract.rule_prefix}_id_malformed", label, str(row_id)))
            continue
        if row_id in seen:
            findings.append(PlanFinding(f"{contract.rule_prefix}_id_duplicate", str(row_id), "duplicate"))
        seen.add(str(row_id))
        findings.extend(_check_fields(row, contract.checks, str(row_id)))
        well_formed.append(row)
    return findings, well_formed


FINDING_ROWS: Final = RowContractV1(
    subject="finding_registry",
    fields=FINDING_FIELDS,
    id_field="finding_id",
    id_pattern=FINDING_ID_RE,
    checks=(
        ("severity", _in(FINDING_SEVERITIES), "finding_severity_unknown"),
        ("status", _in(FINDING_STATUSES), "finding_status_unknown"),
        ("title", _is_nonempty_str, "finding_text_missing"),
        ("source", _is_nonempty_str, "finding_text_missing"),
    ),
    rule_prefix="finding",
)
POLICY_ROWS: Final = RowContractV1(
    subject="unresolved_policies",
    fields=POLICY_FIELDS,
    id_field="policy_id",
    id_pattern=POLICY_ID_RE,
    checks=tuple((field, _is_nonempty_str, "policy_text_missing") for field in ("statement", "source", "implementation_rule")),
    rule_prefix="policy",
)
HEAVY_GATE_ROWS: Final = RowContractV1(
    subject="heavy_gates_requiring_runpod",
    fields=HEAVY_GATE_FIELDS,
    id_field="gate_id",
    id_pattern=HEAVY_GATE_ID_RE,
    checks=tuple((field, _is_nonempty_str, "heavy_gate_text_missing") for field in ("command", "reason", "workspace", "last_recorded_evidence")),
    rule_prefix="heavy_gate",
)


def _validate_finding_registry(plan: Mapping[str, Any], tasks: Sequence[Mapping[str, Any]]) -> list[PlanFinding]:
    findings, rows = _validate_rows(plan["finding_registry"], FINDING_ROWS)
    killed: set[str] = set()
    for task in tasks:
        refs = _as_str_list(task.get("findings"))
        if refs is not None and _in(CLOSED_TASK_STATUSES)(task.get("status")) and task.get("mutation_killers"):
            killed.update(refs)
    findings.extend(
        PlanFinding("finding_closed_without_killer", str(row["finding_id"]), "a closed task with a mutation killer must reference it")
        for row in rows
        if row["status"] == "CLOSED" and row["finding_id"] not in killed
    )
    return findings


def _registry_bindings(spec: LiveGateSpecV1) -> tuple[tuple[str, object], ...]:
    return (
        ("command", list(spec.argv)),
        ("checker_path", spec.checker_path),
        ("output_format", spec.output_format),
        ("observed_projection", list(spec.observed_projection)),
        ("timeout_seconds", spec.timeout_seconds),
    )


def _live_gate_binding_findings(gate: object, *, label: str) -> tuple[list[PlanFinding], LiveGateSpecV1 | None]:
    """Shape plus exact registry equality; no observation or hash checks."""

    shape = _shape(gate, LIVE_GATE_FIELDS, rule="live_gate_field_set_not_closed", subject=label)
    if shape is not None or not isinstance(gate, Mapping):
        return ([shape] if shape is not None else []), None
    gate_id = gate["gate_id"]
    spec = LIVE_GATE_REGISTRY.get(gate_id) if isinstance(gate_id, str) else None
    if spec is None:
        return [PlanFinding("live_gate_not_in_registry", label, str(gate_id))], None
    mismatches = [PlanFinding("live_gate_registry_mismatch", spec.gate_id, field) for field, expected in _registry_bindings(spec) if gate[field] != expected]
    return mismatches, (spec if not mismatches else None)


def _live_gate_record_findings(
    gate: Mapping[str, Any], spec: LiveGateSpecV1, root: ConfinedRootV1, profile: PlanValidationProfileV1
) -> list[PlanFinding]:
    checks: tuple[FieldCheck, ...] = (
        ("observed", lambda value: isinstance(value, Mapping), "live_gate_observed_malformed"),
        ("exit_code", _is_int, "live_gate_exit_code_malformed"),
        ("purpose", _is_nonempty_str, "live_gate_purpose_missing"),
        ("checker_sha256", _is_sha256, "live_gate_checker_hash_malformed"),
    )
    findings = _check_fields(gate, checks, spec.gate_id)
    if not _is_regular_file(root, spec.checker_path):
        findings.append(PlanFinding("live_gate_checker_missing", spec.gate_id, spec.checker_path))
    if not profile.compares_regenerable or findings:
        return findings
    if set(gate["observed"]) != set(spec.observed_projection):
        findings.append(PlanFinding("live_gate_observed_projection_mismatch", spec.gate_id, "observed keys must equal the projection"))
    if _sha256_file(root, spec.checker_path) != gate["checker_sha256"]:
        findings.append(PlanFinding("live_gate_checker_hash_drift", spec.gate_id, spec.checker_path))
    return findings


def _validate_live_gate(
    gate: object, *, label: str, root: ConfinedRootV1, profile: PlanValidationProfileV1 = ORDINARY_VALIDATION_PROFILE_V1
) -> list[PlanFinding]:
    findings, spec = _live_gate_binding_findings(gate, label=label)
    if spec is not None and isinstance(gate, Mapping):
        findings.extend(_live_gate_record_findings(gate, spec, root, profile))
    return findings


def _registry_set_findings(gates: Sequence[object]) -> list[PlanFinding]:
    ids = [_text(gate.get("gate_id")) for gate in gates if isinstance(gate, Mapping)]
    if ids == [_text(gate_id) for gate_id in sorted(LIVE_GATE_REGISTRY)]:
        return []
    return [PlanFinding("live_gate_registry_set_mismatch", "live_gates", f"declared={ids} registry={sorted(LIVE_GATE_REGISTRY)}")]


def _validate_live_gates(plan: Mapping[str, Any], root: ConfinedRootV1, profile: PlanValidationProfileV1) -> list[PlanFinding]:
    gates = plan["live_gates"]
    if not isinstance(gates, list):
        return [PlanFinding("live_gates_malformed", "live_gates", "must be a list")]
    findings: list[PlanFinding] = []
    for index, gate in enumerate(gates):
        findings.extend(_validate_live_gate(gate, label=f"live_gates[{index}]", root=root, profile=profile))
    return findings + _registry_set_findings(gates)


def _validate_external_gates(plan: Mapping[str, Any]) -> list[PlanFinding]:
    external = plan["external_gates"]
    if not isinstance(external, list) or not external:
        return [PlanFinding("external_gates_malformed", "external_gates", "must be a nonempty list")]
    checks: tuple[FieldCheck, ...] = (
        ("gate_id", _is_nonempty_str, "external_gate_text_missing"),
        ("location", _is_nonempty_str, "external_gate_text_missing"),
        ("location", _is_location_without_absolute_path, "external_gate_location_absolute"),
        ("purpose", _is_nonempty_str, "external_gate_text_missing"),
        ("executed_by_checker", lambda value: value is False, "external_gate_claims_execution"),
    )
    findings: list[PlanFinding] = []
    for index, entry in enumerate(external):
        label = f"external_gates[{index}]"
        shape = _shape(entry, EXTERNAL_GATE_FIELDS, rule="external_gate_field_set_not_closed", subject=label)
        findings.extend([shape] if shape is not None else _check_fields(entry, checks, label))
    return findings


def _validate_receipt(plan: Mapping[str, Any]) -> list[PlanFinding]:
    receipt = plan["test_execution_receipt"]
    shape = _shape(receipt, RECEIPT_FIELDS, rule="test_receipt_field_set_not_closed", subject="test_execution_receipt")
    if shape is not None:
        return [shape]
    checks: tuple[FieldCheck, ...] = (
        ("command", lambda value: _is_str_list(value) and bool(value), "test_receipt_command_malformed"),
        ("passed", _is_nonneg_int, "test_receipt_count_malformed"),
        ("failed", _is_nonneg_int, "test_receipt_count_malformed"),
        ("duration_seconds", _is_nonneg_int, "test_receipt_count_malformed"),
        ("failed_tests", _is_sorted_str_list, "test_receipt_failures_malformed"),
        ("evidence_authority", lambda value: value == "LOCAL_EXECUTION_RECORD_UNATTESTED", "test_receipt_authority_overclaimed"),
        ("interpreter", _is_nonempty_str, "test_receipt_interpreter_missing"),
        ("subject_commit", _is_commit, "test_receipt_subject_malformed"),
    )
    findings = _check_fields(receipt, checks, "test_execution_receipt")
    failed_tests = _as_str_list(receipt["failed_tests"])
    if failed_tests is not None and _is_nonneg_int(receipt["failed"]) and len(failed_tests) != receipt["failed"]:
        findings.append(PlanFinding("test_receipt_failure_count_mismatch", "test_execution_receipt", f"{len(failed_tests)}!={receipt['failed']}"))
    return findings


def _markdown_table(header: Sequence[str], rows: Iterable[Sequence[str]]) -> list[str]:
    lines = ["| " + " | ".join(header) + " |", "| " + " | ".join("---" for _ in header) + " |"]
    lines.extend("| " + " | ".join(cell.replace("|", "\\|") for cell in row) + " |" for row in rows)
    return lines


def _render_header(plan: Mapping[str, Any]) -> list[str]:
    subject = plan["subject"]
    authority = ", ".join(f"`{key}={json.dumps(value)}`" for key, value in sorted(plan["authority"].items()))
    return [
        f"Subject: base `{subject['base_commit']}` on `{subject['branch']}`, source snapshot "
        f"`{subject['source_snapshot_sha256']}` ({subject['source_snapshot_file_count']} files, plan artifacts excluded), "
        f"observed {subject['observed_at']}.",
        "",
        f"Authority ceiling: {authority}.",
    ]


def _render_tasks(plan: Mapping[str, Any]) -> list[str]:
    header = ("Task", "Status", "Title", "Depends on", "VM gates", "Findings", "Claims VM improvement")
    rows = (
        (
            task["task_id"], task["status"], task["title"], ", ".join(task["depends_on"]) or "-",
            ", ".join(task["vm_gates"]) or "-", ", ".join(task["findings"]) or "-",
            "yes" if task["claims_vm_improvement"] else "no",
        )
        for task in plan["tasks"]
    )
    return _markdown_table(header, rows)


def _render_live_gates(plan: Mapping[str, Any]) -> list[str]:
    rows = (
        (
            gate["gate_id"], "`" + " ".join(gate["command"]) + "`", str(gate["exit_code"]),
            "`" + json.dumps(gate["observed"], sort_keys=True, separators=(",", ":")) + "`",
        )
        for gate in plan["live_gates"]
    )
    return _markdown_table(("Gate", "Command", "Exit", "Observed"), rows)


def _render_receipt(plan: Mapping[str, Any]) -> list[str]:
    receipt = plan["test_execution_receipt"]
    lines = [
        f"`{' '.join(receipt['command'])}` at `{receipt['subject_commit']}`: "
        f"{receipt['passed']} passed, {receipt['failed']} failed in {receipt['duration_seconds']} s "
        f"({receipt['interpreter']}; {receipt['evidence_authority']})."
    ]
    lines.extend(f"- FAILED `{failed}`" for failed in receipt["failed_tests"])
    return lines


def _render_sections(plan: Mapping[str, Any]) -> list[tuple[str, list[str]]]:
    return [
        ("Phases", _markdown_table(("Phase", "Original plan section", "Title"), ((p["phase_id"], str(p["original_plan_section"]), p["title"]) for p in plan["phases"]))),
        ("Tasks", _render_tasks(plan)),
        ("VM gate status", _markdown_table(("Gate", "Status", "Decisive remaining condition", "Tasks"), ((g["gate_id"], g["status"], g["decisive_remaining_condition"], ", ".join(g["tasks"]) or "-") for g in plan["vm_gate_status"]))),
        ("Live gates", _render_live_gates(plan)),
        ("Heavy gates requiring RunPod or external capacity", _markdown_table(("Gate", "Workspace", "Command", "Reason", "Last recorded evidence"), ((h["gate_id"], h["workspace"], "`" + h["command"] + "`", h["reason"], h["last_recorded_evidence"]) for h in plan["heavy_gates_requiring_runpod"]))),
        ("Unresolved policy inputs", _markdown_table(("Policy", "Statement", "Source", "Implementation rule"), ((p["policy_id"], p["statement"], p["source"], p["implementation_rule"]) for p in plan["unresolved_policies"]))),
        ("Finding registry", _markdown_table(("Finding", "Severity", "Status", "Title", "Source"), ((f["finding_id"], f["severity"], f["status"], f["title"], f["source"]) for f in plan["finding_registry"]))),
        ("Test execution receipt", _render_receipt(plan)),
    ]


def render_generated_markdown_v1(plan: Mapping[str, Any]) -> str:
    """Render the deterministic generated block for the markdown companion."""

    lines: list[str] = [GENERATED_BEGIN, "", *_render_header(plan), ""]
    for title, body in _render_sections(plan):
        lines.extend([f"### {title}", "", *body, ""])
    lines.append(GENERATED_END)
    return "\n".join(lines) + "\n"


def _split_markdown(markdown: str) -> tuple[str, str, str] | None:
    begin = markdown.find(GENERATED_BEGIN)
    end = markdown.find(GENERATED_END)
    if begin < 0 or end < begin:
        return None
    end_stop = end + len(GENERATED_END) + 1
    return markdown[:begin], markdown[begin:end_stop], markdown[end_stop:]


def _narrative_range_findings(plan: Mapping[str, Any], narrative: str) -> list[PlanFinding]:
    """A narrative range such as ``B-01 through B-04`` must end at the highest registered B finding."""

    registered = sorted(
        str(row["finding_id"]) for row in _rows_of(plan["finding_registry"]) if str(row.get("finding_id", "")).startswith("B-")
    )
    if not registered:
        return []
    return [
        PlanFinding("plan_markdown_narrative_stale_finding_range", PLAN_MARKDOWN_PATH.as_posix(), f"narrative ends at B-{match.group(1)} while {registered[-1]} is registered")
        for match in NARRATIVE_BASE_DEFECT_RANGE_RE.finditer(narrative)
        if f"B-{match.group(1)}" != registered[-1]
    ]


def _rows_of(value: object) -> list[Mapping[str, Any]]:
    return [row for row in value if isinstance(row, Mapping)] if isinstance(value, list) else []


def _validate_markdown(plan: Mapping[str, Any], markdown: str | None, profile: PlanValidationProfileV1) -> list[PlanFinding]:
    if markdown is None:
        return [PlanFinding("plan_markdown_missing", PLAN_MARKDOWN_PATH.as_posix(), "companion markdown is required")]
    parts = _split_markdown(markdown)
    if parts is None:
        return [PlanFinding("plan_markdown_generated_block_missing", PLAN_MARKDOWN_PATH.as_posix(), "generated markers absent")]
    try:
        expected = render_generated_markdown_v1(plan)
    except (KeyError, TypeError, AttributeError, ValueError, IndexError) as exc:
        return [PlanFinding("plan_markdown_unrenderable", PLAN_MARKDOWN_PATH.as_posix(), f"{type(exc).__name__}: {exc}")]
    findings = _narrative_range_findings(plan, parts[0] + parts[2])
    if not profile.compares_regenerable:
        return findings
    if parts[1] != expected:
        findings.append(PlanFinding("plan_markdown_generated_block_drift", PLAN_MARKDOWN_PATH.as_posix(), "regenerate with --render"))
    findings.extend(
        PlanFinding("plan_markdown_task_missing", str(task["task_id"]), "task id absent from markdown")
        for task in plan["tasks"]
        if isinstance(task, Mapping) and isinstance(task.get("task_id"), str) and task["task_id"] not in markdown
    )
    return findings


def _row_ids(rows: object, field: str) -> frozenset[str]:
    if not isinstance(rows, list):
        return frozenset()
    return frozenset(str(row[field]) for row in rows if isinstance(row, Mapping) and field in row)


def validate_plan_v1(
    plan: Mapping[str, Any],
    *,
    root: RootLike,
    markdown: str | None,
    profile: PlanValidationProfileV1 = ORDINARY_VALIDATION_PROFILE_V1,
) -> list[PlanFinding]:
    """Return every structural, lineage, evidence, artifact, and drift finding.

    ``profile`` is one of the three closed profiles (``ORDINARY`` by default;
    ``PlanValidationProfileV1.pre_regeneration`` before regeneration;
    ``POST_REGENERATION_PROFILE_V1`` right after it). ``root`` is bound to its
    directory identity for every confined read. Never raises on a malformed
    plan: every defect, including a hostile JSON type in any field, is a
    typed finding.
    """

    checked_profile, profile_findings = _profile_or_findings_v1(profile)
    if checked_profile is None:
        return profile_findings
    owned_plan, ownership_findings = _owned_plan_v1(plan)
    if owned_plan is None:
        return ownership_findings
    if markdown is not None and type(markdown) is not str:
        return [
            PlanFinding(
                "plan_markdown_type_invalid",
                PLAN_MARKDOWN_PATH.as_posix(),
                f"expected an exact string or None, received {type(markdown).__name__}",
            )
        ]
    try:
        with _UseRoot(root) as bound:
            return _validate_with_root(owned_plan, bound, markdown, checked_profile)
    except RootUnavailable as exc:
        return _root_unavailable(exc)


def _validate_with_root(
    plan: Mapping[str, Any], bound: ConfinedRootV1, markdown: str | None, profile: PlanValidationProfileV1
) -> list[PlanFinding]:
    findings = _validate_top_level(plan)
    if findings:
        return findings
    tasks = plan["tasks"]
    if not isinstance(tasks, list) or not tasks:
        return [PlanFinding("tasks_malformed", "tasks", "must be a nonempty list")]
    well_formed = [task for task in tasks if isinstance(task, Mapping)]
    vocabulary = PlanVocabularyV1(
        _row_ids(plan["finding_registry"], "finding_id"), _row_ids(plan["unresolved_policies"], "policy_id"), profile.repin_tasks
    )
    for index, task in enumerate(tasks):
        findings.extend(_validate_task(task, index=index, root=bound, vocabulary=vocabulary))
    validators: tuple[Callable[[], list[PlanFinding]], ...] = (
        lambda: plan_artifact_findings_v1(bound),
        lambda: _validate_subject(plan, bound, profile),
        lambda: _validate_semantic_anchors(plan, bound),
        lambda: _validate_phases(plan),
        lambda: _validate_finding_registry(plan, well_formed),
        lambda: _validate_rows(plan["unresolved_policies"], POLICY_ROWS)[0],
        lambda: _validate_dependencies(well_formed),
        lambda: _validate_vm_gate_status(plan, well_formed),
        lambda: _validate_live_gates(plan, bound, profile),
        lambda: _validate_external_gates(plan),
        lambda: _validate_rows(plan["heavy_gates_requiring_runpod"], HEAVY_GATE_ROWS)[0],
        lambda: _validate_receipt(plan),
        lambda: _validate_markdown(plan, markdown, profile),
    )
    for validator in validators:
        findings.extend(validator())
    return sorted(findings, key=lambda item: (item.rule_id, item.subject, item.evidence))


@dataclass(frozen=True, slots=True)
class ExecutionContextV1:
    """Trusted-process record of one exact-HEAD, clean, sealed-artifact plan.

    This public same-process value is a convention, not an unforgeable
    capability. Every consumer rechecks its complete binding before effects.
    """

    _owner: ConfinedRootV1
    _head: str
    _artifacts: BoundPlanArtifactsV1

    @property
    def artifact_digests(self) -> tuple[tuple[str, str], ...]:
        return self._artifacts.digests

    def close(self) -> None:
        self._artifacts.close()


@dataclass(frozen=True, slots=True)
class LiveGateEffectV1:
    """One fully validated gate row frozen into a trusted-process effect.

    Beyond the registry spec and the expected result, an effect is inseparable
    from the planning root capability (``_owner``, compared by object
    identity), the exact source snapshot digest observed at planning
    (``_snapshot``), and sealed checker/supervisor snapshots captured while
    their source descriptors matched their hashes. It executes only through
    that same root record while the invocation context still has the exact
    pre-read HEAD, artifact digests, and a fully clean worktree. The dataclass
    is caller-constructible and carries no authority outside this trusted
    process. ``expected_observed`` holds
    ``(key, canonical JSON)`` pairs so the comparison is value-exact for every
    JSON type. Construct effects only through
    ``plan_live_gate_effects_v1`` in ordinary use.
    """

    spec: LiveGateSpecV1
    expected_exit_code: int
    expected_observed: tuple[tuple[str, str], ...]
    checker_sha256: str
    _owner: ConfinedRootV1
    _snapshot: str
    _artifact_digests: tuple[tuple[str, str], ...]
    _context: ExecutionContextV1
    _checker: AnchoredFileV1
    _supervisor: SupervisorCodeV1

    @property
    def _head(self) -> str:
        """Compatibility view of the exact invocation HEAD."""

        return self._context._head

    def close(self) -> None:
        try:
            self._checker.close()
        finally:
            self._supervisor.close()


def close_live_gate_effects_v1(effects: Iterable[LiveGateEffectV1]) -> None:
    """Close every executable snapshot and each shared invocation context."""

    materialized = tuple(effects)
    pending: BaseException | None = None
    for effect in materialized:
        try:
            effect.close()
        except BaseException as exc:
            if pending is None:
                pending = exc
    contexts: list[ExecutionContextV1] = []
    for effect in materialized:
        if not any(effect._context is context for context in contexts):
            contexts.append(effect._context)
    for context in contexts:
        try:
            context.close()
        except BaseException as exc:
            if pending is None:
                pending = exc
    if pending is not None:
        raise pending


def _close_effect_sources_v1(effects: Iterable[LiveGateEffectV1]) -> None:
    """Close checker/supervisor snapshots while leaving a caller-owned context open."""

    pending: BaseException | None = None
    for effect in effects:
        try:
            effect.close()
        except BaseException as exc:
            if pending is None:
                pending = exc
    if pending is not None:
        raise pending


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"))


def _gate_effect(
    gate: object,
    *,
    label: str,
    root: ConfinedRootV1,
    snapshot: str,
    context: ExecutionContextV1,
) -> tuple[LiveGateEffectV1 | None, list[PlanFinding]]:
    """Validate one complete gate row (binding, record, checker digest) into an effect that holds its checker open."""

    findings = _validate_live_gate(gate, label=label, root=root)
    if findings or not isinstance(gate, Mapping):
        return None, findings
    spec = LIVE_GATE_REGISTRY[str(gate["gate_id"])]
    try:
        checker = root.anchored.open_file(spec.checker_path)
    except OSError as exc:
        return None, [PlanFinding("live_gate_checker_missing", spec.gate_id, f"{spec.checker_path}: {exc}")]
    if checker.sha256 != gate["checker_sha256"]:
        checker.close()
        return None, [PlanFinding("live_gate_checker_hash_drift", spec.gate_id, spec.checker_path)]
    try:
        supervisor = bind_supervisor_code_v1(root.anchored)
    except OSError as exc:
        checker.close()
        return None, [
            PlanFinding(
                "live_gate_supervisor_binding_refused",
                spec.gate_id,
                f"{type(exc).__name__}: {exc}",
            )
        ]
    observed = tuple(sorted((str(key), _canonical_json(value)) for key, value in gate["observed"].items()))
    return LiveGateEffectV1(
        spec,
        int(gate["exit_code"]),
        observed,
        checker.sha256,
        root,
        snapshot,
        context.artifact_digests,
        context,
        checker,
        supervisor,
    ), []


def _execution_context_findings(
    root: ConfinedRootV1, *, subject: str, expected_head: str | None
) -> tuple[str | None, list[PlanFinding]]:
    """Bind or recheck the exact HEAD and clean worktree used by an effect."""

    code, head = _git(root, ["rev-parse", "HEAD"])
    if code != 0 or not _is_commit(head):
        return None, [
            PlanFinding(
                "live_gate_effect_head_unavailable",
                subject,
                "git rev-parse HEAD failed",
            )
        ]
    if expected_head is not None and head != expected_head:
        return head, [
            PlanFinding(
                "live_gate_effect_head_drift",
                subject,
                f"planned={expected_head} observed={head}",
            )
        ]
    dirty = scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.FULL)
    if dirty is None:
        return head, [
            PlanFinding(
                "live_gate_effect_worktree_unavailable",
                subject,
                "git status failed or returned a malformed record",
            )
        ]
    if dirty:
        return head, [
            PlanFinding(
                "live_gate_effect_worktree_drift",
                subject,
                ",".join(dirty[:8]),
            )
        ]
    return head, []


def _bind_execution_context_v1(
    root: ConfinedRootV1, *, subject: str
) -> tuple[ExecutionContextV1 | None, list[PlanFinding]]:
    """Record exact HEAD, FULL cleanliness, and sealed HEAD-bound artifacts."""

    head, findings = _execution_context_findings(
        root, subject=subject, expected_head=None
    )
    findings = [
        PlanFinding(
            "scoped_worktree_dirty",
            "subject.scoped_worktree_clean",
            finding.evidence,
        )
        if finding.rule_id == "live_gate_effect_worktree_drift"
        else PlanFinding(
            "scoped_worktree_status_unavailable",
            "subject",
            finding.evidence,
        )
        if finding.rule_id == "live_gate_effect_worktree_unavailable"
        else finding
        for finding in findings
    ]
    if head is None or findings:
        return None, findings
    artifacts, binding_findings = bind_plan_artifacts_v1(
        root.anchored, head
    )
    if artifacts is None:
        return None, _artifact_binding_plan_findings_v1(binding_findings)
    try:
        context = ExecutionContextV1(root, head, artifacts)
    except BaseException:
        try:
            artifacts.close()
        except BaseException:
            pass
        raise
    try:
        findings = _bound_execution_context_findings(
            context, root, subject=subject
        )
    except BaseException:
        try:
            context.close()
        except BaseException:
            pass
        raise
    if findings:
        try:
            context.close()
        except BaseException as exc:
            findings.append(
                PlanFinding(
                    "plan_artifact_cleanup_refused",
                    "plan_artifacts",
                    f"{type(exc).__name__}: {exc}",
                )
            )
        return None, findings
    return context, []


def _artifact_binding_plan_findings_v1(
    findings: Iterable[PlanArtifactBindingFindingV1],
) -> list[PlanFinding]:
    return [
        PlanFinding(finding.rule_id, finding.subject, finding.evidence)
        for finding in findings
    ]


def _bound_execution_context_findings(
    context: object, root: ConfinedRootV1, *, subject: str
) -> list[PlanFinding]:
    """Recheck a trusted-process context's root, HEAD, cleanliness, and artifacts."""

    if not isinstance(context, ExecutionContextV1) or context._owner is not root:
        return [
            PlanFinding(
                "live_gate_execution_context_not_owned",
                subject,
                "execution context is not the trusted-process record for this root",
            )
        ]
    _head, findings = _execution_context_findings(
        root, subject=subject, expected_head=context._head
    )
    if findings:
        return findings
    findings.extend(
        _artifact_binding_plan_findings_v1(
            context._artifacts.integrity_findings(
                root.anchored, expected_head=context._head
            )
        )
    )
    return findings


def _observe_anchored(
    spec: LiveGateSpecV1,
    root: ConfinedRootV1,
    checker: AnchoredFileV1,
    supervisor: SupervisorCodeV1,
) -> tuple[LiveGateObservationV1 | None, str]:
    """Observe one registry gate with preflight, search path, cwd, and the executed bytes all bound to the capability."""

    try:
        return observe_live_gate_v1(
            spec,
            root.anchored,
            checker=checker,
            supervisor=supervisor,
        ), ""
    except OSError as exc:
        return None, _refusal(Path(spec.checker_path), exc)


def _close_owned_context_v1(
    context: ExecutionContextV1, owns_context: bool
) -> None:
    if owns_context:
        context.close()


def _plan_effects(
    gates: object,
    root: ConfinedRootV1,
    *,
    require_registry_set: bool,
    context: ExecutionContextV1 | None = None,
) -> tuple[tuple[LiveGateEffectV1, ...], list[PlanFinding]]:
    if not isinstance(root, ConfinedRootV1) or not root.is_open:
        return (), [PlanFinding("root_unavailable", "root", "effects require an open persistent root capability")]
    owns_context = context is None
    if context is None:
        context, findings = _bind_execution_context_v1(
            root, subject="live_gates"
        )
    else:
        findings = _bound_execution_context_findings(
            context, root, subject="live_gates"
        )
    if context is None or findings:
        return (), findings
    snapshot, findings = source_snapshot_v1(root)
    if snapshot is None:
        _close_owned_context_v1(context, owns_context)
        return (), findings
    findings.extend(
        _bound_execution_context_findings(
            context, root, subject="live_gates"
        )
    )
    if findings:
        _close_owned_context_v1(context, owns_context)
        return (), findings
    if not isinstance(gates, list):
        _close_owned_context_v1(context, owns_context)
        return (), [PlanFinding("live_gates_malformed", "live_gates", "must be a list")]
    effects: list[LiveGateEffectV1] = []
    for index, gate in enumerate(gates):
        effect, row_findings = _gate_effect(
            gate,
            label=f"live_gates[{index}]",
            root=root,
            snapshot=snapshot.sha256,
            context=context,
        )
        findings.extend(row_findings)
        if effect is not None:
            effects.append(effect)
    if require_registry_set:
        findings.extend(_registry_set_findings(gates))
    findings.extend(
        _bound_execution_context_findings(
            context, root, subject="live_gates"
        )
    )
    if findings:
        _close_effect_sources_v1(effects)
        _close_owned_context_v1(context, owns_context)
        return (), findings
    return tuple(effects), []


def plan_live_gate_effects_v1(gates: object, root: ConfinedRootV1) -> tuple[tuple[LiveGateEffectV1, ...], list[PlanFinding]]:
    """Validate every full gate row plus the exact registry set and order into an immutable, owned effect plan.

    Any finding in any row, or any subset, duplicate, extra, or reordered row,
    yields an empty effect plan; nothing executes from a partially valid list.
    The effects belong to ``root`` (a persistent capability) and to the source
    snapshot observed now; close them with ``close_live_gate_effects_v1``.
    """

    return _plan_effects(gates, root, require_registry_set=True)


def _effect_binding_findings(effect: LiveGateEffectV1, root: object) -> list[PlanFinding]:
    """Refuse an effect unless it is executed through its own open capability at its planning snapshot."""

    gate_id = effect.spec.gate_id
    if not isinstance(root, ConfinedRootV1) or root is not effect._owner:
        return [PlanFinding("live_gate_effect_not_owned", gate_id, "effects execute only through the capability that planned them")]
    if not root.is_open or not effect._checker.is_open or not effect._supervisor.is_open:
        return [PlanFinding("live_gate_effect_closed", gate_id, "the planning capability or held executable source is closed")]
    if effect._supervisor.root is not root.anchored:
        return [PlanFinding("live_gate_supervisor_not_owned", gate_id, "supervisor source is not owned by the planning root")]
    if effect._artifact_digests != effect._context.artifact_digests:
        return [
            PlanFinding(
                "live_gate_effect_artifact_binding_drift",
                gate_id,
                "effect artifact digests differ from its invocation context",
            )
        ]
    context_findings = _bound_execution_context_findings(
        effect._context, root, subject=gate_id
    )
    if context_findings:
        return context_findings
    snapshot, findings = source_snapshot_v1(root)
    if snapshot is None:
        return findings
    if snapshot.sha256 != effect._snapshot:
        return [PlanFinding("live_gate_effect_snapshot_drift", gate_id, f"planned={effect._snapshot} observed={snapshot.sha256}")]
    if effect._checker.rehash() != effect.checker_sha256:
        return [PlanFinding("live_gate_checker_hash_drift", gate_id, "held checker inode changed since planning")]
    if effect._supervisor.source.rehash() != effect._supervisor.sha256:
        return [PlanFinding("live_gate_supervisor_hash_drift", gate_id, "held supervisor inode changed since planning")]
    return []


def _post_observation_snapshot_findings(effect: LiveGateEffectV1, root: ConfinedRootV1) -> list[PlanFinding]:
    """After the observer ran, require the same committed tree and clean worktree."""

    snapshot, findings = source_snapshot_v1(root)
    if snapshot is None:
        return findings
    if snapshot.sha256 != effect._snapshot:
        return [
            PlanFinding(
                "live_gate_effect_snapshot_drift",
                effect.spec.gate_id,
                f"source snapshot changed during observation: planned={effect._snapshot} observed={snapshot.sha256}; observation refused",
            )
        ]
    context_findings = _bound_execution_context_findings(
        effect._context, root, subject=effect.spec.gate_id
    )
    return context_findings


def _execute_live_gate_effect_with_count_v1(
    effect: LiveGateEffectV1, root: ConfinedRootV1
) -> tuple[list[PlanFinding], int]:
    """Run one owned effect and return findings plus exact observer-call count.

    Any binding failure means no observer call; the committed source snapshot
    is compared before and again after the observer ran, and an observation
    made across a snapshot change is refused, never accepted.
    """

    findings = _effect_binding_findings(effect, root)
    if findings:
        return findings, 0
    observation, refusal = _observe_anchored(
        effect.spec, root, effect._checker, effect._supervisor
    )
    findings = _post_observation_snapshot_findings(effect, root)
    if findings:
        return findings, 1
    if observation is None:
        return [PlanFinding("live_gate_execution_failed", effect.spec.gate_id, refusal)], 1
    if observation.error:
        return [PlanFinding("live_gate_execution_failed", effect.spec.gate_id, observation.error)], 1
    if observation.exit_code != effect.expected_exit_code:
        findings.append(PlanFinding("live_gate_exit_code_drift", effect.spec.gate_id, f"recorded={effect.expected_exit_code} observed={observation.exit_code}"))
    findings.extend(
        PlanFinding("live_gate_observation_drift", effect.spec.gate_id, key)
        for key, recorded in effect.expected_observed
        if key not in observation.observed or _canonical_json(observation.observed[key]) != recorded
    )
    return findings, 1


def execute_live_gate_effect_v1(
    effect: LiveGateEffectV1, root: ConfinedRootV1
) -> list[PlanFinding]:
    """Run one owned effect through the registry and report drift."""

    return _execute_live_gate_effect_with_count_v1(effect, root)[0]


def compare_live_gate_execution_v1(gate: object, root: RootLike) -> list[PlanFinding]:
    """Plan and execute one gate row within one capability; refuse any row that does not fully validate."""

    try:
        with _UseRoot(root) as bound:
            effects, findings = _plan_effects([gate], bound, require_registry_set=False)
            if findings or not effects:
                return findings
            try:
                return execute_live_gate_effect_v1(effects[0], bound)
            finally:
                close_live_gate_effects_v1(effects)
    except RootUnavailable as exc:
        return _root_unavailable(exc)


def _validated_committed_execution_plan_v1(
    caller_plan: Mapping[str, Any],
    root: ConfinedRootV1,
    context: ExecutionContextV1,
) -> tuple[Mapping[str, Any] | None, list[PlanFinding]]:
    """Validate committed semantics, caller compatibility, and exact equality."""

    try:
        committed_plan, markdown = _decode_bound_plan_artifacts_v1(
            context._artifacts
        )
    except PlanUnreadable as exc:
        return None, [
            PlanFinding("plan_artifact_unreadable", "plan_artifacts", str(exc))
        ]
    findings = validate_plan_v1(
        committed_plan,
        root=root,
        markdown=markdown,
        profile=ORDINARY_VALIDATION_PROFILE_V1,
    )
    if findings:
        return None, findings
    findings = validate_plan_v1(
        caller_plan,
        root=root,
        markdown=markdown,
        profile=ORDINARY_VALIDATION_PROFILE_V1,
    )
    if findings:
        return None, findings
    try:
        caller_bytes = canonical_plan_json_v1(caller_plan).encode("utf-8")
    except (TypeError, ValueError, RecursionError) as exc:
        return None, [
            PlanFinding(
                "caller_plan_unserializable",
                "plan",
                f"{type(exc).__name__}: {exc}",
            )
        ]
    committed_plan_bytes = context._artifacts.bytes_for(PLAN_JSON_PATH.as_posix())
    if committed_plan_bytes is None:
        return None, [
            PlanFinding(
                "plan_artifact_binding_shape_invalid",
                "plan_artifacts",
                "sealed JSON artifact is absent from the exact ordered pair",
            )
        ]
    if caller_bytes != committed_plan_bytes:
        return None, [
            PlanFinding(
                "caller_plan_artifact_mismatch",
                PLAN_JSON_PATH.as_posix(),
                "caller mapping differs from the sealed committed plan",
            )
        ]
    return committed_plan, _bound_execution_context_findings(
        context, root, subject="live_gates"
    )


def _run_live_gate_effects_v1(
    effects: tuple[LiveGateEffectV1, ...],
    root: ConfinedRootV1,
    context: ExecutionContextV1,
) -> tuple[list[PlanFinding], int]:
    """Run until first refusal and preserve exact observer-call accounting."""

    findings: list[PlanFinding] = []
    executed = 0
    try:
        for effect in effects:
            effect_findings, effect_executed = (
                _execute_live_gate_effect_with_count_v1(effect, root)
            )
            executed += effect_executed
            findings.extend(effect_findings)
            if effect_findings:
                break
        if not findings:
            findings.extend(
                _bound_execution_context_findings(
                    context, root, subject="live_gates"
                )
            )
        return findings, executed
    finally:
        _close_effect_sources_v1(effects)


def _execute_live_gates_with_count_v1(
    plan: Mapping[str, Any],
    root: RootLike,
    *,
    context: ExecutionContextV1 | None = None,
) -> tuple[list[PlanFinding], int]:
    """Re-run gates and return findings plus the exact observer-call count.

    The sealed current JSON/Markdown pair owns semantics. It is decoded and
    validated first. The caller mapping is independently validated for stable
    mutation findings, then its canonical bytes must equal the held committed
    JSON exactly. Every effect carries both artifact digests. Any pre-execution
    finding means zero observer calls.
    """

    try:
        with _UseRoot(root) as bound:
            owns_context = context is None
            if context is None:
                context, findings = _bind_execution_context_v1(
                    bound, subject="live_gates"
                )
            else:
                findings = _bound_execution_context_findings(
                    context, bound, subject="live_gates"
                )
            if context is None or findings:
                return findings, 0
            try:
                committed_plan, findings = _validated_committed_execution_plan_v1(
                    plan, bound, context
                )
                if committed_plan is None or findings:
                    return findings, 0
                effects, effect_findings = _plan_effects(
                    committed_plan["live_gates"],
                    bound,
                    require_registry_set=True,
                    context=context,
                )
                if effect_findings:
                    return effect_findings, 0
                return _run_live_gate_effects_v1(effects, bound, context)
            finally:
                if owns_context:
                    context.close()
    except RootUnavailable as exc:
        return _root_unavailable(exc), 0


def execute_live_gates_v1(
    plan: Mapping[str, Any], root: RootLike
) -> list[PlanFinding]:
    """Re-run gates from the sealed committed plan after validating an equal caller mapping."""

    return _execute_live_gates_with_count_v1(plan, root)[0]


def _repin_evidence(refreshed: dict[str, Any], root: ConfinedRootV1, repin_tasks: frozenset[str]) -> list[PlanFinding]:
    """Recompute file-evidence digests of the (already validated) re-pin tasks."""

    findings: list[PlanFinding] = []
    for task in refreshed["tasks"]:
        if task["task_id"] not in repin_tasks:
            continue
        for item in task["evidence"]:
            reference = str(item["reference"])
            digest = _sha256_file(root, reference) if item["kind"] in FILE_EVIDENCE_KINDS and _is_regular_file(root, reference) else None
            if item["kind"] in FILE_EVIDENCE_KINDS and digest is None:
                findings.append(PlanFinding("evidence_missing", task["task_id"], reference))
            elif digest is not None:
                item["sha256"] = digest
    return findings


def _refresh_invocation_findings(plan: Mapping[str, Any], observed_at: object, repin_tasks: frozenset[str]) -> list[PlanFinding]:
    """Refuse a refresh whose date or re-pin ids are invalid before any validation or observer call."""

    findings: list[PlanFinding] = []
    if not _is_date(observed_at):
        findings.append(PlanFinding("refresh_observed_at_malformed", "subject.observed_at", _text(observed_at)))
    raw_tasks = plan.get("tasks") if isinstance(plan, Mapping) else None
    rows = raw_tasks if isinstance(raw_tasks, list) else []
    known = {task["task_id"] for task in rows if isinstance(task, Mapping) and isinstance(task.get("task_id"), str)}
    for task_id in sorted(repin_tasks, key=_text):
        if not _matches(TASK_ID_RE)(task_id):
            findings.append(PlanFinding("repin_task_malformed", _text(task_id), "not a task id"))
        elif task_id not in known:
            findings.append(PlanFinding("repin_task_unknown", task_id, "no such task"))
    return findings


def _refresh_subject(refreshed: dict[str, Any], root: ConfinedRootV1, observed_at: str) -> list[PlanFinding]:
    """Rebind the subject to the committed sources (git anchored to the bound root); the candidate SHA is never recorded."""

    snapshot, findings = source_snapshot_v1(root)
    if snapshot is None:
        return findings
    dirty = scoped_worktree_dirty_paths_v1(root, CleanlinessScopeV1.REGENERATION)
    if dirty is None:
        return [PlanFinding("scoped_worktree_status_unavailable", "subject", "git status failed or returned a malformed record")]
    branch_code, branch = _git(root, ["branch", "--show-current"])
    if branch_code == 0 and branch:
        refreshed["subject"]["branch"] = branch
    refreshed["subject"]["source_snapshot_sha256"] = snapshot.sha256
    refreshed["subject"]["source_snapshot_file_count"] = snapshot.entry_count
    refreshed["subject"]["observed_at"] = observed_at
    refreshed["subject"]["scoped_worktree_clean"] = not dirty
    return []


def _bound_gates(gates: Sequence[object]) -> tuple[list[tuple[dict[str, Any], LiveGateSpecV1]], list[PlanFinding]]:
    bound: list[tuple[dict[str, Any], LiveGateSpecV1]] = []
    findings: list[PlanFinding] = []
    for index, gate in enumerate(gates):
        gate_findings, spec = _live_gate_binding_findings(gate, label=f"live_gates[{index}]")
        findings.extend(gate_findings)
        if spec is not None and isinstance(gate, dict):
            bound.append((gate, spec))
    return bound, findings + _registry_set_findings(gates)


def refresh_plan_v1(
    plan: Mapping[str, Any],
    *,
    root: RootLike,
    observed_at: str,
    repin_tasks: Iterable[str],
) -> tuple[dict[str, Any], list[PlanFinding]]:
    """Regenerate live-gate observations, the subject binding, and named evidence pins.

    The invocation itself (a real ``YYYY-MM-DD`` date and re-pin ids that are
    well-formed and present in the plan) and then the complete
    candidate-controlled plan in the ``PRE_REGENERATION`` profile are
    validated before any gate executes; any finding returns an untouched copy
    with zero observer calls. This is the only phase that may find the two
    plan artifacts dirty.
    """

    refreshed = copy.deepcopy(dict(plan))
    repin = frozenset(repin_tasks)
    findings = _refresh_invocation_findings(plan, observed_at, repin)
    if findings:
        return refreshed, findings
    try:
        with _UseRoot(root) as bound_root:
            return refreshed, _refresh_with_root(plan, refreshed, bound_root, observed_at, repin)
    except RootUnavailable as exc:
        return refreshed, _root_unavailable(exc)


def _refresh_with_root(
    plan: Mapping[str, Any], refreshed: dict[str, Any], bound_root: ConfinedRootV1, observed_at: str, repin: frozenset[str]
) -> list[PlanFinding]:
    profile = PlanValidationProfileV1.pre_regeneration(repin)
    findings = validate_plan_v1(plan, root=bound_root, markdown=read_plan_markdown_v1(bound_root), profile=profile)
    if findings:
        return findings
    bound, findings = _bound_gates(refreshed["live_gates"])
    if findings:
        return findings
    planned, snapshot_findings = source_snapshot_v1(bound_root)
    if planned is None:
        return snapshot_findings
    try:
        supervisor = bind_supervisor_code_v1(bound_root.anchored)
    except OSError as exc:
        return [
            PlanFinding(
                "live_gate_supervisor_binding_refused",
                "refresh",
                f"{type(exc).__name__}: {exc}",
            )
        ]
    try:
        for gate, spec in bound:
            try:
                checker = bound_root.anchored.open_file(spec.checker_path)
            except OSError as exc:
                findings.append(PlanFinding("live_gate_checker_missing", spec.gate_id, f"{spec.checker_path}: {exc}"))
                continue
            with checker:
                observation, refusal = _observe_anchored(
                    spec, bound_root, checker, supervisor
                )
            current, current_findings = source_snapshot_v1(bound_root)
            if current is None or current.sha256 != planned.sha256:
                findings.extend(current_findings or [PlanFinding("live_gate_effect_snapshot_drift", spec.gate_id, "source snapshot changed during observation; observation refused")])
                continue
            if observation is None or observation.error:
                findings.append(PlanFinding("live_gate_execution_failed", spec.gate_id, refusal or (observation.error if observation else "")))
                continue
            gate.update({"checker_sha256": checker.sha256, "exit_code": observation.exit_code, "observed": observation.observed})
    finally:
        supervisor.close()
    findings.extend(_repin_evidence(refreshed, bound_root, repin))
    findings.extend(_refresh_subject(refreshed, bound_root, observed_at))
    return findings


def canonical_plan_json_v1(plan: Mapping[str, Any]) -> str:
    return json.dumps(plan, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def write_markdown_v1(root: RootLike, plan: Mapping[str, Any]) -> list[PlanFinding]:
    """Rewrite the generated block only after the complete plan validates pre-regeneration.

    The companion is read without following symlinks and replaced atomically
    inside its confined directory under the bound root identity; an
    unreadable companion raises ``PlanUnreadable`` like any other unreadable
    input.
    """

    try:
        with _UseRoot(root) as bound:
            markdown = read_plan_markdown_v1(bound)
            findings = validate_plan_v1(plan, root=bound, markdown=markdown, profile=PlanValidationProfileV1.pre_regeneration())
            if findings or markdown is None:
                return findings or [PlanFinding("plan_markdown_missing", PLAN_MARKDOWN_PATH.as_posix(), "companion markdown is required")]
            parts = _split_markdown(markdown)
            if parts is None:
                return [PlanFinding("plan_markdown_generated_block_missing", PLAN_MARKDOWN_PATH.as_posix(), "generated markers absent")]
            rendered = (parts[0] + render_generated_markdown_v1(plan) + parts[2]).encode("utf-8")
            refusal = replace_confined_file_v1(bound, PLAN_MARKDOWN_PATH, rendered)
            return [PlanFinding("plan_artifact_write_refused", PLAN_MARKDOWN_PATH.as_posix(), refusal)] if refusal else []
    except RootUnavailable as exc:
        return _root_unavailable(exc)


def _closed_plan_report_v1(
    plan: object,
    findings: object,
    *,
    executed: object,
    profile: object,
    mode: object,
    error: object = None,
    mode_accepted: object = True,
    validation_complete: object = False,
) -> dict[str, object]:
    """Build the only JSON report shape for success, typed refusal, and CLI failure.

    The report itself is a defensive boundary. It derives the literal authority
    ceiling, exact closed profile/mode labels, and a zero observer count for
    malformed requests before it exposes any candidate-controlled summary.
    """

    checked_mode, mode_findings = _mode_or_findings_v1(mode)
    checked_profile, profile_findings = _profile_or_findings_v1(profile)
    normalized_findings: list[PlanFinding] = []
    if type(findings) in (list, tuple):
        for finding in cast(list[object] | tuple[object, ...], findings):
            if _plan_finding_is_closed_v1(finding):
                normalized_findings.append(cast(PlanFinding, finding))
            else:
                normalized_findings.append(
                    PlanFinding(
                        "report_findings_invalid",
                        "findings",
                        f"expected PlanFinding, received {type(finding).__name__}",
                    )
                )
    else:
        normalized_findings.append(
            PlanFinding(
                "report_findings_invalid",
                "findings",
                f"expected list or tuple, received {type(findings).__name__}",
            )
        )
    normalized_findings.extend(mode_findings)
    normalized_findings.extend(profile_findings)
    owned_plan, ownership_findings = _owned_plan_v1(plan)
    normalized_findings.extend(ownership_findings)
    report_plan: Mapping[str, object] = owned_plan if owned_plan is not None else {}
    normalized_error = error if type(error) is str else None
    if error is not None and normalized_error is None:
        normalized_findings.append(
            PlanFinding(
                "report_error_invalid",
                "error",
                f"expected string or None, received {type(error).__name__}",
            )
        )
    if type(mode_accepted) is not bool:
        normalized_findings.append(
            PlanFinding(
                "report_mode_accepted_invalid",
                "accepted_check_mode",
                "expected an exact Boolean",
            )
        )
    elif not mode_accepted and not mode_findings:
        normalized_findings.append(
            PlanFinding(
                "report_mode_not_accepted",
                "accepted_check_mode",
                "the requested check mode was explicitly refused",
            )
        )
    if type(validation_complete) is not bool:
        normalized_findings.append(
            PlanFinding(
                "report_validation_state_invalid",
                "validation_complete",
                "expected an exact Boolean",
            )
        )
    accepted_mode = (
        checked_mode
        if checked_mode is not None
        and checked_profile is not None
        and type(mode_accepted) is bool
        and mode_accepted
        and normalized_error is None
        else None
    )
    executed_is_valid = type(executed) is int and executed >= 0
    normalized_executed = executed if executed_is_valid else 0
    if not executed_is_valid:
        normalized_findings.append(
            PlanFinding(
                "report_executed_live_gates_invalid",
                "executed_live_gates",
                "expected a nonnegative exact integer",
            )
        )
    if accepted_mode is None or checked_profile is None:
        normalized_executed = 0
    elif not normalized_findings and accepted_mode is PlanCheckModeV1.STRUCTURAL and normalized_executed != 0:
        normalized_findings.append(
            PlanFinding(
                "report_structural_observer_count_invalid",
                "executed_live_gates",
                "structural mode cannot report live-gate observations",
            )
        )
        normalized_executed = 0
    elif (
        not normalized_findings
        and accepted_mode is PlanCheckModeV1.EXECUTE
        and normalized_executed != len(LIVE_GATE_REGISTRY)
    ):
        normalized_findings.append(
            PlanFinding(
                "report_execute_observer_count_invalid",
                "executed_live_gates",
                f"accepted execute requires exactly {len(LIVE_GATE_REGISTRY)} observer calls",
            )
        )
        normalized_executed = 0
    if (
        type(validation_complete) is bool
        and not validation_complete
        and not normalized_findings
        and normalized_error is None
    ):
        normalized_findings.append(
            PlanFinding(
                "report_validation_missing",
                "plan",
                "public report construction has no completed checker validation",
            )
        )
    raw_tasks = report_plan.get("tasks")
    tasks = [task for task in raw_tasks if type(task) is dict] if type(raw_tasks) is list else []
    raw_gates = report_plan.get("vm_gate_status")
    gate_entries = [entry for entry in raw_gates if type(entry) is dict] if type(raw_gates) is list else []
    return {
        "accepted_check_mode": accepted_mode.value if accepted_mode is not None else "none",
        "authority": dict(REQUIRED_AUTHORITY),
        "cleanliness_scope": checked_profile.cleanliness.value if checked_profile is not None else "invalid",
        "closed_task_count": sum(1 for task in tasks if _in(CLOSED_TASK_STATUSES)(task.get("status"))),
        "error": normalized_error,
        "executed_live_gates": normalized_executed,
        "findings": [finding.to_dict() for finding in normalized_findings],
        "nonclaims": list(NONCLAIMS),
        "ok": not normalized_findings and normalized_error is None,
        "requested_check_mode": checked_mode.value if checked_mode is not None else "invalid",
        "schema": CHECK_SCHEMA_V1,
        "task_count": len(tasks),
        "validation_profile": checked_profile.kind.value if checked_profile is not None else "invalid",
        "vm_gate_status": {
            entry["gate_id"]: entry["status"]
            for entry in gate_entries
            if type(entry.get("gate_id")) is str and type(entry.get("status")) is str
        },
    }


def plan_report_v1(
    plan: Mapping[str, Any],
    findings: Sequence[PlanFinding],
    *,
    executed: int,
    profile: PlanValidationProfileV1,
    mode: PlanCheckModeV1 = PlanCheckModeV1.STRUCTURAL,
    error: str | None = None,
    mode_accepted: bool = True,
) -> dict[str, object]:
    """Build a fail-closed report without claiming caller-supplied validation."""

    return _closed_plan_report_v1(
        plan,
        findings,
        executed=executed,
        profile=profile,
        mode=mode,
        error=error,
        mode_accepted=mode_accepted,
    )


def _validated_plan_report_v1(
    plan: Mapping[str, Any],
    findings: Sequence[PlanFinding],
    *,
    executed: int,
    profile: PlanValidationProfileV1,
    mode: PlanCheckModeV1 = PlanCheckModeV1.STRUCTURAL,
    error: str | None = None,
    mode_accepted: bool = True,
) -> dict[str, object]:
    """Internal report builder used only after a checker-owned validation path."""

    return _closed_plan_report_v1(
        plan,
        findings,
        executed=executed,
        profile=profile,
        mode=mode,
        error=error,
        mode_accepted=mode_accepted,
        validation_complete=True,
    )


def _structural_report(
    root: ConfinedRootV1,
    profile: PlanValidationProfileV1,
    artifacts: BoundPlanArtifactsV1 | None = None,
) -> tuple[Mapping[str, Any], list[PlanFinding]]:
    """Validate path reads for regeneration or held exact-HEAD bytes for execution."""

    if artifacts is None:
        plan = load_plan_v1(root)
        markdown = read_plan_markdown_v1(root)
    else:
        plan, markdown = _decode_bound_plan_artifacts_v1(artifacts)
    return plan, validate_plan_v1(plan, root=root, markdown=markdown, profile=profile)


def _raise_if_plan_artifacts_unreadable_v1(root: ConfinedRootV1) -> None:
    """Preserve typed unreadable diagnostics after binding has already refused.

    These mutable-path reads can only refine a failure into ``PlanUnreadable``;
    their values are discarded and can never become accepted plan semantics.
    """

    load_plan_v1(root)
    if read_plan_markdown_v1(root) is None:
        raise PlanUnreadable("plan markdown is missing")


def _ordinary_context_result_v1(
    root: ConfinedRootV1,
    context: ExecutionContextV1,
    mode: PlanCheckModeV1,
) -> tuple[Mapping[str, Any], list[PlanFinding], int]:
    """Decode the held artifacts, validate, optionally execute, and recheck."""

    checked_mode, mode_findings = _mode_or_findings_v1(mode)
    if checked_mode is None:
        return {}, mode_findings, 0
    try:
        plan, findings = _structural_report(
            root, ORDINARY_VALIDATION_PROFILE_V1, context._artifacts
        )
    except PlanUnreadable as exc:
        return {}, [
            PlanFinding("plan_artifact_unreadable", "plan_artifacts", str(exc))
        ], 0
    if checked_mode is PlanCheckModeV1.STRUCTURAL:
        return plan, findings, 0
    findings.extend(
        _bound_execution_context_findings(
            context, root, subject="whole_program_plan"
        )
    )
    executed = 0
    if not findings:
        execution_findings, executed = _execute_live_gates_with_count_v1(
            plan, root, context=context
        )
        findings.extend(execution_findings)
    if not findings:
        findings.extend(
            _bound_execution_context_findings(
                context, root, subject="whole_program_plan"
            )
        )
    return plan, findings, executed


def check_whole_program_plan_v1(root: RootLike = REPO_ROOT, *, mode: PlanCheckModeV1 = PlanCheckModeV1.STRUCTURAL) -> dict[str, object]:
    """Return the ordinary deterministic report (``FULL`` cleanliness); never grants authority.

    The root identity, exact HEAD/FULL cleanliness, and both HEAD-bound sealed
    artifacts are recorded before either artifact is decoded. In ``EXECUTE``
    mode the same trusted-process context and artifact digests are preserved
    through validation, planning, every observer, and final report construction.
    """

    checked_mode, _mode_findings = _mode_or_findings_v1(mode)
    if checked_mode is None:
        return _validated_plan_report_v1(
            {},
            [],
            executed=0,
            profile=ORDINARY_VALIDATION_PROFILE_V1,
            mode=mode,
            mode_accepted=False,
        )
    try:
        with _UseRoot(root) as bound:
            context, findings = _bind_execution_context_v1(
                bound, subject="whole_program_plan"
            )
            if context is None:
                _raise_if_plan_artifacts_unreadable_v1(bound)
                return _validated_plan_report_v1(
                    {},
                    findings,
                    executed=0,
                    profile=ORDINARY_VALIDATION_PROFILE_V1,
                    mode=checked_mode,
                )
            try:
                plan, findings, executed = _ordinary_context_result_v1(
                    bound, context, checked_mode
                )
                return _validated_plan_report_v1(
                    plan,
                    findings,
                    executed=executed,
                    profile=ORDINARY_VALIDATION_PROFILE_V1,
                    mode=checked_mode,
                )
            finally:
                context.close()
    except PlanUnreadable as exc:
        return _validated_plan_report_v1(
            {},
            [PlanFinding("plan_unreadable", "plan_artifacts", str(exc))],
            executed=0,
            profile=ORDINARY_VALIDATION_PROFILE_V1,
            mode=checked_mode,
            error=str(exc),
            mode_accepted=False,
        )


def post_regeneration_report_v1(root: RootLike) -> dict[str, object]:
    """Structural report right after ``--refresh``/``--render``: every comparison, artifacts may be uncommitted."""

    with _UseRoot(root) as bound:
        plan, findings = _structural_report(bound, POST_REGENERATION_PROFILE_V1)
    return _validated_plan_report_v1(
        plan,
        findings,
        executed=0,
        profile=POST_REGENERATION_PROFILE_V1,
        mode=PlanCheckModeV1.STRUCTURAL,
    )


def _emit(payload: Mapping[str, object]) -> None:
    print(json.dumps(payload, indent=2, sort_keys=True))


def _failure(
    findings: Sequence[PlanFinding],
    *,
    profile: PlanValidationProfileV1,
    mode: PlanCheckModeV1,
    error: str | None = None,
    mode_accepted: bool = True,
    exit_code: int = 1,
) -> int:
    """Emit one closed report for every CLI refusal without weakening authority labels."""

    _emit(
        _validated_plan_report_v1(
            {},
            findings,
            executed=0,
            profile=profile,
            mode=mode,
            error=error,
            mode_accepted=mode_accepted,
        )
    )
    return exit_code


def _run_refresh(root: RootLike, observed_at: str | None, repin: Sequence[str]) -> int:
    if observed_at is None or not _is_date(observed_at):
        return _failure(
            [
                PlanFinding(
                    "cli_observed_at_invalid",
                    "--observed-at",
                    "--refresh requires --observed-at YYYY-MM-DD",
                )
            ],
            profile=PlanValidationProfileV1.pre_regeneration(),
            mode=PlanCheckModeV1.STRUCTURAL,
            error="--refresh requires --observed-at YYYY-MM-DD",
            mode_accepted=False,
            exit_code=2,
        )
    refreshed, findings = refresh_plan_v1(load_plan_v1(root), root=root, observed_at=observed_at, repin_tasks=repin)
    if findings:
        return _failure(
            findings,
            profile=PlanValidationProfileV1.pre_regeneration(),
            mode=PlanCheckModeV1.STRUCTURAL,
        )
    findings = write_markdown_v1(root, refreshed)
    if findings:
        return _failure(
            findings,
            profile=PlanValidationProfileV1.pre_regeneration(),
            mode=PlanCheckModeV1.STRUCTURAL,
        )
    refusal = replace_confined_file_v1(root, PLAN_JSON_PATH, canonical_plan_json_v1(refreshed).encode("utf-8"))
    return (
        _failure(
            [PlanFinding("plan_artifact_write_refused", PLAN_JSON_PATH.as_posix(), refusal)],
            profile=PlanValidationProfileV1.pre_regeneration(),
            mode=PlanCheckModeV1.STRUCTURAL,
        )
        if refusal
        else 0
    )


def _parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = _ClosedPlanArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--execute",
        action="store_true",
        help="bind exact sealed plan artifacts, re-run every registry gate, and compare observations",
    )
    parser.add_argument("--refresh", action="store_true", help="regenerate live-gate observations and subject lineage")
    parser.add_argument("--observed-at", help="YYYY-MM-DD recorded with --refresh")
    parser.add_argument("--repin-evidence", action="append", default=[], metavar="TASK_ID")
    parser.add_argument("--render", action="store_true", help="rewrite the generated markdown block")
    return parser.parse_args(list(argv) if argv is not None else None)


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = _parse_args(argv)
    except PlanCliUsageError as exc:
        return _failure(
            [PlanFinding("cli_arguments_invalid", "argv", str(exc))],
            profile=ORDINARY_VALIDATION_PROFILE_V1,
            mode=PlanCheckModeV1.STRUCTURAL,
            error=str(exc),
            mode_accepted=False,
            exit_code=2,
        )
    root = Path(args.root)
    regenerating = bool(args.refresh or args.render)
    mode = PlanCheckModeV1.EXECUTE if args.execute else PlanCheckModeV1.STRUCTURAL
    failure_profile = (
        PlanValidationProfileV1.pre_regeneration()
        if regenerating
        else ORDINARY_VALIDATION_PROFILE_V1
    )
    if regenerating and args.execute:
        return _failure(
            [
                PlanFinding(
                    "cli_arguments_invalid",
                    "argv",
                    "--execute requires a fully committed worktree; run it after committing the regenerated artifacts",
                )
            ],
            profile=failure_profile,
            mode=mode,
            error="--execute requires a fully committed worktree; run it after committing the regenerated artifacts",
            mode_accepted=False,
            exit_code=2,
        )
    try:
        with ConfinedRootV1.bind(root) as bound:
            if args.refresh:
                code = _run_refresh(bound, args.observed_at, args.repin_evidence)
                if code:
                    return code
            elif args.render:
                findings = write_markdown_v1(bound, load_plan_v1(bound))
                if findings:
                    return _failure(
                        findings,
                        profile=PlanValidationProfileV1.pre_regeneration(),
                        mode=PlanCheckModeV1.STRUCTURAL,
                    )
            if regenerating:
                report = post_regeneration_report_v1(bound)
            else:
                report = check_whole_program_plan_v1(bound, mode=mode)
    except PlanUnreadable as exc:
        return _failure(
            [PlanFinding("plan_unreadable", "plan_artifacts", str(exc))],
            profile=failure_profile,
            mode=mode,
            error=str(exc),
            mode_accepted=False,
            exit_code=2,
        )
    if args.json or not report["ok"]:
        _emit(report)
    elif regenerating:
        print(f"whole-program plan regenerated ({report['cleanliness_scope']} scope); commit both plan artifacts before any ordinary check or --execute")
    else:
        print(f"whole-program plan ok; {report['closed_task_count']}/{report['task_count']} tasks closed; production_authority remains NONE")
    if report["ok"]:
        return 0
    return 2 if type(report["error"]) is str and report["error"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
