"""Immutable records and canonical roots for the O-007C inventory."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import PurePosixPath
from typing import NoReturn

_SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")


class IndirectSinkRejectV1(ValueError):
    """Stable fail-closed rejection from an O-007C boundary."""

    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code}: {path}: {detail}")
        self.code = code
        self.path = path
        self.detail = detail


def reject(code: str, path: str, detail: str) -> NoReturn:
    raise IndirectSinkRejectV1(code, path, detail)


def canonical_json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def pretty_json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def canonical_root(domain: str, value: object) -> str:
    return hashlib.sha256(domain.encode("ascii") + b"\0" + canonical_json_bytes(value)).hexdigest()


def require_sha256(value: object, *, path: str) -> str:
    if type(value) is not str or _SHA256_RE.fullmatch(value) is None:
        reject("SHA256", path, "expected lowercase SHA-256")
    return value


def require_relative_path(value: object, *, path: str) -> str:
    if type(value) is not str or not value or value.startswith("/") or "\\" in value:
        reject("TARGET_ESCAPE", path, "path is not canonical repository-relative")
    parts = PurePosixPath(value).parts
    if any(part in {"", ".", ".."} for part in parts):
        reject("TARGET_ESCAPE", path, "path contains a forbidden component")
    if PurePosixPath(*parts).as_posix() != value:
        reject("TARGET_ESCAPE", path, "path is not canonical repository-relative")
    return value


class SourceDispositionV1(str, Enum):
    INVENTORIED_NONPRIMARY_RUNTIME_WRITER = "INVENTORIED_NONPRIMARY_RUNTIME_WRITER"
    GENERATED_REFERENCE_SOURCE_BOUND = "GENERATED_REFERENCE_SOURCE_BOUND"
    SOURCE_BOUND_RESEARCH_OR_OPERATOR_EXCLUSION = "SOURCE_BOUND_RESEARCH_OR_OPERATOR_EXCLUSION"


class DynamicDispositionV1(str, Enum):
    DERIVED_LOCAL_LITERAL_TARGET = "DERIVED_LOCAL_LITERAL_TARGET"
    DERIVED_EXTERNAL_LITERAL_TARGET = "DERIVED_EXTERNAL_LITERAL_TARGET"
    DERIVED_CLOSED_STATIC_REGISTRY = "DERIVED_CLOSED_STATIC_REGISTRY"
    CLOSED_LOCAL_TARGET_SET = "CLOSED_LOCAL_TARGET_SET"
    SOURCE_BOUND_RESEARCH_EXCLUSION = "SOURCE_BOUND_RESEARCH_EXCLUSION"


class GapDispositionV1(str, Enum):
    GENERATED_SOURCE_SCANNED_AND_PINNED = "GENERATED_SOURCE_SCANNED_AND_PINNED"
    DYNAMIC_DECLARATION_DISPOSITIONED = "DYNAMIC_DECLARATION_DISPOSITIONED"
    EXTERNAL_PROCESS_PORT_RECORDED = "EXTERNAL_PROCESS_PORT_RECORDED"
    UNRESOLVED_OPERATOR_PROCESS_BOUNDARY = "UNRESOLVED_OPERATOR_PROCESS_BOUNDARY"
    SOURCE_BOUND_RESEARCH_OR_OPERATOR_EXCLUSION = "SOURCE_BOUND_RESEARCH_OR_OPERATOR_EXCLUSION"


class LifecycleDispositionV1(str, Enum):
    INVENTORIED_RECOVERY_SURFACE = "INVENTORIED_RECOVERY_SURFACE"
    UNMOUNTED_MIGRATION_ENTRYPOINT = "UNMOUNTED_MIGRATION_ENTRYPOINT"
    INVENTORIED_CALLBACK_SURFACE = "INVENTORIED_CALLBACK_SURFACE"
    MISSING_MOUNTED_WORKER_ENTRYPOINT = "MISSING_MOUNTED_WORKER_ENTRYPOINT"
    INVENTORIED_ADMINISTRATIVE_SURFACE = "INVENTORIED_ADMINISTRATIVE_SURFACE"


@dataclass(frozen=True, slots=True, order=True)
class DynamicDeclarationV1:
    path: str
    line: int
    mechanism: str
    fingerprint: str
    primary_reachable: bool
    source_sha256: str
    target_expression: str
    target_kind: str
    target_status: str
    targets: tuple[str, ...]

    def to_json(self) -> dict[str, object]:
        value = asdict(self)
        value["targets"] = list(self.targets)
        return value


@dataclass(frozen=True, slots=True, order=True)
class IndirectAliasV1:
    path: str
    symbol: str
    line: int
    sink_kind: str
    fingerprint: str
    primary_reachable: bool

    def to_json(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True, slots=True, order=True)
class LifecycleRecordV1:
    path: str
    symbol: str
    line: int
    categories: tuple[str, ...]
    fingerprint: str
    primary_reachable: bool

    def to_json(self) -> dict[str, object]:
        value = asdict(self)
        value["categories"] = list(self.categories)
        return value
