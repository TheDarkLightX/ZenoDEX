"""Immutable values and canonical roots for the O-007B inventory."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any


def canonical_bytes(value: Any) -> bytes:
    """Encode an inventory value with one deterministic JSON representation."""

    return json.dumps(
        value,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")


def canonical_root(value: Any) -> str:
    """Bind an inventory value under the O-007B domain separator."""

    return hashlib.sha256(
        b"zenodex-m6-cross-language-sinks-v1\0" + canonical_bytes(value)
    ).hexdigest()


@dataclass(frozen=True, slots=True, order=True)
class CrossLanguageObservationV1:
    language: str
    path: str
    operation_kind: str
    effect_class: str
    occurrence_count: int
    fingerprint: str
    mediation_status: str
    provenance: str
    source_role: str

    def to_dict(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True, slots=True, order=True)
class GeneratedPythonOwnerV1:
    path: str
    owner_class: str
    declared_owner: str
    ir_sha256: str
    replay_binding: str

    def to_dict(self) -> dict[str, str]:
        return asdict(self)


@dataclass(frozen=True, slots=True, order=True)
class DynamicImportDeclarationV1:
    path: str
    line: int
    mechanism: str
    target_status: str
    targets: tuple[str, ...]
    fingerprint: str

    def to_dict(self) -> dict[str, object]:
        return {
            "fingerprint": self.fingerprint,
            "line": self.line,
            "mechanism": self.mechanism,
            "path": self.path,
            "target_status": self.target_status,
            "targets": list(self.targets),
        }


@dataclass(frozen=True, slots=True, order=True)
class GeneratedIncludeOwnerV1:
    path: str
    build_path: str
    include_kind: str
    source_sha256: str
    build_sha256: str

    def to_dict(self) -> dict[str, str]:
        return asdict(self)
