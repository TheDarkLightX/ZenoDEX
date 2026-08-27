#!/usr/bin/env python3
"""Source pins, owned reads, and exact binding (WholeEconomyDisasterCoverageV1).

A pin binds path, Git mode, blob OID, SHA-256, and byte size.  Binding
consumes the single owned read of each path together with its lstat and
captured-tree probes; every mismatch fails closed with an exact code.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence, cast

from tools.runtime_disaster_discovery_primitives_v1 import (
    RejectCodeV1,
    domain_root,
    git_blob_oid,
    reject,
    require_closed_object,
    require_enum,
    require_git_oid,
    require_int,
    require_list,
    require_sha256,
    require_string,
    sha256_hex,
    validate_repo_path,
)
from tools.runtime_disaster_discovery_vocabulary_v1 import (
    MAX_SOURCE_BYTES_V1,
    REQUIRED_SOURCE_PINS_V1,
    HeadBindingV1,
    PathKindV1,
    SourceRoleV1,
)

_PIN_FIELDS = ("path", "role", "git_mode", "blob_oid", "sha256", "byte_size")
REGULAR_GIT_MODES_V1 = frozenset({"100644", "100755"})


@dataclass(frozen=True, slots=True)
class SourcePinV1:
    """Registry-declared exact binding of one repository file."""

    path: str
    role: SourceRoleV1
    git_mode: str
    blob_oid: str
    sha256: str
    byte_size: int

    def to_canonical(self) -> dict[str, object]:
        return {
            "path": self.path,
            "role": self.role.value,
            "git_mode": self.git_mode,
            "blob_oid": self.blob_oid,
            "sha256": self.sha256,
            "byte_size": self.byte_size,
        }


@dataclass(frozen=True, slots=True)
class HeadEntryV1:
    """One ``git ls-tree -z <captured tree oid> -- <path>`` row supplied by a shell probe."""

    path: str
    git_mode: str
    object_type: str
    object_id: str


@dataclass(frozen=True, slots=True)
class OwnedSourceV1:
    """Exactly one read of one path plus its lstat and captured-tree probes."""

    path: str
    kind: PathKindV1
    symlink_in_ancestry: bool
    data: bytes | None
    head_entry: HeadEntryV1 | None
    head_probe_available: bool


@dataclass(frozen=True, slots=True)
class BoundSourceV1:
    """A source whose owned bytes match the registry pin exactly."""

    pin: SourcePinV1
    data: bytes
    head_binding: HeadBindingV1

    def to_canonical(self) -> dict[str, object]:
        return {"pin": self.pin.to_canonical(), "head_binding": self.head_binding.value}


def parse_source_pin(value: object, name: str) -> SourcePinV1:
    raw = require_closed_object(value, _PIN_FIELDS, name)
    git_mode = require_string(raw["git_mode"], f"{name}.git_mode", max_chars=6)
    if (
        not git_mode.isdigit()
        or len(git_mode) != 6
        or any(char not in "01234567" for char in git_mode)
    ):
        raise reject(RejectCodeV1.SOURCE_GIT_MODE_INVALID, f"{name}: {git_mode}")
    if git_mode == "160000":
        raise reject(RejectCodeV1.SOURCE_SUBMODULE, name)
    if git_mode not in REGULAR_GIT_MODES_V1:
        raise reject(RejectCodeV1.SOURCE_GIT_MODE_INVALID, f"{name}: {git_mode}")
    return SourcePinV1(
        path=validate_repo_path(raw["path"], f"{name}.path"),
        role=cast(SourceRoleV1, require_enum(raw["role"], SourceRoleV1, f"{name}.role")),
        git_mode=git_mode,
        blob_oid=require_git_oid(raw["blob_oid"], f"{name}.blob_oid"),
        sha256=require_sha256(raw["sha256"], f"{name}.sha256"),
        byte_size=require_int(
            raw["byte_size"], f"{name}.byte_size", low=1, high=MAX_SOURCE_BYTES_V1
        ),
    )


def parse_source_pins(value: object, name: str) -> tuple[SourcePinV1, ...]:
    """Require exactly the closed pin universe, unique paths, and sorted order."""

    pins = tuple(
        parse_source_pin(item, f"{name}[{index}]")
        for index, item in enumerate(require_list(value, name))
    )
    observed = tuple((pin.path, pin.role) for pin in pins)
    paths = [pin.path for pin in pins]
    if len(set(paths)) != len(paths):
        raise reject(RejectCodeV1.PATH_DUPLICATE, name)
    if tuple(sorted(observed)) != REQUIRED_SOURCE_PINS_V1:
        missing = sorted(set(REQUIRED_SOURCE_PINS_V1) - set(observed))
        if missing:
            raise reject(RejectCodeV1.SOURCE_PIN_MISSING, f"{name}: {missing[0][0]}")
        extra = sorted(set(observed) - set(REQUIRED_SOURCE_PINS_V1))
        raise reject(RejectCodeV1.SOURCE_PIN_UNEXPECTED, f"{name}: {extra[0][0]}")
    if observed != tuple(sorted(observed)):
        raise reject(RejectCodeV1.RESULT_ORDER_INVALID, f"{name}: pins must be sorted by path")
    return pins


def _head_binding(pin: SourcePinV1, owned: OwnedSourceV1, computed_oid: str) -> HeadBindingV1:
    if not owned.head_probe_available:
        return HeadBindingV1.PROBE_UNAVAILABLE
    entry = owned.head_entry
    if entry is None:
        return HeadBindingV1.NOT_IN_HEAD
    if entry.git_mode == "160000" or entry.object_type != "blob":
        raise reject(RejectCodeV1.SOURCE_SUBMODULE, pin.path)
    if entry.git_mode == "120000":
        raise reject(RejectCodeV1.PATH_SYMLINK, f"{pin.path}: HEAD symlink")
    if entry.git_mode != pin.git_mode:
        raise reject(RejectCodeV1.SOURCE_GIT_MODE_INVALID, f"{pin.path}: HEAD {entry.git_mode}")
    if entry.object_id != computed_oid:
        return HeadBindingV1.HEAD_BLOB_MISMATCH
    return HeadBindingV1.HEAD_BLOB_MATCH


def bind_source(pin: SourcePinV1, owned: OwnedSourceV1) -> BoundSourceV1:
    """Bind one owned read to its pin; every mismatch fails closed."""

    name = pin.path
    if owned.path != pin.path:
        raise reject(RejectCodeV1.PATH_INVALID, f"{name}: owned path mismatch")
    if owned.symlink_in_ancestry or owned.kind is PathKindV1.SYMLINK:
        raise reject(RejectCodeV1.PATH_SYMLINK, name)
    if owned.kind is PathKindV1.OVERSIZE:
        raise reject(RejectCodeV1.SOURCE_OVERSIZE, name)
    if owned.kind is not PathKindV1.REGULAR:
        raise reject(RejectCodeV1.PATH_NOT_REGULAR_FILE, f"{name}: {owned.kind.value}")
    if owned.data is None:
        raise reject(RejectCodeV1.SOURCE_UNREADABLE, name)
    if len(owned.data) != pin.byte_size:
        raise reject(RejectCodeV1.SOURCE_SIZE_DRIFT, f"{name}: {len(owned.data)}")
    if sha256_hex(owned.data) != pin.sha256:
        raise reject(RejectCodeV1.SOURCE_HASH_DRIFT, name)
    computed_oid = git_blob_oid(owned.data)
    if computed_oid != pin.blob_oid:
        raise reject(RejectCodeV1.SOURCE_BLOB_DRIFT, name)
    binding = _head_binding(pin, owned, computed_oid)
    if pin.role in (SourceRoleV1.SEMANTIC_SOURCE, SourceRoleV1.PROFILE_RELEASE):
        if binding is HeadBindingV1.PROBE_UNAVAILABLE:
            raise reject(RejectCodeV1.GIT_PROBE_UNAVAILABLE, name)
        if binding is not HeadBindingV1.HEAD_BLOB_MATCH:
            raise reject(RejectCodeV1.SOURCE_BLOB_DRIFT, f"{name}: {binding.value}")
    return BoundSourceV1(pin=pin, data=owned.data, head_binding=binding)


def bind_sources(
    pins: Sequence[SourcePinV1],
    owned: Mapping[str, OwnedSourceV1],
) -> tuple[BoundSourceV1, ...]:
    extra = sorted(set(owned) - {pin.path for pin in pins})
    if extra:
        raise reject(RejectCodeV1.SOURCE_PIN_UNEXPECTED, extra[0])
    bound: list[BoundSourceV1] = []
    for pin in pins:
        if pin.path not in owned:
            raise reject(RejectCodeV1.SOURCE_UNREADABLE, pin.path)
        bound.append(bind_source(pin, owned[pin.path]))
    return tuple(bound)


def owned_source_matches_head_v1(owned: OwnedSourceV1) -> bool:
    """Return whether one owned regular-file snapshot is the captured-tree blob.

    This check is used for the registry itself, whose bytes cannot self-pin in
    the registry.  It therefore participates in the execution premise without
    becoming part of the registry-declared source-pin set.
    """

    entry = owned.head_entry
    return (
        owned.head_probe_available
        and not owned.symlink_in_ancestry
        and owned.kind is PathKindV1.REGULAR
        and owned.data is not None
        and entry is not None
        and entry.path == owned.path
        and entry.git_mode in REGULAR_GIT_MODES_V1
        and entry.object_type == "blob"
        and entry.object_id == git_blob_oid(owned.data)
    )


def source_pins_root(pins: Sequence[SourcePinV1]) -> str:
    return domain_root("wedc1-source-pins", [pin.to_canonical() for pin in pins])


def bind_artifact(artifacts: Mapping[str, OwnedSourceV1], path: str, sha256: str) -> None:
    """Require a referenced artifact to be a committed regular file with the exact hash."""

    owned = artifacts.get(path)
    if owned is None:
        raise reject(RejectCodeV1.ARTIFACT_UNBOUND, path)
    if owned.symlink_in_ancestry or owned.kind is PathKindV1.SYMLINK:
        raise reject(RejectCodeV1.PATH_SYMLINK, path)
    if owned.kind is PathKindV1.OVERSIZE:
        raise reject(RejectCodeV1.SOURCE_OVERSIZE, path)
    if owned.data is None:
        raise reject(RejectCodeV1.ARTIFACT_UNBOUND, path)
    if owned.kind is not PathKindV1.REGULAR:
        raise reject(RejectCodeV1.PATH_NOT_REGULAR_FILE, f"{path}: {owned.kind.value}")
    if sha256_hex(owned.data) != sha256:
        raise reject(RejectCodeV1.ARTIFACT_HASH_MISMATCH, path)
    if not owned.head_probe_available:
        raise reject(RejectCodeV1.GIT_PROBE_UNAVAILABLE, path)
    entry = owned.head_entry
    if entry is None or entry.object_type != "blob" or entry.git_mode not in REGULAR_GIT_MODES_V1:
        raise reject(RejectCodeV1.ARTIFACT_UNBOUND, f"{path}: not a committed regular file")
    if entry.object_id != git_blob_oid(owned.data):
        raise reject(RejectCodeV1.ARTIFACT_HASH_MISMATCH, f"{path}: HEAD blob")
