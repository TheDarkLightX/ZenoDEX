from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from src.fire.registry.object_manifest_v1 import FireObjectManifest
from src.fire.verifier.cert_v1 import _require_sha256_prefixed


LOCK_SCHEMA = "zenodex/fire-object-lock/v1"


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _canonical_json_bytes(payload: dict[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def fire_object_lock_sha256(payload_without_hash: dict[str, object]) -> str:
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(payload_without_hash)).hexdigest()


def fire_object_lock_file_sha256(lock: "FireObjectDependencyLock") -> str:
    return fire_object_lock_sha256(lock.to_dict())


@dataclass(frozen=True)
class FireLockedDependency:
    name: str
    dependency_kind: str
    object_id: str
    object_version: str
    interface_output: str
    ir_hash: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        object.__setattr__(self, "dependency_kind", _require_nonempty_str("dependency_kind", self.dependency_kind))
        object.__setattr__(self, "object_id", _require_nonempty_str("object_id", self.object_id))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        object.__setattr__(self, "interface_output", _require_nonempty_str("interface_output", self.interface_output))
        object.__setattr__(self, "ir_hash", _require_sha256_prefixed("ir_hash", self.ir_hash))

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "dependency_kind": self.dependency_kind,
            "object_id": self.object_id,
            "object_version": self.object_version,
            "interface_output": self.interface_output,
            "ir_hash": self.ir_hash,
        }

    @classmethod
    def from_dict(cls, payload: object) -> "FireLockedDependency":
        if not isinstance(payload, dict):
            raise TypeError("dependency payload must be an object")
        return cls(
            name=payload.get("name"),
            dependency_kind=payload.get("dependency_kind"),
            object_id=payload.get("object_id"),
            object_version=payload.get("object_version"),
            interface_output=payload.get("interface_output"),
            ir_hash=payload.get("ir_hash"),
        )


@dataclass(frozen=True)
class FireObjectDependencyLock:
    object_name: str
    object_version: str
    object_hash: str
    dependencies: tuple[FireLockedDependency, ...]
    lock_hash: str
    schema: str = LOCK_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "object_name", _require_nonempty_str("object_name", self.object_name))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        object.__setattr__(self, "object_hash", _require_sha256_prefixed("object_hash", self.object_hash))
        object.__setattr__(self, "lock_hash", _require_sha256_prefixed("lock_hash", self.lock_hash))
        if self.schema != LOCK_SCHEMA:
            raise ValueError(f"unsupported lock schema: {self.schema}")
        if not isinstance(self.dependencies, tuple):
            raise TypeError("dependencies must be a tuple")
        if any(not isinstance(item, FireLockedDependency) for item in self.dependencies):
            raise TypeError("dependencies must contain FireLockedDependency values")
        dependency_names = [item.name for item in self.dependencies]
        if len(dependency_names) != len(set(dependency_names)):
            raise ValueError("duplicate dependency names")

    def payload_without_hash(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "object_name": self.object_name,
            "object_version": self.object_version,
            "object_hash": self.object_hash,
            "dependencies": [item.to_dict() for item in self.dependencies],
        }

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["lock_hash"] = self.lock_hash
        return payload

    @classmethod
    def build(
        cls,
        *,
        object_name: str,
        object_version: str,
        object_hash: str,
        dependencies: Sequence[FireLockedDependency],
    ) -> "FireObjectDependencyLock":
        dependency_items = tuple(sorted(dependencies, key=lambda item: item.name))
        payload_without_hash = {
            "schema": LOCK_SCHEMA,
            "object_name": object_name,
            "object_version": object_version,
            "object_hash": object_hash,
            "dependencies": [item.to_dict() for item in dependency_items],
        }
        return cls(
            object_name=object_name,
            object_version=object_version,
            object_hash=object_hash,
            dependencies=dependency_items,
            lock_hash=fire_object_lock_sha256(payload_without_hash),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireObjectDependencyLock":
        if not isinstance(payload, dict):
            raise TypeError("lock payload must be an object")
        dependencies = payload.get("dependencies")
        if not isinstance(dependencies, list):
            raise TypeError("dependencies must be a list")
        return cls(
            schema=payload.get("schema", LOCK_SCHEMA),
            object_name=payload.get("object_name"),
            object_version=payload.get("object_version"),
            object_hash=payload.get("object_hash"),
            dependencies=tuple(FireLockedDependency.from_dict(item) for item in dependencies),
            lock_hash=payload.get("lock_hash"),
        )


def build_fire_object_dependency_lock(object_manifest: FireObjectManifest) -> FireObjectDependencyLock:
    from src.fire.runtime.interface_registry_v1 import get_fire_interface_entry

    dependencies: list[FireLockedDependency] = []
    for imported in object_manifest.imported_interfaces:
        interface_spec = get_fire_interface_entry(imported.interface_object_id)
        dependencies.append(
            FireLockedDependency(
                name=imported.name,
                dependency_kind="interface",
                object_id=interface_spec.object_id,
                object_version=interface_spec.object_version,
                interface_output=imported.interface_output,
                ir_hash=interface_spec.ir_hash,
            )
        )
    return FireObjectDependencyLock.build(
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        object_hash=object_manifest.manifest_hash,
        dependencies=dependencies,
    )


def verify_fire_object_dependency_lock(
    lock: FireObjectDependencyLock,
    *,
    object_manifest: FireObjectManifest,
) -> tuple[bool, str | None]:
    if lock.object_hash != object_manifest.manifest_hash:
        return False, "lock_object_hash_mismatch"
    expected_hash = fire_object_lock_sha256(lock.payload_without_hash())
    if lock.lock_hash != expected_hash:
        return False, "lock_hash_mismatch"
    expected_lock = build_fire_object_dependency_lock(object_manifest)
    if lock.dependencies != expected_lock.dependencies:
        return False, "lock_dependencies_mismatch"
    return True, None


def write_fire_object_dependency_lock(path: str | Path, lock: FireObjectDependencyLock) -> str:
    file_path = Path(path)
    file_path.write_bytes(_canonical_json_bytes(lock.to_dict()))
    return fire_object_lock_file_sha256(lock)


def load_fire_object_dependency_lock(path: str | Path) -> tuple[FireObjectDependencyLock, str]:
    file_path = Path(path)
    payload_bytes = file_path.read_bytes()
    payload = json.loads(payload_bytes.decode("utf-8"))
    lock = FireObjectDependencyLock.from_dict(payload)
    file_sha256 = "sha256:" + hashlib.sha256(payload_bytes).hexdigest()
    return lock, file_sha256


__all__ = [
    "FireLockedDependency",
    "FireObjectDependencyLock",
    "LOCK_SCHEMA",
    "build_fire_object_dependency_lock",
    "fire_object_lock_file_sha256",
    "fire_object_lock_sha256",
    "load_fire_object_dependency_lock",
    "verify_fire_object_dependency_lock",
    "write_fire_object_dependency_lock",
]
