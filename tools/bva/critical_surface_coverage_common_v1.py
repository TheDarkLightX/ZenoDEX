"""Strict primitives shared by the critical BVA inventory validators."""

from __future__ import annotations

import hashlib
import json
import string
from pathlib import Path
from typing import Any, Mapping, cast


class CoverageManifestError(RuntimeError):
    """The inventory or one of its source-bound artifacts is invalid."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CoverageManifestError(message)


def reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise CoverageManifestError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def object_value(value: object, *, context: str) -> Mapping[str, Any]:
    require(type(value) is dict, f"{context}: expected object")
    return cast(Mapping[str, Any], value)


def exact_keys(
    value: Mapping[str, Any],
    allowed: frozenset[str],
    *,
    context: str,
) -> None:
    unknown = sorted(set(value) - allowed)
    require(not unknown, f"{context}: unknown fields: {','.join(unknown)}")


def string_list(
    value: object,
    *,
    context: str,
    allow_empty: bool = False,
) -> list[str]:
    require(type(value) is list, f"{context}: expected list")
    items = cast(list[object], value)
    require(allow_empty or bool(items), f"{context}: must not be empty")
    require(
        all(type(item) is str and bool(item) for item in items),
        f"{context}: expected non-empty strings",
    )
    strings = cast(list[str], items)
    require(len(strings) == len(set(strings)), f"{context}: duplicate values")
    return strings


def load_json_object(path: Path, *, context: str) -> Mapping[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=reject_duplicate_keys,
        )
    except CoverageManifestError:
        raise
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise CoverageManifestError(f"{context}: failed to load JSON: {exc}") from exc
    return object_value(value, context=context)


def relative_repo_path(value: object, *, context: str) -> Path:
    require(type(value) is str and bool(value), f"{context}: invalid path")
    relative = Path(cast(str, value))
    require(bool(relative.parts), f"{context}: empty path")
    require(
        not relative.is_absolute() and ".." not in relative.parts and "." not in relative.parts,
        f"{context}: non-portable path",
    )
    require(relative.as_posix() == cast(str, value), f"{context}: path is not canonical")
    return relative


def repo_file(repo_root: Path, relative: Path, *, context: str) -> Path:
    root = repo_root.resolve()
    candidate = root
    for part in relative.parts:
        candidate /= part
        require(not candidate.is_symlink(), f"{context}: symbolic links are forbidden")
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise CoverageManifestError(f"{context}: missing file {relative}") from exc
    require(resolved.is_relative_to(root), f"{context}: path escapes repository")
    require(resolved.is_file(), f"{context}: expected regular file {relative}")
    return resolved


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_canonical_json(value: object) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def valid_sha256(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 64
        and all(character in string.hexdigits for character in value)
        and value == value.lower()
    )
