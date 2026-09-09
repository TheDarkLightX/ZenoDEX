"""Bounded reads on a cooperative local filesystem; no workflow decisions."""

from __future__ import annotations

import hashlib
import os
import stat
from pathlib import Path
from typing import Final, NoReturn

from .model import LacunaError


def _raise(code: str) -> NoReturn:
    raise LacunaError(code)


_MAX_SOURCE_BYTES: Final = 12 * 1024 * 1024



def _path_stat(path: Path, missing_code: str) -> os.stat_result:
    try:
        result = os.lstat(path)
    except FileNotFoundError as exc:
        raise LacunaError(missing_code) from exc
    if stat.S_ISLNK(result.st_mode):
        _raise("PATH_SYMLINK")
    return result



def _checked_directory(path: Path, missing_code: str) -> Path:
    absolute = Path(os.path.abspath(os.fspath(path)))
    cursor = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        cursor /= part
        _path_stat(cursor, missing_code)
    if not stat.S_ISDIR(_path_stat(absolute, missing_code).st_mode):
        _raise("INVALID_PATH")
    return absolute



def _read_regular(path: Path, missing_code: str, maximum: int) -> bytes:
    details = _path_stat(path, missing_code)
    if not stat.S_ISREG(details.st_mode) or details.st_size > maximum:
        _raise("CORRUPT_RECORD")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise LacunaError(missing_code) from exc
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode) or opened.st_size > maximum:
            _raise("CORRUPT_RECORD")
        chunks: list[bytes] = []
        remaining = maximum + 1
        while remaining:
            chunk = os.read(descriptor, min(65_536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
        if len(raw) > maximum:
            _raise("CORRUPT_RECORD")
        return raw
    finally:
        os.close(descriptor)



def _source_digest(path: Path) -> str:
    details = _path_stat(path, "SOURCE_MISSING")
    if not stat.S_ISREG(details.st_mode) or details.st_size > _MAX_SOURCE_BYTES:
        _raise("SOURCE_MISSING")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise LacunaError("SOURCE_MISSING") from exc
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode) or opened.st_size > _MAX_SOURCE_BYTES:
            _raise("SOURCE_MISSING")
        digest_value = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(descriptor, 65_536)
            if not chunk:
                break
            total += len(chunk)
            if total > _MAX_SOURCE_BYTES:
                _raise("SOURCE_MISSING")
            digest_value.update(chunk)
        return digest_value.hexdigest()
    finally:
        os.close(descriptor)
