#!/usr/bin/env python3
"""Closed live-gate registry and bounded process boundary for plan tooling.

This module is the only place that decides which commands the whole-program
plan checker may execute. Plan JSON never selects code: it may mirror a
registry entry, and the checker requires exact equality before any execution.

Boundary rules:

- every registry entry binds exact argv (``python3`` plus a repository tool
  path), output format, observation projection, and a bounded timeout;
- child processes receive an explicit minimal environment. ``PATH``,
  ``HOME``, and ``PYTHONPATH`` are never inherited; user site-packages are
  disabled. Gate and supervisor interpreters start with ``-I`` and add the
  descriptor-bound repository root only after interpreter startup, so the
  tracked root ``sitecustomize.py`` cannot widen their import path.
  ``live_gate_preflight_v1`` also refuses when the ignored
  ``external/ESSO`` trigger is present or cannot be proved absent. The
  environment is explicit, not fully hermetic: the interpreter, its standard
  library and site-packages, and transitive imports are not attested;
- output capture is bounded in bytes and time; every child starts its own
  session and the whole process group is killed on timeout or overflow so
  descendants cannot retain the pipes, and a child that completes after its
  deadline is a timeout, never a success. A descendant that leaves the
  process group (``setsid``, double fork) is not reachable by that kill, so
  every gate runs under a dedicated supervisor process: the supervisor makes
  itself a child subreaper (``PR_SET_CHILD_SUBREAPER``), spawns the gate,
  and after the gate finishes finds every reparented descendant through
  ``/proc``, kills it, and reaps it in bounded rounds. The supervisor is a
  fresh process whose only children are the gate and its reparented
  descendants, so ownership is exact: nothing created by the checker
  process or any of its threads can be classified as an escapee. A gate that
  leaked any descendant is refused as an observation; a process that will
  not die within the deadline is a typed error. The sandbox claim is exactly
  this and no more: a committed, hash-bound, trusted checker; a dedicated
  supervisor that prevents cross-run child ownership; ordinary leaked
  descendants reaped under a live supervisor; ``/proc`` enumeration bounded
  in entries and bytes; a deadline checked between system calls (one
  blocking kernel read cannot be preempted). Outside the claim: a gate that
  deliberately kills its supervisor, or double-forks into a new session and
  then loses its supervisor. Then: a direct gate child that has not cleared
  its ``PR_SET_PDEATHSIG`` guard dies with the supervisor (the guard is
  installed fail-closed between fork and exec: a failed ``prctl`` or a
  parent already gone aborts the child before exec as a typed start
  failure), but Linux clears the setting in processes the child forks and a
  hostile child may clear it, so this is no containment; nothing is killed
  by pid (a pid may already belong to an unrelated process group), and the
  run is a typed parent-side failure stating that gate processes and their
  descendants may be orphaned. Closing that case needs a cgroup, a PID
  namespace, or an external sandbox, which this advisory checker does not
  provide;
- directories and files are addressed by descriptor, never by pathname:
  ``AnchoredDirectoryV1`` opens every root-path component with
  ``openat2(RESOLVE_NO_SYMLINKS|RESOLVE_NO_MAGICLINKS)`` and every subtree
  component with ``openat2(RESOLVE_NO_SYMLINKS|RESOLVE_NO_MAGICLINKS|
  RESOLVE_NO_XDEV|RESOLVE_BENEATH)``: symlinks, magic links, any mount
  crossing (same-device bind mounts included, because the kernel compares
  vfsmounts), and ``..`` escapes are refused by the kernel; support is probed
  exactly once and a kernel without it refuses to bind. The descriptor is
  kept for the whole invocation and inherited explicitly by children as
  ``/proc/self/fd/N``; ``AnchoredFileV1`` keeps the mutable source inode for
  drift checks and executes a bounded, write-sealed memfd snapshot captured
  while that inode matched its hash. The checker and supervisor top-level
  bytes therefore cannot change after binding, including a rewrite restored
  before later source/status checks. Mount substitution of an ancestor after
  binding cannot redirect a held descriptor; before binding, the host layout
  is the operator's responsibility and is not attested;
- what an observation attests is exactly the sealed top-level checker and
  supervisor bytes, the registry argv, the explicit environment, the anchored
  working directory, and the committed source snapshot before and after
  execution. The descriptor-bound repository root is inserted only after
  isolated startup; the tracked ambient path hook is never imported. Modules
  the checker imports are still resolved at execution time and are not
  individually sealed or attested: a transitive dependency swapped and
  restored between snapshot checks is not detected. Transitive repository
  code is trusted, not attested;
- git runs from ``/usr/bin/git`` with replacement-object resolution, system,
  and global configuration disabled and a descriptor-bound working directory.
  The git store itself
  is not anchored: git metadata, refs, worktree administrative paths,
  commondir, and the object store are not separately descriptor-bound or
  attested and can be raced by a same-host adversary; in a linked worktree
  the ``.git`` file indirection may point outside the anchored root. Every
  git-derived value (lineage, status, snapshot) is deterministic local
  evidence under a trusted git store, not an adversarially immutable
  repository snapshot;
- gate stdout is decoded through ``tools.bounded_json_v1``.

The module grants no authority. Observations are local execution records.
"""

from __future__ import annotations

import base64
import ctypes
import enum
import errno as errno_module
import fcntl
import hashlib
import json
import os
import re
import selectors
import signal
import stat as stat_module
import subprocess
import sys
import time
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Final

_RUNNING_AS_SUPERVISOR_V1: Final = (
    __name__ == "__main__" and sys.argv[1:] == ["--supervise-v1"]
)
_REPO_ROOT = Path(__file__).resolve().parents[1]
if not __package__ and not _RUNNING_AS_SUPERVISOR_V1 and str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.bounded_json_v1 import (  # noqa: E402
    GATE_OUTPUT_LIMITS_V1,
    BoundedJsonError,
    decode_bounded_json_v1,
)

GIT_BINARY: Final = "/usr/bin/git"
GIT_TIMEOUT_SECONDS: Final = 60
MAX_GIT_OUTPUT_BYTES: Final = 1024 * 1024
MAX_GIT_OBJECT_PROBE_OUTPUT_BYTES: Final = 256
MAX_GATE_OUTPUT_BYTES: Final = GATE_OUTPUT_LIMITS_V1.max_bytes
MAX_LIVE_GATE_TIMEOUT_SECONDS: Final = 900
_READ_CHUNK_BYTES: Final = 65536
_TERMINATE_GRACE_SECONDS: Final = 5
_PR_SET_CHILD_SUBREAPER: Final = 36
_REAP_DEADLINE_SECONDS: Final = 5.0
_REAP_POLL_SECONDS: Final = 0.01
_PROC_ROOT: Final = Path("/proc")
_MAX_PROC_ENTRIES: Final = 4_194_304
_MAX_PROC_RECORD_BYTES: Final = 4096
_MAX_PROC_LIST_BYTES: Final = 1024 * 1024
_SUPERVISOR_OVERHEAD_SECONDS: Final = 10
_SUPERVISOR_REQUEST_LIMIT_BYTES: Final = 65536
PROCESS_ENVIRONMENT_BASE: Final[Mapping[str, str]] = MappingProxyType(
    {
        "PATH": "/usr/bin:/bin",
        "HOME": "/nonexistent",
        "XDG_CONFIG_HOME": "/nonexistent",
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_TERMINAL_PROMPT": "0",
    }
)

_GIT_OID_RE_V1: Final = re.compile(r"[0-9a-f]{40}")


def _closed_git_path_v1(value: str) -> bool:
    """Accept one canonical repository-relative Git path argument."""

    if not value or value.startswith("/") or "\\" in value or "\x00" in value:
        return False
    return all(part not in {"", ".", ".."} for part in value.split("/"))


def _closed_git_arguments_v1(args: Sequence[str]) -> tuple[str, ...] | None:
    """Snapshot only the exact read-only Git forms used by this assurance code.

    Keeping this grammar here prevents caller-supplied global options such as
    ``-C``, ``--git-dir``, ``--work-tree``, and ``-c`` from redirecting the
    descriptor-bound working directory or changing command semantics.
    """

    if type(args) not in (list, tuple) or any(type(arg) is not str for arg in args):
        return None
    argv = tuple(args)
    if argv in {
        ("rev-parse", "HEAD"),
        ("rev-parse", "--show-toplevel"),
        ("branch", "--show-current"),
        ("status", "--porcelain=v2", "--untracked-files=all"),
        (
            "status",
            "--porcelain=v2",
            "-z",
            "--untracked-files=all",
            "--no-renames",
        ),
        ("ls-tree", "-r", "-z", "--full-tree", "HEAD"),
    }:
        return argv
    if (
        len(argv) == 5
        and argv[:4] == ("ls-tree", "-z", "HEAD", "--")
        and _closed_git_path_v1(argv[4])
    ):
        return argv
    if len(argv) == 3 and argv[:2] == ("cat-file", "-e"):
        expression = argv[2]
        oid = expression.removesuffix("^{commit}")
        if expression == f"{oid}^{{commit}}" and _GIT_OID_RE_V1.fullmatch(oid):
            return argv
    if len(argv) == 3 and argv[:2] == ("cat-file", "blob"):
        oid, separator, path = argv[2].partition(":")
        if separator and _GIT_OID_RE_V1.fullmatch(oid) and _closed_git_path_v1(path):
            return argv
    if (
        len(argv) == 3
        and argv[:2] == ("cat-file", "commit")
        and _GIT_OID_RE_V1.fullmatch(argv[2])
    ):
        return argv
    if (
        len(argv) == 4
        and argv[:2] == ("merge-base", "--is-ancestor")
        and _GIT_OID_RE_V1.fullmatch(argv[2])
        and (argv[3] == "HEAD" or _GIT_OID_RE_V1.fullmatch(argv[3]))
    ):
        return argv
    return None


_ANCHOR_FLAGS: Final = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
_ENTRY_FLAGS: Final = os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK
_MAX_HASHED_FILE_BYTES: Final = 64 * 1024 * 1024
_SYS_OPENAT2: Final = 437
RESOLVE_NO_XDEV: Final = 0x01
RESOLVE_NO_MAGICLINKS: Final = 0x02
RESOLVE_NO_SYMLINKS: Final = 0x04
RESOLVE_BENEATH: Final = 0x08
ROOT_PATH_RESOLVE: Final = RESOLVE_NO_SYMLINKS | RESOLVE_NO_MAGICLINKS
SUBTREE_RESOLVE: Final = RESOLVE_NO_SYMLINKS | RESOLVE_NO_MAGICLINKS | RESOLVE_NO_XDEV | RESOLVE_BENEATH
_PR_SET_PDEATHSIG: Final = 1


class AnchorRefused(OSError):
    """A path operation was refused before touching anything: symlink component, mount crossing, closed anchor."""


class AnchoredPathStateV1(enum.Enum):
    """Closed result of resolving one path through an anchored root."""

    ABSENT = "absent"
    PRESENT = "present"
    REFUSED = "refused"


@dataclass(frozen=True, slots=True)
class AnchoredPathProbeV1:
    """Presence result whose refusal cannot be confused with safe absence."""

    state: AnchoredPathStateV1
    reason: str = ""


class _OpenHow(ctypes.Structure):
    _fields_ = (("flags", ctypes.c_uint64), ("mode", ctypes.c_uint64), ("resolve", ctypes.c_uint64))


_LIBC = ctypes.CDLL(None, use_errno=True)
_LIBC.syscall.restype = ctypes.c_long


def _openat2_raw(dirfd: int, name: str, flags: int, mode: int, resolve: int) -> int:
    how = _OpenHow(flags | os.O_CLOEXEC, mode, resolve)
    descriptor = _LIBC.syscall(_SYS_OPENAT2, dirfd, name.encode("utf-8"), ctypes.byref(how), ctypes.sizeof(how))
    if descriptor >= 0:
        return int(descriptor)
    error = ctypes.get_errno()
    raise OSError(error, os.strerror(error), name)


_OPENAT2_SUPPORT: list[str] = []


def openat2_support_v1() -> str:
    """Exact, one-time support probe: ``""`` when the kernel honours every resolve flag this module relies on.

    The probe opens ``/`` itself with the full subtree policy through
    ``openat2``; ``ENOSYS`` (no syscall) or ``EINVAL`` (an unknown resolve
    flag or ``open_how`` layout) means the policy cannot be enforced, and
    every anchor then refuses to bind.
    """

    if not _OPENAT2_SUPPORT:
        root = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            probe = _openat2_raw(root, ".", os.O_RDONLY | os.O_DIRECTORY, 0, SUBTREE_RESOLVE)
            os.close(probe)
            _OPENAT2_SUPPORT.append("")
        except OSError as exc:
            _OPENAT2_SUPPORT.append(f"openat2 with the required resolve flags is unavailable on this kernel ({os.strerror(exc.errno or 0)})")
        finally:
            os.close(root)
    return _OPENAT2_SUPPORT[0]


def _openat2(dirfd: int, name: str, flags: int, mode: int, resolve: int) -> int:
    """``openat2(2)`` of one component relative to ``dirfd`` with kernel-enforced resolution policy.

    ``RESOLVE_NO_SYMLINKS`` refuses any symlink, ``RESOLVE_NO_MAGICLINKS``
    any ``/proc``-style magic link, ``RESOLVE_NO_XDEV`` any mount crossing
    (bind mounts of the same device included, because the kernel compares
    vfsmounts, not device numbers), and ``RESOLVE_BENEATH`` any escape above
    ``dirfd``. Support is probed exactly once; an unsupported kernel is a
    typed refusal, never a fallback.
    """

    unsupported = openat2_support_v1()
    if unsupported:
        raise AnchorRefused(unsupported)
    return _openat2_raw(dirfd, name, flags, mode, resolve)


def _subtree_open(directory: int, name: str, flags: int, mode: int) -> int:
    """One subtree component under the full policy, with symlink and mount refusals typed."""

    try:
        return _openat2(directory, name, flags, mode, SUBTREE_RESOLVE)
    except OSError as exc:
        if exc.errno == errno_module.EXDEV:
            raise AnchorRefused(f"mount boundary crossed at {name!r}") from exc
        if exc.errno == errno_module.ELOOP:
            raise AnchorRefused(f"symlink refused at {name!r}") from exc
        raise


def _die_with_parent(expected_parent: int) -> None:
    """In the gate child between fork and exec: install SIGKILL-on-parent-death fail-closed.

    The guard is established only if ``prctl`` succeeds and the parent is
    still ``expected_parent`` afterwards (a parent that died in the fork-to-
    prctl window has already been replaced, so the child aborts before exec;
    the abort surfaces to the supervisor as a typed start failure). What this
    establishes: a direct gate child that does not clear the setting dies
    with its supervisor. Linux clears the setting in processes the child
    forks and the child may clear it itself, so deliberate hostile behaviour
    stays outside the claim; this is not containment of descendants.
    """

    if _LIBC.prctl(_PR_SET_PDEATHSIG, int(signal.SIGKILL), 0, 0, 0) != 0:
        raise RuntimeError("parent-death guard could not be installed")
    if os.getppid() != expected_parent:
        raise RuntimeError("supervisor died before the parent-death guard was installed")


def _canonical_parts(relative: Sequence[str]) -> tuple[str, ...]:
    parts = tuple(relative)
    if not parts or any(part in {"", ".", ".."} or "/" in part or "\0" in part for part in parts):
        raise AnchorRefused(f"{'/'.join(parts)!r} is not a canonical repository-relative path")
    return parts


class AnchoredDirectoryV1:
    """One persistent descriptor-backed directory capability.

    Exact path policy, enforced by the kernel through ``openat2``:

    - root path (``/`` down to the root): each component is opened with
      ``RESOLVE_NO_SYMLINKS|RESOLVE_NO_MAGICLINKS`` and ``O_DIRECTORY``, so a
      symlink or magic link anywhere in the root path is refused, never
      followed; ancestor components may cross mounts (host layout, not
      attested);
    - subtree (every walk below the root): each component and the final entry
      are opened with ``RESOLVE_NO_SYMLINKS|RESOLVE_NO_MAGICLINKS|
      RESOLVE_NO_XDEV|RESOLVE_BENEATH``, so symlinks, magic links, any mount
      crossing (bind mounts of the same device included), and ``..`` escapes
      are refused;
    - a kernel without ``openat2`` cannot enforce this, so binding is refused.

    Persistence: the descriptor is created only here, is never re-derived from
    a pathname, is held for the whole invocation, and is inherited explicitly
    by every child started against it (``/proc/self/fd/N`` inside the child);
    every stat, read, replacement, and child process addresses this inode, so
    neither a pathname swap nor inode reuse after deletion can redirect work.
    """

    __slots__ = ("_descriptor", "device", "inode")

    def __init__(self, descriptor: int, device: int, inode: int) -> None:
        self._descriptor = descriptor
        self.device = device
        self.inode = inode

    @classmethod
    def open(cls, path: Path) -> AnchoredDirectoryV1:
        absolute = Path(os.path.abspath(path))
        descriptor = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            for name in absolute.parts[1:]:
                try:
                    next_descriptor = _openat2(descriptor, name, os.O_RDONLY | os.O_DIRECTORY, 0, ROOT_PATH_RESOLVE)
                except AnchorRefused:
                    raise
                except OSError as exc:
                    raise AnchorRefused(f"root component {name!r} is not a directory reachable without following a symlink: {type(exc).__name__}") from exc
                os.close(descriptor)
                descriptor = next_descriptor
            info = os.fstat(descriptor)
        except BaseException:
            os.close(descriptor)
            raise
        return cls(descriptor, info.st_dev, info.st_ino)

    @property
    def is_open(self) -> bool:
        return self._descriptor >= 0

    def _require_open(self) -> int:
        if not self.is_open:
            raise AnchorRefused("anchored directory is closed")
        return self._descriptor

    @property
    def child_path(self) -> str:
        """The pathname a child of this process must use to reach the anchored directory."""

        return f"/proc/self/fd/{self._require_open()}"

    def walk(self, parts: Sequence[str]) -> int:
        """Descriptor of the directory holding ``parts[-1]``, every component opened under the subtree policy."""

        canonical = _canonical_parts(parts)
        directory = os.dup(self._require_open())
        try:
            for name in canonical[:-1]:
                next_directory = _subtree_open(directory, name, os.O_RDONLY | os.O_DIRECTORY, 0)
                os.close(directory)
                directory = next_directory
        except BaseException:
            os.close(directory)
            raise
        return directory

    def open_entry(self, parts: Sequence[str], flags: int, mode: int = 0o644) -> int:
        """Open the final entry itself under the subtree policy (never followed, never blocking, never across a mount)."""

        directory = self.walk(parts)
        try:
            entry_flags = flags | os.O_NOFOLLOW | os.O_CLOEXEC | (0 if flags & os.O_PATH else os.O_NONBLOCK)
            creating = bool(flags & (os.O_CREAT | getattr(os, "O_TMPFILE", 0)))
            return _subtree_open(directory, _canonical_parts(parts)[-1], entry_flags, mode if creating else 0)
        finally:
            os.close(directory)

    def stat(self, relative: str) -> os.stat_result:
        """Stat of the entry itself through the anchored descriptor; no component is followed."""

        descriptor = self.open_entry(relative.split("/"), os.O_PATH)
        try:
            return os.fstat(descriptor)
        finally:
            os.close(descriptor)

    def probe(self, relative: str) -> AnchoredPathProbeV1:
        """Resolve ``relative`` without following links; only ``ENOENT`` means absent."""

        try:
            self.stat(relative)
        except FileNotFoundError:
            return AnchoredPathProbeV1(AnchoredPathStateV1.ABSENT)
        except OSError as exc:
            reason = str(exc) if isinstance(exc, AnchorRefused) else f"{type(exc).__name__}: {exc}"
            return AnchoredPathProbeV1(AnchoredPathStateV1.REFUSED, reason)
        return AnchoredPathProbeV1(AnchoredPathStateV1.PRESENT)

    def exists(self, relative: str) -> bool:
        """Compatibility predicate that propagates resolution refusal instead of treating it as absence."""

        probe = self.probe(relative)
        if probe.state is AnchoredPathStateV1.REFUSED:
            raise AnchorRefused(probe.reason)
        return probe.state is AnchoredPathStateV1.PRESENT

    def open_file(self, relative: str) -> AnchoredFileV1:
        """Hold a regular source inode and an immutable sealed copy of its exact bytes."""

        descriptor = self.open_entry(relative.split("/"), os.O_RDONLY)
        sealed: int | None = None
        try:
            before = os.fstat(descriptor)
            if not stat_module.S_ISREG(before.st_mode):
                raise AnchorRefused(f"{relative!r} is not a regular file")
            sealed, digest, size = _seal_descriptor_copy_v1(descriptor)
            after = os.fstat(descriptor)
            stable = (
                before.st_dev,
                before.st_ino,
                before.st_mode,
                before.st_size,
                before.st_mtime_ns,
                before.st_ctime_ns,
            ) == (
                after.st_dev,
                after.st_ino,
                after.st_mode,
                after.st_size,
                after.st_mtime_ns,
                after.st_ctime_ns,
            )
            if not stable or size != before.st_size or _hash_descriptor(descriptor) != digest:
                raise AnchorRefused(f"{relative!r} changed while its executable snapshot was sealed")
        except BaseException:
            try:
                if sealed is not None:
                    os.close(sealed)
            finally:
                os.close(descriptor)
            raise
        return AnchoredFileV1(descriptor, sealed, digest, size)

    def close(self) -> None:
        if self.is_open:
            descriptor, self._descriptor = self._descriptor, -1
            os.close(descriptor)

    def __enter__(self) -> AnchoredDirectoryV1:
        return self

    def __exit__(self, *_exc: object) -> None:
        self.close()


def _hash_descriptor(descriptor: int) -> str:
    """SHA-256 of one descriptor without mutating its shared file offset."""

    digest = hashlib.sha256()
    total = 0
    offset = 0
    while True:
        chunk = os.pread(descriptor, _READ_CHUNK_BYTES, offset)
        if not chunk:
            break
        total += len(chunk)
        if total > _MAX_HASHED_FILE_BYTES:
            raise AnchorRefused(f"file exceeds {_MAX_HASHED_FILE_BYTES} bytes")
        digest.update(chunk)
        offset += len(chunk)
    return digest.hexdigest()


def _seal_descriptor_copy_v1(descriptor: int) -> tuple[int, str, int]:
    """Copy bounded source bytes into a write-sealed memfd and return fd, digest, size."""

    required = (
        "memfd_create",
        "MFD_ALLOW_SEALING",
        "MFD_CLOEXEC",
    )
    if any(not hasattr(os, name) for name in required):
        raise AnchorRefused("sealed executable snapshots are unavailable")
    seal_names = (
        "F_ADD_SEALS",
        "F_GET_SEALS",
        "F_SEAL_GROW",
        "F_SEAL_SEAL",
        "F_SEAL_SHRINK",
        "F_SEAL_WRITE",
    )
    if any(not hasattr(fcntl, name) for name in seal_names):
        raise AnchorRefused("kernel file seals are unavailable")
    sealed = os.memfd_create(
        "zenodex-live-gate-v1",
        os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING,
    )
    try:
        digest = hashlib.sha256()
        total = 0
        offset = 0
        while True:
            chunk = os.pread(descriptor, _READ_CHUNK_BYTES, offset)
            if not chunk:
                break
            total += len(chunk)
            if total > _MAX_HASHED_FILE_BYTES:
                raise AnchorRefused(f"file exceeds {_MAX_HASHED_FILE_BYTES} bytes")
            digest.update(chunk)
            view = memoryview(chunk)
            while view:
                written = os.write(sealed, view)
                if written <= 0:
                    raise AnchorRefused("sealed executable snapshot write made no progress")
                view = view[written:]
            offset += len(chunk)
        os.fchmod(sealed, 0o400)
        seals = (
            fcntl.F_SEAL_GROW
            | fcntl.F_SEAL_SEAL
            | fcntl.F_SEAL_SHRINK
            | fcntl.F_SEAL_WRITE
        )
        fcntl.fcntl(sealed, fcntl.F_ADD_SEALS, seals)
        observed_seals = int(fcntl.fcntl(sealed, fcntl.F_GET_SEALS))
        if observed_seals & seals != seals:
            raise AnchorRefused("sealed executable snapshot is missing required write seals")
        os.lseek(sealed, 0, os.SEEK_SET)
        return sealed, digest.hexdigest(), total
    except BaseException:
        os.close(sealed)
        raise


class AnchoredFileV1:
    """A mutable source inode for drift checks plus an immutable sealed executable snapshot.

    ``child_path`` always names the write-sealed memfd copy captured while the
    source matched ``sha256``. The original inode remains open only so
    :meth:`rehash` can detect persistent drift. A transient source rewrite can
    therefore never alter executed bytes even when it is restored before the
    post-check. Created only by :meth:`AnchoredDirectoryV1.open_file`.
    """

    __slots__ = ("_descriptor", "_sealed_descriptor", "sha256", "size")

    def __init__(self, descriptor: int, sealed_descriptor: int, sha256: str, size: int) -> None:
        self._descriptor = descriptor
        self._sealed_descriptor = sealed_descriptor
        self.sha256 = sha256
        self.size = size

    @property
    def is_open(self) -> bool:
        return self._descriptor >= 0 and self._sealed_descriptor >= 0

    @property
    def child_path(self) -> str:
        if not self.is_open:
            raise AnchorRefused("anchored file is closed")
        return f"/proc/self/fd/{self._sealed_descriptor}"

    def rehash(self) -> str:
        if not self.is_open:
            raise AnchorRefused("anchored file is closed")
        return _hash_descriptor(self._descriptor)

    def read(self, max_bytes: int) -> bytes | None:
        """Whole content without mutating the shared offset, or ``None`` above the bound."""

        if not self.is_open:
            raise AnchorRefused("anchored file is closed")
        chunks: list[bytes] = []
        remaining = max_bytes + 1
        offset = 0
        while remaining > 0:
            chunk = os.pread(
                self._sealed_descriptor,
                min(remaining, _READ_CHUNK_BYTES),
                offset,
            )
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
            offset += len(chunk)
        data = b"".join(chunks)
        return data if len(data) <= max_bytes else None

    def close(self) -> None:
        descriptor, self._descriptor = self._descriptor, -1
        sealed, self._sealed_descriptor = self._sealed_descriptor, -1
        try:
            if descriptor >= 0:
                os.close(descriptor)
        finally:
            if sealed >= 0:
                os.close(sealed)

    def __enter__(self) -> AnchoredFileV1:
        return self

    def __exit__(self, *_exc: object) -> None:
        self.close()


SUPERVISOR_MODULE_PATH_V1: Final = "tools/live_gate_registry_v1.py"


@dataclass(frozen=True, slots=True)
class SupervisorCodeV1:
    """Held supervisor source and the exact anchored root from which it was opened."""

    root: AnchoredDirectoryV1
    source: AnchoredFileV1
    sha256: str

    @property
    def is_open(self) -> bool:
        return self.root.is_open and self.source.is_open

    def close(self) -> None:
        self.source.close()


def _open_supervisor_code_v1(
    root: AnchoredDirectoryV1, *, expected_sha256: str | None
) -> SupervisorCodeV1:
    if not root.is_open:
        raise AnchorRefused("supervisor root is closed")
    source = root.open_file(SUPERVISOR_MODULE_PATH_V1)
    if expected_sha256 is not None and source.sha256 != expected_sha256:
        observed = source.sha256
        source.close()
        raise AnchorRefused(
            f"supervisor source hash differs from the loaded registry: expected={expected_sha256} observed={observed}"
        )
    return SupervisorCodeV1(root, source, source.sha256)


# Bind the source that defined this process eagerly at import time. This closes
# the old first-use pathname window; gate execution below still derives a fresh
# held source from the gate's own already-bound root and requires this hash.
_DEFAULT_SUPERVISOR_ROOT: AnchoredDirectoryV1 | None
_DEFAULT_SUPERVISOR_CODE: SupervisorCodeV1 | None
TRUSTED_SUPERVISOR_SHA256_V1: str
if _RUNNING_AS_SUPERVISOR_V1:
    _DEFAULT_SUPERVISOR_ROOT = None
    _DEFAULT_SUPERVISOR_CODE = None
    TRUSTED_SUPERVISOR_SHA256_V1 = ""
else:
    _DEFAULT_SUPERVISOR_ROOT = AnchoredDirectoryV1.open(_REPO_ROOT)
    _DEFAULT_SUPERVISOR_CODE = _open_supervisor_code_v1(
        _DEFAULT_SUPERVISOR_ROOT, expected_sha256=None
    )
    TRUSTED_SUPERVISOR_SHA256_V1 = _DEFAULT_SUPERVISOR_CODE.sha256


def bind_supervisor_code_v1(root: AnchoredDirectoryV1) -> SupervisorCodeV1:
    """Hold the trusted supervisor from ``root`` or refuse a different byte identity."""

    return _open_supervisor_code_v1(
        root, expected_sha256=TRUSTED_SUPERVISOR_SHA256_V1
    )


WorkingDirectory = Path | AnchoredDirectoryV1


@dataclass(frozen=True, slots=True)
class ProcessBoundsV1:
    """Deadline and output ceiling for one bounded child process."""

    timeout_seconds: int
    max_output_bytes: int


@dataclass(frozen=True, slots=True)
class ProcessRunV1:
    """Bounded child-process outcome; ``error`` is empty when the run completed.

    ``escaped_descendants`` counts live processes that outlived the child's
    process group, were reparented to the supervisor, and were killed.
    """

    exit_code: int
    stdout: bytes
    error: str
    escaped_descendants: int = 0
    stderr: bytes = b""


class GitObjectPresenceV1(enum.Enum):
    """Closed semantic result of probing one exact commit object."""

    PRESENT = "present"
    ABSENT = "absent"
    QUERY_FAILED = "query_failed"


@dataclass(frozen=True, slots=True)
class GitObjectProbeV1:
    """Typed object-presence observation; process failure is never absence."""

    state: GitObjectPresenceV1
    reason: str = ""


@dataclass(frozen=True, slots=True)
class LiveGateSpecV1:
    """One closed registry entry; the only source of executable gate argv."""

    gate_id: str
    argv: tuple[str, ...]
    checker_path: str
    output_format: str
    observed_projection: tuple[str, ...]
    timeout_seconds: int


RegistryRow = tuple[str, tuple[str, ...], str, tuple[str, ...], int]


def _build_registry(rows: Sequence[RegistryRow]) -> Mapping[str, LiveGateSpecV1]:
    registry: dict[str, LiveGateSpecV1] = {}
    for gate_id, argv, output_format, projection, timeout_seconds in rows:
        malformed = (
            gate_id in registry
            or len(argv) < 2
            or argv[0] != "python3"
            or not argv[1].startswith("tools/")
            or not argv[1].endswith(".py")
            or output_format not in {"json", "text"}
            or (output_format == "text" and bool(projection))
            or not 1 <= timeout_seconds <= MAX_LIVE_GATE_TIMEOUT_SECONDS
        )
        if malformed:
            raise ValueError(f"malformed live gate registry row: {gate_id}")
        registry[gate_id] = LiveGateSpecV1(gate_id, argv, argv[1], output_format, projection, timeout_seconds)
    if list(registry) != sorted(registry):
        raise ValueError("live gate registry must be sorted by gate id")
    return MappingProxyType(registry)


LIVE_GATE_REGISTRY: Final[Mapping[str, LiveGateSpecV1]] = _build_registry(
    (
        (
            "m6_asset_precision_policy",
            ("python3", "tools/check_m6_asset_precision_policy_v1.py"),
            "json",
            ("ok", "decimal_places", "atoms_per_display_unit", "policy_root"),
            300,
        ),
        (
            "m6_atdd_contract",
            ("python3", "tools/check_m6_global_economic_core_atdd_v1.py"),
            "json",
            ("contract_status", "errors#len"),
            300,
        ),
        (
            "m6_capability_manifest",
            ("python3", "tools/check_m6_capability_manifest_v1.py"),
            "json",
            ("ok", "lane_count", "open_capability_count", "manifest_complete", "release_eligible", "production_authority", "manifest_root"),
            300,
        ),
        (
            "m6_luna_completeness_review",
            ("python3", "tools/check_m6_global_economic_core_luna_review_v1.py"),
            "json",
            ("errors#len",),
            300,
        ),
        (
            "m6_research_boundary",
            ("python3", "tools/check_m6_research_boundary.py", "--json"),
            "json",
            ("ok", "checked_file_count", "findings[].path", "findings[].rule_id", "m6_production_mounted"),
            300,
        ),
        (
            "m6_risc0_semantic_surface",
            ("python3", "tools/check_m6_risc0_semantic_surface_v1.py"),
            "json",
            ("status", "ok", "activation_eligible", "canonical_state_codec_match", "errors#len", "risc0_guest_transition_reachable"),
            300,
        ),
        (
            "m6_value_sinks",
            ("python3", "tools/check_m6_value_sinks_v1.py", "--json"),
            "json",
            ("ok", "classified_identity_count", "observed_occurrence_count", "release_gaps#len", "release_ready"),
            300,
        ),
        (
            "m6_writer_inventory",
            ("python3", "tools/check_m6_writer_inventory.py", "--json"),
            "json",
            ("ok", "coverage_row_count", "open_coverage_count", "unmounted_entrypoint_count", "release_gate_status", "release_ready", "findings#len"),
            300,
        ),
        (
            "permissionless_assurance_status",
            ("python3", "tools/permissionless_assurance.py", "status"),
            "text",
            (),
            600,
        ),
        (
            "production_boundary",
            ("python3", "tools/check_production_boundary.py", "--json"),
            "json",
            ("ok", "checks[].check_id", "checks[].ok"),
            600,
        ),
        (
            "value_movement_closure_status",
            ("python3", "tools/check_value_movement_closure_status_v1.py"),
            "json",
            ("ok", "subject_commit", "gate_count", "production_authority", "findings#len"),
            300,
        ),
    )
)


AMBIENT_PATH_HOOK_DIRECTORIES: Final[tuple[str, ...]] = ("external/ESSO",)


def live_gate_preflight_v1(root: WorkingDirectory) -> list[str]:
    """Refuse gate execution while a tracked path hook could widen the child search path.

    The repository-root ``sitecustomize.py`` inserts ``external/ESSO`` (an
    ignored directory) at the front of ``sys.path`` whenever it exists.
    ``PYTHONPATH`` equal to the root makes that hook run in every child, so its
    trigger directory must be absent before any gate executes. With an anchored
    root the check is a ``dir_fd`` stat on the anchored inode.
    """

    owned: AnchoredDirectoryV1 | None = None
    try:
        if isinstance(root, AnchoredDirectoryV1):
            anchored = root
        else:
            try:
                owned = anchored = AnchoredDirectoryV1.open(Path(root))
            except OSError as exc:
                return [f"live gate preflight: root could not be anchored: {type(exc).__name__}: {exc}"]
        errors: list[str] = []
        for relative in AMBIENT_PATH_HOOK_DIRECTORIES:
            probe = anchored.probe(relative)
            if probe.state is AnchoredPathStateV1.PRESENT:
                errors.append(
                    f"live gate preflight: {relative} is present under the root and the tracked "
                    "sitecustomize.py would insert it into child sys.path"
                )
            elif probe.state is AnchoredPathStateV1.REFUSED:
                errors.append(
                    f"live gate preflight: {relative} could not be proved absent under the anchored root: "
                    f"{probe.reason}"
                )
        return errors
    finally:
        if owned is not None:
            owned.close()


def gate_environment_v1(root: WorkingDirectory) -> dict[str, str]:
    """Explicit child environment: PYTHONPATH is exactly the root; nothing is inherited.

    For an anchored root the entry is the child's ``/proc/self/fd/N`` view of
    the anchored inode, so the search path cannot be redirected by a pathname
    swap either.
    """

    python_path = root.child_path if isinstance(root, AnchoredDirectoryV1) else str(root.resolve())
    return {
        **PROCESS_ENVIRONMENT_BASE,
        "PYTHONPATH": python_path,
        "PYTHONNOUSERSITE": "1",
        "PYTHONHASHSEED": "0",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONIOENCODING": "utf-8",
    }


def _kill_process_group(process: subprocess.Popen[bytes]) -> None:
    """Kill the child's whole session so descendants cannot keep pipes open."""

    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    except PermissionError:
        process.kill()


def enable_child_subreaper_v1() -> str:
    """Make this process the reaper of every orphaned descendant; returns ``""`` or the refusal."""

    try:
        libc = ctypes.CDLL(None, use_errno=True)
        result = libc.prctl(_PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0)
    except (OSError, AttributeError) as exc:
        return f"descendant containment unavailable: {type(exc).__name__}"
    return "" if result == 0 else f"descendant containment unavailable: prctl errno {ctypes.get_errno()}"


@dataclass(frozen=True, slots=True)
class ChildScanV1:
    """Children of one process as ``{pid: state}``; ``error`` is nonempty when enumeration itself failed."""

    children: Mapping[int, str]
    error: str


def _read_proc_record(path: Path, max_bytes: int) -> bytes | None:
    """Bytes of one ``/proc`` record, or ``None`` when unreadable or larger than ``max_bytes``."""

    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError:
        return None
    try:
        chunks: list[bytes] = []
        remaining = max_bytes + 1
        while remaining > 0:
            chunk = os.read(descriptor, remaining)
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
    except OSError:
        return None
    finally:
        os.close(descriptor)
    data = b"".join(chunks)
    return data if len(data) <= max_bytes else None


def _stat_fields(pid: int) -> list[bytes] | None:
    """Fields after the command name in ``/proc/<pid>/stat`` (state first), or ``None`` when unreadable or oversized."""

    record = _read_proc_record(_PROC_ROOT / str(pid) / "stat", _MAX_PROC_RECORD_BYTES)
    if record is None:
        return None
    fields = record.rsplit(b")", 1)[-1].split()
    return fields if len(fields) >= 2 and fields[1].isdigit() else None


def _listed_children(parent_pid: int) -> list[int] | None:
    """Child pids from the kernel's per-task ``children`` file, or ``None`` when absent, oversized, or malformed."""

    record = _read_proc_record(_PROC_ROOT / str(parent_pid) / "task" / str(parent_pid) / "children", _MAX_PROC_LIST_BYTES)
    if record is None:
        return None
    listed = record.split()
    return [int(item) for item in listed] if all(item.isdigit() for item in listed) else None


def _numeric_proc_entries() -> Iterator[str]:
    """Numeric ``/proc`` entry names, streamed one at a time so the consumer can stop at its ceiling."""

    with os.scandir(_PROC_ROOT) as iterator:
        for entry in iterator:
            if entry.name.isdigit():
                yield entry.name


def _scanned_candidates(parent_pid: int) -> tuple[list[int], str]:
    """Every ``/proc`` pid whose record names ``parent_pid`` plus every unreadable pid that ``waitpid`` proves ours.

    The listing is consumed incrementally and refused on the entry after
    ``_MAX_PROC_ENTRIES`` before more than the ceiling is retained; each
    record is bounded by ``_MAX_PROC_RECORD_BYTES``. A listing beyond the
    ceiling is an enumeration error, never a partial result.
    """

    if _stat_fields(parent_pid) is None:
        return [], f"/proc record for pid {parent_pid} is unreadable or malformed"
    entries: list[int] = []
    try:
        for name in _numeric_proc_entries():
            if len(entries) >= _MAX_PROC_ENTRIES:
                return [], f"/proc enumeration exceeded the {_MAX_PROC_ENTRIES} entry ceiling"
            entries.append(int(name))
    except OSError as exc:
        return [], f"/proc enumeration failed: {type(exc).__name__}"
    if not entries:
        return [], "/proc enumeration returned no process entries"
    candidates: list[int] = []
    for pid in entries:
        fields = _stat_fields(pid)
        if (fields is None and pid != parent_pid and _is_live_child(pid)) or (fields is not None and int(fields[1]) == parent_pid):
            candidates.append(pid)
    return candidates, ""


def _scan_children(parent_pid: int) -> ChildScanV1:
    """Enumerate the current children of ``parent_pid`` with a typed failure.

    The kernel's per-task ``children`` list is used when it exists and parses
    cleanly; otherwise every ``/proc`` entry is scanned. On both paths a pid
    whose record cannot be read is decided by parentage (``waitpid`` with
    ``WNOHANG``) and reported as a live child with state ``?`` rather than
    dropped. An unreadable ``/proc``, a listing without a single numeric
    entry, or an unreadable record for ``parent_pid`` itself is an
    enumeration error, never an empty result.
    """

    candidates = _listed_children(parent_pid)
    if candidates is None:
        candidates, error = _scanned_candidates(parent_pid)
        if error:
            return ChildScanV1({}, error)
    children: dict[int, str] = {}
    for pid in candidates:
        fields = _stat_fields(pid)
        if fields is not None:
            children[pid] = fields[0].decode("ascii", errors="replace")
        elif _is_live_child(pid):
            children[pid] = "?"
    return ChildScanV1(children, "")


def _is_live_child(pid: int) -> bool:
    """Whether ``pid`` is a still-running child of this process, decided by parentage, not by ``/proc``.

    A child whose ``/proc`` record cannot be read must not disappear from
    containment: ``waitpid`` with ``WNOHANG`` raises for a non-child, returns
    ``(0, 0)`` for a live child, and reaps a child that already exited.
    """

    try:
        return os.waitpid(pid, os.WNOHANG) == (0, 0)
    except ChildProcessError:
        return False


def _reap_once(found: Mapping[int, str]) -> int:
    """Kill every live process in ``found`` and reap without blocking; returns the live count killed."""

    killed = 0
    for pid, state in found.items():
        if state not in {"Z", "X"}:
            killed += 1
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        try:
            os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            pass
    return killed


def reap_escaped_descendants_v1(baseline: frozenset[int], *, deadline_seconds: float = _REAP_DEADLINE_SECONDS) -> tuple[int, str]:
    """Kill and reap every new child of this process; returns ``(killed_live_count, error)``.

    With the subreaper flag set, any descendant that outlived its parent has
    been reparented to this process, so it appears as a direct child that was
    not in ``baseline``. Zombies are reaped silently; live processes are
    killed and counted. Reaping never blocks (``WNOHANG``) and the loop is
    bounded by a monotonic deadline that is checked after every enumeration
    and before any success is reported, so a process that will not die (for
    example in uninterruptible sleep), an enumeration failure, or an
    enumeration that itself outran the deadline is a typed error rather than
    a hang or a silent pass. Residual: the deadline is checked between system
    calls; one blocking kernel read cannot be preempted, so an overrun is
    bounded by the duration of a single call.
    """

    own_pid = os.getpid()
    deadline = time.monotonic() + deadline_seconds
    killed_pids: set[int] = set()
    while True:
        scan = _scan_children(own_pid)
        overdue = time.monotonic() >= deadline
        if scan.error:
            return len(killed_pids), f"descendant containment unverifiable: {scan.error}"
        found = {pid: state for pid, state in scan.children.items() if pid not in baseline}
        if not found:
            if overdue:
                return len(killed_pids), f"descendant containment unverifiable: enumeration exceeded the {deadline_seconds} s deadline"
            return len(killed_pids), ""
        killed_pids.update(pid for pid, state in found.items() if state not in {"Z", "X"})
        _reap_once(found)
        if overdue:
            return len(killed_pids), f"descendant containment incomplete: {len(found)} child process(es) unresolved after {deadline_seconds} s"
        time.sleep(_REAP_POLL_SECONDS)


def _drain_pipes(process: subprocess.Popen[bytes], captured: dict[int, bytearray], *, deadline: float, max_output_bytes: int) -> str:
    total = 0
    with selectors.DefaultSelector() as selector:
        for stream in (process.stdout, process.stderr):
            if stream is not None:
                selector.register(stream, selectors.EVENT_READ)
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return "process exceeded the timeout"
            for key, _events in selector.select(timeout=remaining):
                chunk = os.read(key.fd, _READ_CHUNK_BYTES)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                total += len(chunk)
                if total > max_output_bytes:
                    return "process output exceeds the bound"
                captured[key.fd].extend(chunk)
    return ""


def _finish_process(process: subprocess.Popen[bytes], *, deadline: float, error: str) -> str:
    """Wait for completion strictly within the deadline; a child that completes late is a timeout, never a success."""

    if not error:
        try:
            process.wait(timeout=max(deadline - time.monotonic(), 0))
        except subprocess.TimeoutExpired:
            error = "process exceeded the timeout"
        else:
            if time.monotonic() > deadline:
                error = "process exceeded the timeout"
    if error:
        _kill_process_group(process)
        try:
            process.wait(timeout=_TERMINATE_GRACE_SECONDS)
        except subprocess.TimeoutExpired:
            error = f"{error}; process did not terminate"
    for stream in (process.stdout, process.stderr):
        if stream is not None:
            stream.close()
    return error


def _run_plain_process(
    argv: Sequence[str],
    *,
    cwd: str,
    env: Mapping[str, str],
    bounds: ProcessBoundsV1,
    pass_fds: Sequence[int] = (),
    stdin_data: bytes | None = None,
    gate_child: bool = False,
) -> ProcessRunV1:
    """One bounded child in its own session (drain, deadline with no grace, process-group kill); no reaping.

    Used for trusted git and for driving the supervisor; gate children run
    only inside the supervisor process (``gate_child=True`` there: the direct
    child installs ``PR_SET_PDEATHSIG`` fail-closed before exec; Linux clears
    it in processes the child forks). After supervisor loss nothing is killed
    by pid, because a pid may already belong to an unrelated process group.
    """

    parent = os.getpid()

    def guard() -> None:
        _die_with_parent(parent)

    try:
        process = subprocess.Popen(
            list(argv),
            cwd=cwd,
            env=dict(env),
            stdin=subprocess.PIPE if stdin_data is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
            pass_fds=tuple(pass_fds),
            preexec_fn=guard if gate_child else None,
        )
    except OSError as exc:
        return ProcessRunV1(-1, b"", f"process could not start: {type(exc).__name__}")
    except subprocess.SubprocessError as exc:
        return ProcessRunV1(-1, b"", f"process could not start: parent-death guard aborted the child before exec ({exc})")
    if process.stdout is None or process.stderr is None:
        return ProcessRunV1(-1, b"", _finish_process(process, deadline=0.0, error="process pipes unavailable"))
    if process.stdin is not None:
        try:
            process.stdin.write(stdin_data or b"")
            process.stdin.close()
        except OSError:
            return ProcessRunV1(-1, b"", _finish_process(process, deadline=0.0, error="process refused its request"))
    deadline = time.monotonic() + bounds.timeout_seconds
    stdout_fd, stderr_fd = process.stdout.fileno(), process.stderr.fileno()
    captured = {stdout_fd: bytearray(), stderr_fd: bytearray()}
    error = _drain_pipes(process, captured, deadline=deadline, max_output_bytes=bounds.max_output_bytes)
    error = _finish_process(process, deadline=deadline, error=error)
    if error:
        return ProcessRunV1(-1, b"", error, 0, bytes(captured[stderr_fd]))
    exit_code = process.returncode if process.returncode is not None else -1
    return ProcessRunV1(exit_code, bytes(captured[stdout_fd]), "", 0, bytes(captured[stderr_fd]))


def _run_contained_process(argv: Sequence[str], *, cwd: str, env: Mapping[str, str], bounds: ProcessBoundsV1, pass_fds: Sequence[int]) -> ProcessRunV1:
    """Inside the supervisor process: become the reaper of every descendant, run the child, kill and count escapees.

    The supervisor is a fresh process whose only children are this child and
    whatever gets reparented from it, so ownership is exact: nothing created
    by any other process or thread can be classified as an escaped descendant.
    """

    containment = enable_child_subreaper_v1()
    if containment:
        return ProcessRunV1(-1, b"", containment)
    baseline_scan = _scan_children(os.getpid())
    if baseline_scan.error:
        return ProcessRunV1(-1, b"", f"descendant containment unavailable: {baseline_scan.error}")
    baseline = frozenset(baseline_scan.children)
    run = _run_plain_process(argv, cwd=cwd, env=env, bounds=bounds, pass_fds=pass_fds, gate_child=True)
    escaped, reap_error = reap_escaped_descendants_v1(baseline)
    error = run.error or reap_error
    if error:
        return ProcessRunV1(-1, b"", error, escaped)
    return ProcessRunV1(run.exit_code, run.stdout, "", escaped)


_SUPERVISOR_LOST: Final = "gate processes and their descendants may be orphaned; nothing is killed by pid after supervisor loss"


def supervise_main() -> None:
    """Entry point of the dedicated supervisor process: one request on stdin, one response on stdout."""

    request = json.loads(sys.stdin.buffer.read(_SUPERVISOR_REQUEST_LIMIT_BYTES + 1))
    argv = [str(item) for item in request["argv"]]
    cwd_fd = int(request["cwd_fd"])
    inherited = [int(item) for item in request["pass_fds"]]
    run = _run_contained_process(
        argv,
        cwd=f"/proc/self/fd/{cwd_fd}",
        env={str(key): str(value) for key, value in request["env"].items()},
        bounds=ProcessBoundsV1(int(request["timeout_seconds"]), int(request["max_output_bytes"])),
        pass_fds=[cwd_fd, *inherited],
    )
    response = {
        "error": run.error,
        "escaped_descendants": run.escaped_descendants,
        "exit_code": run.exit_code,
        "stdout_b64": base64.b64encode(run.stdout).decode("ascii"),
    }
    sys.stdout.buffer.write(json.dumps(response, sort_keys=True).encode("utf-8"))
    sys.stdout.buffer.flush()
    os._exit(0)


_SUPERVISOR_ENVIRONMENT: Final[Mapping[str, str]] = MappingProxyType(
    {
        **PROCESS_ENVIRONMENT_BASE,
        "PYTHONNOUSERSITE": "1",
        "PYTHONHASHSEED": "0",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONIOENCODING": "utf-8",
    }
)


def _decode_supervisor_response(payload: bytes) -> ProcessRunV1:
    try:
        response = json.loads(payload)
        error = str(response["error"])
        escaped = int(response["escaped_descendants"])
        exit_code = int(response["exit_code"])
        stdout = base64.b64decode(str(response["stdout_b64"]), validate=True)
    except (ValueError, KeyError, TypeError) as exc:
        return ProcessRunV1(-1, b"", f"supervisor response malformed: {type(exc).__name__}")
    return ProcessRunV1(exit_code, stdout, error, escaped)


def run_bounded_process_v1(
    argv: Sequence[str],
    *,
    cwd: WorkingDirectory,
    env: Mapping[str, str],
    bounds: ProcessBoundsV1,
    inherit: Sequence[AnchoredFileV1] = (),
    supervisor: SupervisorCodeV1 | None = None,
) -> ProcessRunV1:
    """Run ``argv`` under a dedicated supervisor process with bounded output, a strict deadline, and descendant reaping.

    ``cwd`` may be an :class:`AnchoredDirectoryV1`; the child then inherits
    exactly that descriptor and starts in ``/proc/self/fd/N``, so its working
    directory is the anchored inode whatever the pathname names by then, and
    every :class:`AnchoredFileV1` in ``inherit`` is available to it under the
    same descriptor numbers. Ownership contract: the supervisor is a fresh
    process that owns only this child and its reparented descendants, so
    nothing else in the calling process (other threads' children included)
    can ever be killed or reaped by containment. The calling process bounds
    the supervisor itself; if the supervisor outruns that bound it is killed
    and the run is a typed error (gate processes may then be orphaned, which
    is reported, never hidden).
    """

    owned = None
    try:
        if isinstance(cwd, AnchoredDirectoryV1):
            anchored = cwd
        else:
            owned = anchored = AnchoredDirectoryV1.open(Path(cwd))
        if not anchored.is_open or any(not item.is_open for item in inherit):
            return ProcessRunV1(-1, b"", "process could not start: anchored directory or file is closed")
        code = supervisor if supervisor is not None else _DEFAULT_SUPERVISOR_CODE
        if code is None or not code.is_open:
            return ProcessRunV1(-1, b"", "process could not start: supervisor code is closed")
        if supervisor is not None and code.root is not anchored:
            return ProcessRunV1(-1, b"", "process could not start: supervisor code is not owned by the working root")
        if code.source.rehash() != code.sha256 or code.sha256 != TRUSTED_SUPERVISOR_SHA256_V1:
            return ProcessRunV1(-1, b"", "process could not start: supervisor source hash drift")
        request = {
            "argv": list(argv),
            "cwd_fd": anchored._descriptor,
            "env": dict(env),
            "max_output_bytes": bounds.max_output_bytes,
            "pass_fds": [item._sealed_descriptor for item in inherit],
            "timeout_seconds": bounds.timeout_seconds,
        }
        payload = json.dumps(request, sort_keys=True).encode("utf-8")
        if len(payload) > _SUPERVISOR_REQUEST_LIMIT_BYTES:
            return ProcessRunV1(-1, b"", "process could not start: supervisor request exceeds its bound")
        bootstrap = _sealed_python_bootstrap_v1(
            code.source,
            code.root,
            SUPERVISOR_MODULE_PATH_V1,
            ("--supervise-v1",),
        )
        outer = ProcessBoundsV1(
            bounds.timeout_seconds + int(_REAP_DEADLINE_SECONDS) + _TERMINATE_GRACE_SECONDS + _SUPERVISOR_OVERHEAD_SECONDS,
            bounds.max_output_bytes * 2 + 65536,
        )
        run = _run_plain_process(
            [sys.executable, "-I", "-c", bootstrap],
            cwd=anchored.child_path,
            env=_SUPERVISOR_ENVIRONMENT,
            bounds=outer,
            pass_fds=tuple(
                dict.fromkeys(
                    (
                        anchored._descriptor,
                        code.root._descriptor,
                        code.source._sealed_descriptor,
                        *(item._sealed_descriptor for item in inherit),
                    )
                )
            ),
            stdin_data=payload,
        )
        if code.source.rehash() != code.sha256:
            return ProcessRunV1(-1, b"", "supervisor source changed in place during execution")
    except OSError as exc:
        return ProcessRunV1(-1, b"", f"process could not start: {type(exc).__name__}: {exc}")
    finally:
        if owned is not None:
            owned.close()
    if run.error:
        return ProcessRunV1(-1, b"", f"supervisor {run.error}; {_SUPERVISOR_LOST}")
    if run.exit_code != 0:
        return ProcessRunV1(-1, b"", f"supervisor lost (exit {run.exit_code}); {_SUPERVISOR_LOST}")
    return _decode_supervisor_response(run.stdout)


def _git_run(root: WorkingDirectory, args: Sequence[str], max_output_bytes: int) -> ProcessRunV1:
    """Trusted read-only Git in its own session under a closed command grammar."""

    closed_args = _closed_git_arguments_v1(args)
    if closed_args is None:
        return ProcessRunV1(
            -1,
            b"",
            "process could not start: git arguments are outside the closed read-only grammar",
        )
    inherited: tuple[int, ...] = ()
    if isinstance(root, AnchoredDirectoryV1):
        if not root.is_open:
            return ProcessRunV1(-1, b"", "process could not start: anchored directory is closed")
        cwd, inherited = root.child_path, (root._descriptor,)
    else:
        cwd = str(root)
    return _run_plain_process(
        (GIT_BINARY, "--no-replace-objects", *closed_args),
        cwd=cwd,
        env=PROCESS_ENVIRONMENT_BASE,
        bounds=ProcessBoundsV1(GIT_TIMEOUT_SECONDS, max_output_bytes),
        pass_fds=inherited,
    )


def git_commit_object_probe_v1(root: WorkingDirectory, oid: str) -> GitObjectProbeV1:
    """Probe one exact commit through Git's explicit batch ``missing`` result.

    ``cat-file -e`` uses the same nonzero exit family for ordinary absence and
    fatal repository failures.  Batch-check instead reports absence in a
    successful, exact stdout record.  Every process error, nonzero exit,
    stderr byte, or noncanonical response is ``QUERY_FAILED``.
    """

    if type(oid) is not str or _GIT_OID_RE_V1.fullmatch(oid) is None:
        return GitObjectProbeV1(
            GitObjectPresenceV1.QUERY_FAILED, "commit id is not one exact 40-hex oid"
        )
    inherited: tuple[int, ...] = ()
    if isinstance(root, AnchoredDirectoryV1):
        if not root.is_open:
            return GitObjectProbeV1(
                GitObjectPresenceV1.QUERY_FAILED, "anchored directory is closed"
            )
        cwd, inherited = root.child_path, (root._descriptor,)
    else:
        cwd = str(root)
    run = _run_plain_process(
        (
            GIT_BINARY,
            "--no-replace-objects",
            "cat-file",
            "--batch-check=%(objectname) %(objecttype)",
        ),
        cwd=cwd,
        env=PROCESS_ENVIRONMENT_BASE,
        bounds=ProcessBoundsV1(
            GIT_TIMEOUT_SECONDS, MAX_GIT_OBJECT_PROBE_OUTPUT_BYTES
        ),
        pass_fds=inherited,
        stdin_data=f"{oid}\n".encode("ascii"),
    )
    if run.error:
        return GitObjectProbeV1(GitObjectPresenceV1.QUERY_FAILED, run.error)
    if run.exit_code != 0:
        return GitObjectProbeV1(
            GitObjectPresenceV1.QUERY_FAILED,
            f"git object probe exited {run.exit_code}",
        )
    if run.stderr:
        return GitObjectProbeV1(
            GitObjectPresenceV1.QUERY_FAILED, "git object probe wrote stderr"
        )
    if run.stdout == f"{oid} commit\n".encode("ascii"):
        return GitObjectProbeV1(GitObjectPresenceV1.PRESENT)
    if run.stdout == f"{oid} missing\n".encode("ascii"):
        return GitObjectProbeV1(GitObjectPresenceV1.ABSENT)
    return GitObjectProbeV1(
        GitObjectPresenceV1.QUERY_FAILED,
        "git object probe returned a noncanonical response",
    )


def git_bytes_v1(root: WorkingDirectory, args: Sequence[str], *, max_output_bytes: int) -> bytes | None:
    """Run trusted git with a minimal environment; ``None`` on failure or any bound breach."""

    run = _git_run(root, args, max_output_bytes)
    if run.error or run.exit_code != 0:
        return None
    return run.stdout


def git_v1(root: WorkingDirectory, args: Sequence[str]) -> tuple[int, str]:
    """Run trusted git with a minimal environment; ``(-1, "")`` on any bound failure."""

    run = _git_run(root, args, MAX_GIT_OUTPUT_BYTES)
    if run.error:
        return -1, ""
    return run.exit_code, run.stdout.decode("utf-8", errors="replace").strip()


def project_observed_value_v1(value: object, key: str) -> object:
    """Project one observation key out of a live-gate JSON output.

    Key grammar: dotted field path; a segment ending in ``[]`` maps the rest of
    the path over a list; a final ``name#len`` segment yields the length of the
    list stored under ``name``.
    """

    return _project(value, key.split("."), key)


def _project(value: object, segments: Sequence[str], key: str) -> object:
    if not segments:
        return value
    head, rest = segments[0], segments[1:]
    if head.endswith("#len"):
        name = head[: -len("#len")]
        target = value if not name else _field(value, name, key)
        if not isinstance(target, list) or rest:
            raise ValueError(f"projection {key}: #len requires a terminal list")
        return len(target)
    if head.endswith("[]"):
        items = _field(value, head[:-2], key)
        if not isinstance(items, list):
            raise ValueError(f"projection {key}: {head} is not a list")
        return [_project(item, rest, key) for item in items]
    return _project(_field(value, head, key), rest, key)


def _field(value: object, name: str, key: str) -> object:
    if not isinstance(value, Mapping) or name not in value:
        raise ValueError(f"projection {key}: missing field {name}")
    return value[name]


@dataclass(frozen=True, slots=True)
class LiveGateObservationV1:
    """Projected result of one registry gate; ``error`` is empty on success."""

    exit_code: int
    observed: dict[str, object]
    error: str


def _sealed_python_bootstrap_v1(
    source: AnchoredFileV1,
    root: AnchoredDirectoryV1,
    logical_relative: str,
    arguments: Sequence[str],
) -> str:
    """Compile and execute bounded sealed bytes under a descriptor-rooted logical filename."""

    source_path = source.child_path
    root_path = root.child_path
    logical_path = f"{root_path}/{logical_relative}"
    argv = (logical_path, *arguments)
    return "\n".join(
        (
            "import sys",
            f"sys.path.insert(0, {root_path!r})",
            f"sys.argv = list({argv!r})",
            f"with open({source_path!r}, 'rb') as _sealed_source:",
            f"    _source = _sealed_source.read({_MAX_HASHED_FILE_BYTES + 1})",
            f"if len(_source) > {_MAX_HASHED_FILE_BYTES}:",
            "    raise RuntimeError('sealed executable snapshot exceeds its bound')",
            "_globals = {",
            "    '__name__': '__main__',",
            f"    '__file__': {logical_path!r},",
            "    '__package__': None,",
            "    '__spec__': None,",
            "    '__cached__': None,",
            "    '__loader__': None,",
            "}",
            f"exec(compile(_source, {logical_path!r}, 'exec'), _globals, _globals)",
        )
    )


def _isolated_gate_argv_v1(
    program: AnchoredFileV1,
    root: AnchoredDirectoryV1,
    logical_relative: str,
    arguments: Sequence[str],
) -> tuple[str, ...]:
    """Run sealed checker bytes after isolated startup; root ``sitecustomize`` is never auto-imported."""

    bootstrap = _sealed_python_bootstrap_v1(
        program,
        root,
        logical_relative,
        arguments,
    )
    return (sys.executable, "-I", "-c", bootstrap)


def _observe_live_gate_bound_v1(
    spec: LiveGateSpecV1,
    root: AnchoredDirectoryV1,
    *,
    checker: AnchoredFileV1 | None,
    supervisor: SupervisorCodeV1 | None,
) -> LiveGateObservationV1:
    preflight = live_gate_preflight_v1(root)
    if preflight:
        return LiveGateObservationV1(-1, {}, "; ".join(preflight))
    owned_checker: AnchoredFileV1 | None = None
    owned_supervisor: SupervisorCodeV1 | None = None
    try:
        if checker is None:
            owned_checker = checker = root.open_file(spec.checker_path)
        if supervisor is None:
            owned_supervisor = supervisor = bind_supervisor_code_v1(root)
        elif supervisor.root is not root:
            return LiveGateObservationV1(
                -1, {}, "live gate supervisor is not owned by the bound gate root"
            )
        run = run_bounded_process_v1(
            _isolated_gate_argv_v1(
                checker,
                root,
                spec.checker_path,
                spec.argv[2:],
            ),
            cwd=root,
            env=gate_environment_v1(root),
            bounds=ProcessBoundsV1(spec.timeout_seconds, MAX_GATE_OUTPUT_BYTES),
            inherit=(checker,),
            supervisor=supervisor,
        )
        if run.error:
            return LiveGateObservationV1(run.exit_code, {}, run.error)
        if run.escaped_descendants:
            return LiveGateObservationV1(
                run.exit_code, {}, f"live gate leaked {run.escaped_descendants} descendant process(es) beyond its process group; killed after reparenting"
            )
        if checker.rehash() != checker.sha256:
            return LiveGateObservationV1(
                run.exit_code, {}, "checker bytes changed in place during execution"
            )
        if spec.output_format == "text":
            return LiveGateObservationV1(run.exit_code, {}, "")
        try:
            parsed = decode_bounded_json_v1(
                run.stdout,
                name=f"live gate {spec.gate_id} stdout",
                limits=GATE_OUTPUT_LIMITS_V1,
            )
            observed = {
                key: project_observed_value_v1(parsed, key)
                for key in spec.observed_projection
            }
        except (BoundedJsonError, ValueError) as exc:
            return LiveGateObservationV1(run.exit_code, {}, str(exc))
        return LiveGateObservationV1(run.exit_code, observed, "")
    except OSError as exc:
        return LiveGateObservationV1(
            -1, {}, f"live gate descriptor binding refused: {type(exc).__name__}: {exc}"
        )
    finally:
        try:
            if owned_checker is not None:
                owned_checker.close()
        finally:
            if owned_supervisor is not None:
                owned_supervisor.close()


def observe_live_gate_v1(
    spec: LiveGateSpecV1,
    root: WorkingDirectory,
    *,
    checker: AnchoredFileV1 | None = None,
    supervisor: SupervisorCodeV1 | None = None,
) -> LiveGateObservationV1:
    """Execute one registry gate with the explicit environment and project stdout.

    Raises ``ValueError`` for any spec object that is not the registry entry
    itself, so a caller cannot smuggle argv through a look-alike spec. Returns
    a typed error without spawning when ``live_gate_preflight_v1`` fails. With
    an anchored root, the preflight, the search path, and the child's working
    directory all address the anchored inode. With ``checker``, the child
    executes the immutable sealed snapshot captured while the source inode
    matched ``checker.sha256``; the mutable source descriptor is retained only
    for persistent-drift checks. Pathname swaps and transient in-place source
    rewrites therefore cannot change the top-level bytes that execute.
    """

    if LIVE_GATE_REGISTRY.get(spec.gate_id) is not spec:
        raise ValueError("live gate spec is not the registry entry")
    try:
        if isinstance(root, AnchoredDirectoryV1):
            return _observe_live_gate_bound_v1(
                spec, root, checker=checker, supervisor=supervisor
            )
        with AnchoredDirectoryV1.open(Path(root)) as anchored:
            return _observe_live_gate_bound_v1(
                spec, anchored, checker=checker, supervisor=supervisor
            )
    except OSError as exc:
        return LiveGateObservationV1(
            -1, {}, f"live gate root binding refused: {type(exc).__name__}: {exc}"
        )


if __name__ == "__main__":
    if sys.argv[1:] != ["--supervise-v1"]:
        raise SystemExit(2)
    supervise_main()
