"""Decode the launchers a deployment step installs or a container runs.

Scan scope comes from these operations rather than from a declared source root.
A launcher the decoder cannot read becomes a typed finding, so an unmodelled
launcher shape cannot silently shrink the scanned surface.

Every path is resolved inside the exact repository root.  A symlink that
escapes, dangles, or loops rejects instead of widening the read set.
"""

from __future__ import annotations

import contextlib
import hashlib
import os
import re
import shlex
import stat
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import TypeVar

LAUNCHER_DIRECTORY = "bin"
INSTALL_SCRIPT = "scripts/install_zenodex.sh"

MAX_LAUNCHER_BYTES = 256 * 1024
MAX_DOCKERFILES = 64
MAX_ROOT_ENTRIES = 4096
MAX_LAUNCHERS = 64
MAX_LAUNCHER_LINES = 512


@dataclass(frozen=True, slots=True)
class ScanResourceLimitsV2:
    """Aggregate ceilings for one report invocation."""

    max_source_bytes: int = 64 * 1024 * 1024
    max_ast_nodes: int = 8_000_000
    max_closure_edges: int = 65_536
    max_observations: int = 16_384
    max_retained_descriptors: int = 8_192
    max_retained_cache_bytes: int = 64 * 1024 * 1024

    def __post_init__(self) -> None:
        for name in self.__dataclass_fields__:
            value = getattr(self, name)
            if type(value) is not int or value < 1:
                raise ValueError(f"{name} must be a positive exact integer")


DEFAULT_SCAN_RESOURCE_LIMITS_V2 = ScanResourceLimitsV2()


class ResourceBudgetExceeded(RuntimeError):
    """A named aggregate budget rejected work before retaining its result."""

    def __init__(self, budget: str, limit: int) -> None:
        self.budget = budget
        self.limit = limit
        super().__init__(f"{budget} exceeds {limit}")


class ScanResourceMeterV2:
    """Mutable invocation-local accounting owned by a repository snapshot."""

    def __init__(self, limits: ScanResourceLimitsV2) -> None:
        self.limits = limits
        self.source_bytes = 0
        self.ast_nodes = 0
        self.closure_edges = 0
        self.observations = 0
        self.retained_descriptors = 1
        self.retained_cache_bytes = 0
        if self.retained_descriptors > limits.max_retained_descriptors:
            raise ResourceBudgetExceeded(
                "retained_descriptors", limits.max_retained_descriptors
            )

    @staticmethod
    def _checked_total(current: int, amount: int, maximum: int, budget: str) -> int:
        if type(amount) is not int or amount < 0:
            raise ValueError(f"{budget} increment must be a nonnegative exact integer")
        if amount > maximum - current:
            raise ResourceBudgetExceeded(budget, maximum)
        return current + amount

    def claim_source_bytes(self, amount: int) -> None:
        total = self._checked_total(
            self.source_bytes, amount, self.limits.max_source_bytes, "source_bytes"
        )
        self.source_bytes = total

    def claim_ast_nodes(self, amount: int) -> None:
        total = self._checked_total(
            self.ast_nodes, amount, self.limits.max_ast_nodes, "ast_nodes"
        )
        self.ast_nodes = total

    def claim_closure_edges(self, amount: int) -> None:
        total = self._checked_total(
            self.closure_edges,
            amount,
            self.limits.max_closure_edges,
            "closure_edges",
        )
        self.closure_edges = total

    def claim_observations(self, amount: int) -> None:
        total = self._checked_total(
            self.observations,
            amount,
            self.limits.max_observations,
            "observations",
        )
        self.observations = total

    def claim_retained(self, cache_bytes: int) -> None:
        descriptors = self._checked_total(
            self.retained_descriptors,
            1,
            self.limits.max_retained_descriptors,
            "retained_descriptors",
        )
        cached = self._checked_total(
            self.retained_cache_bytes,
            cache_bytes,
            self.limits.max_retained_cache_bytes,
            "retained_cache_bytes",
        )
        self.retained_descriptors = descriptors
        self.retained_cache_bytes = cached

    def release_retained(self, cache_bytes: int) -> None:
        """Release accounting for a descriptor that was not actually retained."""

        if self.retained_descriptors <= 1 or not 0 <= cache_bytes <= self.retained_cache_bytes:
            raise RuntimeError("invalid retained-resource release")
        self.retained_descriptors -= 1
        self.retained_cache_bytes -= cache_bytes

_T = TypeVar("_T")

# Every launcher pattern is applied with fullmatch. A prefix match would accept
# trailing shell syntax such as "; evil", "&& evil", or "| evil".
_TARGET = r"(?P<target>[A-Za-z0-9_./-]+\.py)"
_ARGUMENT = r"(?:[A-Za-z0-9_.-]+|'[^']*')"
_INSTALL_WRAPPER_RE = re.compile(
    rf"install_wrapper \"(?P<name>[A-Za-z0-9_.-]+)\" python3? \"\$\{{repo_dir\}}/{_TARGET}\""
    rf"(?: {_ARGUMENT})*"
)
_INSTALL_WRAPPER_DECL_RE = re.compile(r"install_wrapper\(\)\s*\{")
_LAUNCHER_EXEC_RE = re.compile(
    rf"exec python3? \"\$\{{repo_dir\}}/{_TARGET}\"(?: {_ARGUMENT})*(?: \"\$@\")?"
)
_SHELL_MODULE_RE = re.compile(r"\bpython3?\s+-m\s+(?P<module>[A-Za-z_][A-Za-z0-9_.]*)")
_SHELL_SCRIPT_RE = re.compile(r"\bpython3?\s+(?P<target>[A-Za-z0-9_./-]+\.py)\b")
# One whole recognized Python invocation, optionally backgrounded. Anything more
# on the line, including a second command, leaves the modelled set.
_CONTAINER_PYTHON_LINE_RE = re.compile(
    r"python3? (?:-m [A-Za-z_][A-Za-z0-9_.]*|[A-Za-z0-9_./-]+\.py)"
    r"(?: [A-Za-z0-9_.=/-]+)*(?: &)?"
)
_DOCKER_DISPATCH_RE = re.compile(r"^(?:ENTRYPOINT|CMD)\b(?P<body>.*)$", re.IGNORECASE)
_DOCKER_COPY_RE = re.compile(r"^COPY\b(?P<body>.*)$", re.IGNORECASE)
_SHELL_TOKEN_RE = re.compile(r"[A-Za-z0-9_./-]+\.sh\b")

# A generated launcher has one fixed shape. Anything outside it is a directive
# this decoder does not model, and an unmodelled directive may execute anything.
# These are exact whole-line forms, never prefixes, and this is deliberately not
# a shell parser.
_COMMENT_RE = re.compile(r"#.*")
_SET_OPTION_RE = re.compile(r"set -eu")
_SCRIPT_DIR_RE = re.compile(r'script_dir=\$\(CDPATH= cd -- "\$\(dirname -- "\$0"\)" && pwd\)')
_REPO_DIR_RE = re.compile(r'repo_dir=\$\(CDPATH= cd -- "\$\{script_dir\}/\.\." && pwd\)')
_INERT_LINE_PATTERNS = (_COMMENT_RE, _SET_OPTION_RE, _SCRIPT_DIR_RE, _REPO_DIR_RE)


@dataclass(frozen=True, slots=True, order=True)
class DeployedEntrypointV2:
    entrypoint_id: str
    target: str
    discovery: str

    def to_dict(self) -> dict[str, str]:
        return {"discovery": self.discovery, "entrypoint_id": self.entrypoint_id, "target": self.target}


@dataclass(frozen=True, slots=True, order=True)
class ClosureFindingV2:
    path: str
    rule_id: str
    evidence: str

    def to_dict(self) -> dict[str, str]:
        return {"evidence": self.evidence, "path": self.path, "rule_id": self.rule_id}


class RepositorySnapshotChanged(ValueError):
    """The invocation subject changed after its descriptor-backed snapshot began."""


@dataclass(frozen=True, slots=True)
class _FileReadV2:
    raw: bytes | None
    error: str | None
    identity: tuple[int, int, int, int, int] | None
    descriptor: int | None


class RepositorySnapshotV2:
    """One persistent descriptor-backed repository capability.

    All paths are interpreted relative to one open root directory descriptor.
    Reads are cached, probes are identity-bound, and a final stability check
    replays every consumed file and complete directory enumeration.  The
    pathname is checked against the still-open descriptor at phase boundaries,
    so rename/replacement and inode-reuse strategies cannot mix subjects.
    """

    def __init__(
        self,
        root: Path,
        *,
        resource_limits: ScanResourceLimitsV2 = DEFAULT_SCAN_RESOURCE_LIMITS_V2,
    ) -> None:
        self.root_path = _absolute_lexical(root)
        try:
            self._descriptor = _open_directory_componentwise(self.root_path)
        except OSError as exc:
            raise ValueError(f"repository root is not a symlink-free directory: {exc}") from exc
        try:
            self.resource_meter = ScanResourceMeterV2(resource_limits)
            status = os.fstat(self._descriptor)
        except BaseException as primary:
            try:
                os.close(self._descriptor)
            except BaseException as cleanup_error:
                primary.add_note(
                    "repository root cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise
        self._root_identity = (status.st_dev, status.st_ino)
        self._root_stat_identity = self._identity(status)
        self._file_reads: dict[tuple[str, int], _FileReadV2] = {}
        self._complete_directories: dict[str, tuple[str, ...]] = {}
        self._directory_capabilities: dict[
            str, tuple[int, tuple[int, int, int, int, int]]
        ] = {}
        self._probes: dict[str, tuple[str, tuple[int, int, int, int, int] | None]] = {}
        self._closed = False

    def __enter__(self) -> RepositorySnapshotV2:
        return self

    def __exit__(self, _type: object, _value: object, _traceback: object) -> None:
        self.close()

    def __fspath__(self) -> str:
        return os.fspath(self.root_path)

    def __truediv__(self, value: str) -> Path:
        return self.root_path / value

    def joinpath(self, *values: str) -> Path:
        return self.root_path.joinpath(*values)

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        for record in self._file_reads.values():
            if record.descriptor is not None:
                with contextlib.suppress(OSError):
                    os.close(record.descriptor)
        for descriptor, _ in self._directory_capabilities.values():
            with contextlib.suppress(OSError):
                os.close(descriptor)
        with contextlib.suppress(OSError):
            os.close(self._descriptor)

    def assert_path_identity(self) -> None:
        self._require_open()
        try:
            current = _open_directory_componentwise(self.root_path)
        except OSError as exc:
            raise RepositorySnapshotChanged(f"repository root path changed: {exc}") from exc
        try:
            status = os.fstat(current)
            if (status.st_dev, status.st_ino) != self._root_identity:
                raise RepositorySnapshotChanged("repository root path no longer names the bound descriptor")
        finally:
            os.close(current)

    def read_bounded_text(self, relative: str, maximum: int) -> tuple[str | None, str | None]:
        self._require_canonical(relative)
        key = (relative, maximum)
        record = self._file_reads.get(key)
        if record is None:
            record = self._read_file(relative, maximum)
            self._file_reads[key] = record
        if record.raw is None:
            return None, record.error
        try:
            return record.raw.decode("utf-8", errors="strict"), None
        except UnicodeDecodeError as exc:
            return None, str(exc)

    def iter_directory(self, relative: str) -> Iterable[str]:
        """Yield one directory and remember exact contents only if fully consumed."""

        if relative:
            self._require_canonical(relative)
        descriptor = self._open_directory(relative)
        consumed: list[str] = []
        complete = False
        try:
            with os.scandir(descriptor) as entries:
                for entry in entries:
                    consumed.append(entry.name)
                    yield entry.name
            complete = True
        finally:
            with contextlib.suppress(OSError):
                os.close(descriptor)
            if complete:
                canonical = tuple(sorted(consumed))
                prior = self._complete_directories.setdefault(relative, canonical)
                if prior != canonical:
                    raise RepositorySnapshotChanged(f"directory changed during snapshot: {relative or '.'}")

    def contained_regular_file(self, relative: str) -> bool:
        state = self._probe(relative)
        return state[0] == "regular"

    def classify_candidate(self, relative: str) -> str | None:
        state, _ = self._probe(relative)
        if state == "missing":
            return None
        if state == "regular":
            return None
        if state == "symlink":
            return self._symlink_reason(relative, frozenset())
        if state == "nonregular":
            return "unresolvable"
        return state

    def _symlink_reason(self, relative: str, seen: frozenset[str]) -> str:
        if relative in seen:
            return "unresolvable"
        parts = PurePosixPath(relative).parts
        parent = PurePosixPath(*parts[:-1]).as_posix() if parts[:-1] else ""
        try:
            directory = self._open_directory(parent)
            try:
                target = os.readlink(parts[-1], dir_fd=directory)
            finally:
                os.close(directory)
        except OSError:
            return "unresolvable"
        target_path = PurePosixPath(target)
        if target_path.is_absolute():
            try:
                target_relative = _absolute_lexical(Path(target)).relative_to(
                    self.root_path
                ).as_posix()
            except ValueError:
                return "escapes_root"
        else:
            combined = os.path.normpath(
                (PurePosixPath(parent) / target_path).as_posix()
            )
            if combined in {"", ".", ".."} or combined.startswith("../"):
                return "escapes_root"
            target_relative = combined
        if canonical_relative_path(target_relative) != target_relative:
            return "unresolvable"
        state, _ = self._probe_now(target_relative)
        if state == "missing":
            return "dangling"
        if state == "symlink":
            return self._symlink_reason(target_relative, seen | {relative})
        if state == "unresolvable":
            return "unresolvable"
        return "symlink_refused"

    def verify_stable(self) -> None:
        """Reject any subject change relevant to a completed report."""

        self.assert_path_identity()
        for key, expected_file in self._file_reads.items():
            if not self._file_read_is_stable(key[0], key[1], expected_file):
                raise RepositorySnapshotChanged(f"repository file changed: {key[0]}")
        root_status = os.fstat(self._descriptor)
        if self._identity(root_status) != self._root_stat_identity:
            raise RepositorySnapshotChanged("repository root directory changed")
        for relative, (descriptor, expected_identity) in self._directory_capabilities.items():
            if self._identity(os.fstat(descriptor)) != expected_identity:
                raise RepositorySnapshotChanged(f"repository directory changed: {relative}")
            try:
                current = self._open_directory_uncached(relative)
            except OSError as exc:
                raise RepositorySnapshotChanged(
                    f"repository directory path changed: {relative}: {exc}"
                ) from exc
            try:
                current_status = os.fstat(current)
                if (current_status.st_dev, current_status.st_ino) != (
                    expected_identity[0],
                    expected_identity[1],
                ):
                    raise RepositorySnapshotChanged(
                        f"repository directory path changed: {relative}"
                    )
            finally:
                os.close(current)
        for relative, expected_names in self._complete_directories.items():
            observed_names = tuple(sorted(self._directory_names_now(relative)))
            if observed_names != expected_names:
                raise RepositorySnapshotChanged(
                    f"repository directory changed: {relative or '.'}"
                )
        for relative, expected_probe in self._probes.items():
            if expected_probe[0] == "missing":
                # The retained parent-directory identity above detects a new
                # or removed entry without reopening every absent candidate.
                continue
            observed_probe = self._probe_now(relative)
            if observed_probe != expected_probe:
                raise RepositorySnapshotChanged(f"repository path changed: {relative}")
        self.assert_path_identity()

    def _require_open(self) -> None:
        if self._closed:
            raise ValueError("repository snapshot is closed")

    def _require_canonical(self, relative: str) -> None:
        if canonical_relative_path(relative) != relative:
            raise ValueError("repository snapshot path must be canonical and relative")

    def _open_directory(self, relative: str) -> int:
        self._require_open()
        if not relative:
            return os.dup(self._descriptor)
        cached = self._directory_capabilities.get(relative)
        if cached is not None:
            return os.dup(cached[0])
        parts = PurePosixPath(relative).parts
        parent = PurePosixPath(*parts[:-1]).as_posix() if parts[:-1] else ""
        directory = self._open_directory(parent)
        try:
            descriptor = os.open(
                parts[-1],
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC,
                dir_fd=directory,
            )
        finally:
            os.close(directory)
        retained: int | None = None
        retained_claimed = False

        def release_acquired(primary: BaseException | None) -> None:
            cleanup_errors: list[BaseException] = []
            if retained_claimed:
                try:
                    self.resource_meter.release_retained(0)
                except BaseException as exc:  # cleanup must still close both descriptors
                    cleanup_errors.append(exc)
            for owned_descriptor in (retained, descriptor):
                if owned_descriptor is not None:
                    try:
                        os.close(owned_descriptor)
                    except BaseException as exc:  # preserve the acquisition failure
                        cleanup_errors.append(exc)
            if primary is not None:
                for cleanup_error in cleanup_errors:
                    primary.add_note(
                        "directory capability cleanup also failed: "
                        f"{type(cleanup_error).__name__}: {cleanup_error}"
                    )
            elif cleanup_errors:
                raise cleanup_errors[0]

        try:
            identity = self._identity(os.fstat(descriptor))
            retained = os.dup(descriptor)
            self.resource_meter.claim_retained(0)
            retained_claimed = True
            prior = self._directory_capabilities.setdefault(
                relative, (retained, identity)
            )
        except BaseException as primary:
            release_acquired(primary)
            raise
        if prior[0] != retained:
            release_acquired(None)
            return os.dup(prior[0])
        return descriptor

    def _open_directory_uncached(self, relative: str) -> int:
        descriptor = os.dup(self._descriptor)
        try:
            for component in PurePosixPath(relative).parts if relative else ():
                next_descriptor = os.open(
                    component,
                    os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC,
                    dir_fd=descriptor,
                )
                os.close(descriptor)
                descriptor = next_descriptor
            return descriptor
        except OSError:
            with contextlib.suppress(OSError):
                os.close(descriptor)
            raise

    def _open_regular_file(self, relative: str) -> int:
        self._require_canonical(relative)
        parts = PurePosixPath(relative).parts
        directory = self._open_directory(PurePosixPath(*parts[:-1]).as_posix() if parts[:-1] else "")
        try:
            descriptor = os.open(
                parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=directory
            )
        finally:
            os.close(directory)
        try:
            status = os.fstat(descriptor)
            if not stat.S_ISREG(status.st_mode):
                raise OSError("not a regular file")
        except BaseException as primary:
            try:
                os.close(descriptor)
            except BaseException as cleanup_error:
                primary.add_note(
                    "regular file cleanup also failed: "
                    f"{type(cleanup_error).__name__}: {cleanup_error}"
                )
            raise
        return descriptor

    @staticmethod
    def _identity(status: os.stat_result) -> tuple[int, int, int, int, int]:
        return (
            status.st_dev,
            status.st_ino,
            status.st_mode,
            status.st_size,
            status.st_ctime_ns,
        )

    def _read_file(
        self, relative: str, maximum: int, *, retain_budget: bool = True
    ) -> _FileReadV2:
        claimed_cache: int | None = None
        try:
            descriptor = self._open_regular_file(relative)
        except OSError as exc:
            return _FileReadV2(None, str(exc), None, None)
        try:
            status = os.fstat(descriptor)
            identity = self._identity(status)
            if status.st_size > maximum:
                if retain_budget:
                    self.resource_meter.claim_retained(0)
                    claimed_cache = 0
                return _FileReadV2(None, f"exceeds {maximum} bytes", identity, descriptor)
            if retain_budget:
                self.resource_meter.claim_retained(status.st_size)
                claimed_cache = status.st_size
            chunks: list[bytes] = []
            remaining = maximum + 1
            while remaining:
                chunk = os.read(descriptor, min(remaining, 64 * 1024))
                if not chunk:
                    break
                chunks.append(chunk)
                remaining -= len(chunk)
            raw = b"".join(chunks)
            if self._identity(os.fstat(descriptor)) != identity:
                raise RepositorySnapshotChanged(f"repository file changed while read: {relative}")
        except OSError as exc:
            os.close(descriptor)
            if claimed_cache is not None:
                self.resource_meter.release_retained(claimed_cache)
            return _FileReadV2(None, str(exc), None, None)
        except (MemoryError, ResourceBudgetExceeded, SystemError, ValueError):
            os.close(descriptor)
            if claimed_cache is not None:
                self.resource_meter.release_retained(claimed_cache)
            raise
        if len(raw) > maximum:
            return _FileReadV2(None, f"exceeds {maximum} bytes", identity, descriptor)
        return _FileReadV2(raw, None, identity, descriptor)

    def _file_read_is_stable(
        self, relative: str, maximum: int, expected: _FileReadV2
    ) -> bool:
        if expected.descriptor is None or expected.identity is None:
            observed = self._read_file(relative, maximum, retain_budget=False)
            try:
                return (
                    observed.raw,
                    observed.error,
                    observed.identity,
                ) == (expected.raw, expected.error, expected.identity)
            finally:
                if observed.descriptor is not None:
                    os.close(observed.descriptor)
        if self._identity(os.fstat(expected.descriptor)) != expected.identity:
            return False
        try:
            current = self._open_regular_file(relative)
        except OSError:
            return False
        try:
            status = os.fstat(current)
            return self._identity(status) == expected.identity
        finally:
            os.close(current)

    def _directory_names_now(self, relative: str) -> tuple[str, ...]:
        descriptor = self._open_directory(relative)
        try:
            with os.scandir(descriptor) as entries:
                return tuple(entry.name for entry in entries)
        finally:
            os.close(descriptor)

    def _probe(self, relative: str) -> tuple[str, tuple[int, int, int, int, int] | None]:
        self._require_canonical(relative)
        observed = self._probe_now(relative)
        prior = self._probes.setdefault(relative, observed)
        if prior != observed:
            raise RepositorySnapshotChanged(f"repository path changed during snapshot: {relative}")
        return observed

    def _probe_now(self, relative: str) -> tuple[str, tuple[int, int, int, int, int] | None]:
        parts = PurePosixPath(relative).parts
        try:
            directory = self._open_directory(
                PurePosixPath(*parts[:-1]).as_posix() if parts[:-1] else ""
            )
        except FileNotFoundError:
            return "missing", None
        except OSError:
            return "unresolvable", None
        try:
            try:
                status = os.stat(parts[-1], dir_fd=directory, follow_symlinks=False)
            except FileNotFoundError:
                return "missing", None
            if stat.S_ISLNK(status.st_mode):
                return "symlink", self._identity(status)
            if stat.S_ISREG(status.st_mode):
                return "regular", self._identity(status)
            return "nonregular", self._identity(status)
        finally:
            os.close(directory)


def bounded_materialize_v2(values: Iterable[_T], maximum: int) -> tuple[tuple[_T, ...], bool]:
    """Collect at most ``maximum`` values, probing exactly one overflow item.

    On overflow the partial tuple is discarded because returning a prefix would
    turn a resource ceiling into a silently incomplete deployment inventory.
    """

    if type(maximum) is not int or maximum < 0:
        raise ValueError("maximum must be a nonnegative exact integer")
    collected: list[_T] = []
    iterator = iter(values)
    try:
        for value in iterator:
            collected.append(value)
            if len(collected) > maximum:
                return (), True
        return tuple(collected), False
    finally:
        close = getattr(iterator, "close", None)
        if close is not None:
            close()


def _root_path(root: Path | RepositorySnapshotV2) -> Path:
    return root.root_path if isinstance(root, RepositorySnapshotV2) else root


def _absolute_lexical(path: Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def _lexical_relative(path: Path, root: Path | RepositorySnapshotV2) -> str | None:
    absolute_root = _absolute_lexical(_root_path(root))
    absolute_path = _absolute_lexical(path)
    try:
        relative = absolute_path.relative_to(absolute_root).as_posix()
    except ValueError:
        return None
    return relative if canonical_relative_path(relative) == relative else None


def _open_directory_componentwise(path: Path) -> int:
    """Open an absolute directory while refusing a symlink in every component."""

    absolute = _absolute_lexical(path)
    descriptor = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC)
    try:
        for component in absolute.parts[1:]:
            next_descriptor = os.open(
                component,
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC,
                dir_fd=descriptor,
            )
            os.close(descriptor)
            descriptor = next_descriptor
        return descriptor
    except OSError:
        with contextlib.suppress(OSError):
            os.close(descriptor)
        raise


def _open_confined_regular_file(path: Path, root: Path) -> int:
    relative = _lexical_relative(path, root)
    if relative is None:
        raise OSError("path is not a canonical descendant of the subject root")
    parts = PurePosixPath(relative).parts
    directory = _open_directory_componentwise(root)
    try:
        for component in parts[:-1]:
            next_directory = os.open(
                component,
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC,
                dir_fd=directory,
            )
            os.close(directory)
            directory = next_directory
        descriptor = os.open(
            parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=directory
        )
    finally:
        with contextlib.suppress(OSError):
            os.close(directory)
    status = os.fstat(descriptor)
    if not stat.S_ISREG(status.st_mode):
        os.close(descriptor)
        raise OSError("not a regular file")
    return descriptor


def _directory_names(root: Path | RepositorySnapshotV2, relative: str) -> Iterable[str]:
    if isinstance(root, RepositorySnapshotV2):
        yield from root.iter_directory(relative)
        return
    directory = _open_directory_componentwise(root)
    try:
        if relative:
            for component in PurePosixPath(relative).parts:
                next_directory = os.open(
                    component,
                    os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC,
                    dir_fd=directory,
                )
                os.close(directory)
                directory = next_directory
        with os.scandir(directory) as entries:
            for entry in entries:
                yield entry.name
    finally:
        with contextlib.suppress(OSError):
            os.close(directory)


def canonical_relative_path(value: str) -> str | None:
    """Reject absolute, escaping, or noncanonical repository paths."""

    if not value or value.startswith("/") or "\\" in value or ":" in value:
        return None
    if any(ord(character) < 32 or ord(character) == 127 for character in value):
        return None
    # Inspect the literal components: PurePosixPath silently folds away "." parts.
    if any(part in {"", ".", ".."} for part in value.split("/")):
        return None
    return PurePosixPath(value).as_posix()


def safe_relative(path: Path, root: Path | RepositorySnapshotV2) -> str | None:
    """Resolve a path inside the exact repository root, or reject it.

    A symlink may leave the root, dangle, or loop.  Resolution failure and
    escape both reject, so the scan never reads outside the subject tree and
    never raises on a hostile tree.
    """

    relative = _lexical_relative(path, root)
    if relative is None:
        return None
    if isinstance(root, RepositorySnapshotV2):
        return relative if root.contained_regular_file(relative) else None
    try:
        descriptor = _open_confined_regular_file(path, root)
    except OSError:
        return None
    os.close(descriptor)
    return relative


def contained_file(path: Path, root: Path | RepositorySnapshotV2) -> Path | None:
    """Return the resolved path when it is a regular file inside the root."""

    relative = _lexical_relative(path, root)
    if relative is None:
        return None
    if isinstance(root, RepositorySnapshotV2):
        return _absolute_lexical(path) if root.contained_regular_file(relative) else None
    try:
        descriptor = _open_confined_regular_file(path, root)
    except OSError:
        return None
    os.close(descriptor)
    return _absolute_lexical(path)


def classify_unscannable_candidate(
    candidate: Path, root: Path | RepositorySnapshotV2
) -> str | None:
    """Explain why a lexically present candidate cannot be scanned.

    A path that exists in the tree, including as a symlink, is a reachable edge.
    Returning ``None`` for it would drop that edge silently, so escaping,
    dangling, and looping candidates each receive a reason instead.  A candidate
    with no lexical presence is an ordinary external import and stays out of
    scope.
    """

    relative = _lexical_relative(candidate, root)
    if relative is None:
        return "escapes_root"
    if isinstance(root, RepositorySnapshotV2):
        return root.classify_candidate(relative)
    if not (candidate.is_symlink() or candidate.exists()):
        return None
    try:
        resolved = candidate.resolve(strict=True)
    except FileNotFoundError:
        return "dangling"
    except (OSError, RuntimeError, ValueError):
        return "unresolvable"
    if not resolved.is_relative_to(root):
        return "escapes_root"
    return None if resolved.is_file() else "unresolvable"


def read_bounded_text(
    path: Path, maximum: int, *, root: Path | RepositorySnapshotV2 | None = None
) -> tuple[str | None, str | None]:
    """Read at most ``maximum`` bytes from a regular file, never following a link.

    The read stops one byte past the limit, so an oversized file is rejected
    without allocating its full contents.
    """

    subject_root = root if root is not None else path.parent
    if isinstance(subject_root, RepositorySnapshotV2):
        relative = _lexical_relative(path, subject_root)
        if relative is None:
            return None, "path is not a canonical descendant of the subject root"
        return subject_root.read_bounded_text(relative, maximum)
    try:
        descriptor = _open_confined_regular_file(path, subject_root)
    except OSError as exc:
        return None, str(exc)
    closed = False
    try:
        status = os.fstat(descriptor)
        if not stat.S_ISREG(status.st_mode):
            return None, "not a regular file"
        if status.st_size > maximum:
            return None, f"exceeds {maximum} bytes"
        with os.fdopen(descriptor, "rb", closefd=True) as handle:
            closed = True
            raw = handle.read(maximum + 1)
    except OSError as exc:
        return None, str(exc)
    finally:
        if not closed:
            with contextlib.suppress(OSError):
                os.close(descriptor)
    if len(raw) > maximum:
        return None, f"exceeds {maximum} bytes"
    try:
        return raw.decode("utf-8", errors="strict"), None
    except UnicodeDecodeError as exc:
        return None, str(exc)


def classify_launcher_line(line: str) -> str:
    """Classify one launcher line as INERT, DISPATCH, or UNMODELLED.

    Every pattern consumes the whole line, so appended shell syntax such as
    ``; evil``, ``&& evil``, ``| evil``, or a nested substitution leaves the
    recognized forms and becomes UNMODELLED.  A conditional, a second command,
    and an env wrapper fall the same way.  This is a closed grammar for a
    generated file, never a shell parser.
    """

    stripped = line.strip()
    if not stripped:
        return "INERT"
    if _LAUNCHER_EXEC_RE.fullmatch(stripped) is not None:
        return "DISPATCH"
    if any(pattern.fullmatch(stripped) is not None for pattern in _INERT_LINE_PATTERNS):
        return "INERT"
    return "UNMODELLED"


def _decode_install_script(
    root: Path | RepositorySnapshotV2,
) -> tuple[list[DeployedEntrypointV2], list[ClosureFindingV2], list[tuple[str, str]]]:
    root_path = _root_path(root)
    script = contained_file(root_path / INSTALL_SCRIPT, root)
    if script is None:
        return [], [ClosureFindingV2(INSTALL_SCRIPT, "install_script_missing", "no contained regular file")], []
    text, error = read_bounded_text(script, MAX_LAUNCHER_BYTES, root=root)
    if text is None:
        return [], [ClosureFindingV2(INSTALL_SCRIPT, "install_script_unreadable", error or "unreadable")], []
    entrypoints: list[DeployedEntrypointV2] = []
    findings: list[ClosureFindingV2] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if re.match(r"install(?:\s|$)", stripped) is not None:
            findings.append(
                ClosureFindingV2(INSTALL_SCRIPT, "unmodelled_installer_directive", stripped)
            )
        if "install_wrapper" not in stripped:
            continue
        if _INSTALL_WRAPPER_DECL_RE.fullmatch(stripped) is not None:
            # The declaration and its body are shell semantics, not part of the
            # exact call extractor below.
            continue
        matches = list(_INSTALL_WRAPPER_RE.finditer(stripped))
        if not matches:
            findings.append(ClosureFindingV2(INSTALL_SCRIPT, "undecodable_install_wrapper", stripped))
            continue
        entrypoints.extend(
            DeployedEntrypointV2(match.group("name"), match.group("target"), "INSTALL_SCRIPT")
            for match in matches
        )
        if len(matches) > 1:
            findings.append(ClosureFindingV2(INSTALL_SCRIPT, "multi_command_install_line", stripped))
        elif matches[0].group(0) != stripped:
            findings.append(ClosureFindingV2(INSTALL_SCRIPT, "undecodable_install_wrapper", stripped))
    if not entrypoints and not findings:
        findings.append(
            ClosureFindingV2(INSTALL_SCRIPT, "install_script_declares_no_launcher", "zero install_wrapper calls")
        )
    # This decoder extracts one exact call form; it deliberately does not claim
    # to parse shell semantics. The complete installer bytes therefore remain a
    # declared blocking gap, and the digest makes any body or appended-command
    # change invalidate the recorded evidence.
    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
    gaps: list[tuple[str, str]] = [
        (INSTALL_SCRIPT, "unmodelled_installer_shell"),
        (INSTALL_SCRIPT, f"installer_source_sha256_{digest}"),
    ]
    return entrypoints, findings, gaps


def _decode_one_launcher(
    path: Path, relative: str, root: Path | RepositorySnapshotV2
) -> tuple[list[DeployedEntrypointV2], list[ClosureFindingV2]]:
    text, error = read_bounded_text(path, MAX_LAUNCHER_BYTES, root=root)
    if text is None:
        return [], [ClosureFindingV2(relative, "launcher_unreadable", error or "unreadable")]
    lines = text.splitlines()
    if len(lines) > MAX_LAUNCHER_LINES:
        return [], [ClosureFindingV2(relative, "launcher_line_ceiling_exceeded", str(MAX_LAUNCHER_LINES))]
    targets: list[str] = []
    findings: list[ClosureFindingV2] = []
    for number, line in enumerate(lines, start=1):
        classification = classify_launcher_line(line)
        if classification == "DISPATCH":
            match = _LAUNCHER_EXEC_RE.fullmatch(line.strip())
            if match is not None:
                targets.append(match.group("target"))
        elif classification == "UNMODELLED":
            findings.append(
                ClosureFindingV2(relative, "unconsumed_launcher_directive", f"line {number}: {line.strip()}")
            )
    if not targets:
        findings.append(ClosureFindingV2(relative, "undecodable_launcher", "no decodable exec target"))
    return [DeployedEntrypointV2(path.name, target, "LAUNCHER_WRAPPER") for target in targets], findings


def _decode_launcher_directory(
    root: Path | RepositorySnapshotV2,
) -> tuple[list[DeployedEntrypointV2], list[ClosureFindingV2]]:
    root_path = _root_path(root)
    directory = root_path / LAUNCHER_DIRECTORY
    if isinstance(root, RepositorySnapshotV2):
        if root._probe(LAUNCHER_DIRECTORY)[0] == "missing":
            return [], []
    elif not (directory.exists() or directory.is_symlink()):
        return [], []
    try:
        candidates, exceeded = bounded_materialize_v2(
            _directory_names(root, LAUNCHER_DIRECTORY), MAX_LAUNCHERS
        )
    except OSError as exc:
        return [], [
            ClosureFindingV2(
                LAUNCHER_DIRECTORY,
                "launcher_directory_unreadable",
                str(exc),
            )
        ]
    if exceeded:
        # Report before omission: a truncated enumeration would hide launchers.
        return [], [ClosureFindingV2(LAUNCHER_DIRECTORY, "launcher_count_ceiling_exceeded", str(MAX_LAUNCHERS))]
    entrypoints: list[DeployedEntrypointV2] = []
    findings: list[ClosureFindingV2] = []
    for name in sorted(candidates):
        path = directory / name
        relative = safe_relative(path, root)
        if relative is None:
            reason = classify_unscannable_candidate(path, root)
            rule = (
                "launcher_escapes_repository_root"
                if reason in {"escapes_root", "symlink_refused"}
                else "launcher_is_not_a_regular_file"
            )
            findings.append(ClosureFindingV2(path.name, rule, reason or LAUNCHER_DIRECTORY))
            continue
        if contained_file(path, root) is None:
            findings.append(ClosureFindingV2(relative, "launcher_is_not_a_regular_file", LAUNCHER_DIRECTORY))
            continue
        decoded, decoded_findings = _decode_one_launcher(path, relative, root)
        entrypoints.extend(decoded)
        findings.extend(decoded_findings)
    return entrypoints, findings


def _local_copy_bindings(
    root: Path | RepositorySnapshotV2,
    dockerfile: str,
    text: str,
    required_destinations: frozenset[str],
) -> tuple[dict[str, str], list[ClosureFindingV2]]:
    """Bind entrypoint destinations to exact regular local COPY sources.

    Directory, wildcard, and build-stage COPY instructions are ordinary image
    construction inputs. They are irrelevant to executable dispatch unless
    their destination is the exact shell path named by ENTRYPOINT or CMD.
    """

    bindings: dict[str, str] = {}
    findings: list[ClosureFindingV2] = []
    for line in text.splitlines():
        match = _DOCKER_COPY_RE.match(line.strip())
        if match is None:
            continue
        try:
            tokens = shlex.split(match.group("body"), posix=True)
        except ValueError:
            tokens = []
        if not tokens or tokens[0].startswith("--"):
            continue
        if len(tokens) != 2:
            findings.append(ClosureFindingV2(dockerfile, "docker_copy_unmodelled", line.strip()))
            continue
        source, destination = tokens
        if destination.endswith("/"):
            destination = f"{destination}{PurePosixPath(source).name}"
        if destination not in required_destinations:
            continue
        canonical_source = canonical_relative_path(source)
        if canonical_source is None or contained_file(_root_path(root) / source, root) is None:
            findings.append(
                ClosureFindingV2(dockerfile, "container_copy_source_unresolvable", source)
            )
            continue
        prior = bindings.get(destination)
        if prior is not None and prior != canonical_source:
            findings.append(
                ClosureFindingV2(
                    dockerfile,
                    "container_copy_destination_ambiguous",
                    f"{destination}:{prior}:{canonical_source}",
                )
            )
            continue
        bindings[destination] = canonical_source
    return bindings, findings


def _container_shell_scripts(
    root: Path | RepositorySnapshotV2,
) -> tuple[list[str], list[ClosureFindingV2], list[tuple[str, str]]]:
    """Resolve shell scripts that a container image designates as its dispatch."""

    scripts: set[str] = set()
    gaps: list[tuple[str, str]] = []
    try:
        root_names, root_exceeded = bounded_materialize_v2(
            _directory_names(root, ""), MAX_ROOT_ENTRIES
        )
    except OSError as exc:
        return [], [ClosureFindingV2(".", "repository_root_unreadable", str(exc))], []
    if root_exceeded:
        return [], [
            ClosureFindingV2(
                ".", "repository_root_entry_ceiling_exceeded", str(MAX_ROOT_ENTRIES)
            )
        ], []
    names = tuple(name for name in root_names if name.casefold().startswith("dockerfile"))
    if len(names) > MAX_DOCKERFILES:
        # Report before omission: truncating the list would hide a dispatch.
        return [], [ClosureFindingV2(".", "dockerfile_count_ceiling_exceeded", str(MAX_DOCKERFILES))], []
    findings: list[ClosureFindingV2] = []
    for relative in sorted(names):
        dockerfile = _root_path(root) / relative
        text, error = read_bounded_text(dockerfile, MAX_LAUNCHER_BYTES, root=root)
        if text is None:
            findings.append(ClosureFindingV2(relative, "dockerfile_unreadable", error or "unreadable"))
            continue
        dispatches = [
            match
            for line in text.splitlines()
            if (match := _DOCKER_DISPATCH_RE.match(line.strip())) is not None
        ]
        required_destinations = frozenset(
            token
            for match in dispatches
            for token in _SHELL_TOKEN_RE.findall(match.group("body"))
        )
        copy_bindings, copy_findings = _local_copy_bindings(
            root, relative, text, required_destinations
        )
        findings.extend(copy_findings)
        for match in dispatches:
            body = match.group("body")
            tokens = _SHELL_TOKEN_RE.findall(body)
            if not tokens:
                # ``ENTRYPOINT ["python"]`` and a healthcheck ``CMD python -c``
                # both run code this decoder does not model. Silence would read
                # as no container dispatch at all.
                gaps.append((relative, "unmodelled_container_dispatch"))
                continue
            for token in tokens:
                resolved = copy_bindings.get(token)
                if resolved is None:
                    findings.append(ClosureFindingV2(relative, "container_entrypoint_copy_unbound", token))
                else:
                    scripts.add(resolved)
    return sorted(scripts), findings, gaps


def _unmodelled_body_lines(text: str) -> int:
    """Count container-script lines the decoder does not model in full.

    A line is modelled only when the whole line is one recognized Python
    invocation.  ``python good.py; sh evil.sh`` contains a recognized target yet
    also runs another command, so a containment test rather than a search keeps
    that second command visible.
    """

    unmodelled = 0
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if _CONTAINER_PYTHON_LINE_RE.fullmatch(stripped) is None:
            unmodelled += 1
    return unmodelled


def _decode_container_entrypoints(
    root: Path | RepositorySnapshotV2,
) -> tuple[list[DeployedEntrypointV2], list[ClosureFindingV2], list[tuple[str, str]]]:
    scripts, findings, gaps = _container_shell_scripts(root)
    entrypoints: list[DeployedEntrypointV2] = []
    for script in scripts:
        text, error = read_bounded_text(_root_path(root) / script, MAX_LAUNCHER_BYTES, root=root)
        if text is None:
            findings.append(ClosureFindingV2(script, "container_script_unreadable", error or "unreadable"))
            continue
        entrypoints.extend(
            DeployedEntrypointV2(script, f"-m {match.group('module')}", "CONTAINER_ENTRYPOINT")
            for match in _SHELL_MODULE_RE.finditer(text)
        )
        entrypoints.extend(
            DeployedEntrypointV2(script, match.group("target"), "CONTAINER_ENTRYPOINT")
            for match in _SHELL_SCRIPT_RE.finditer(text)
        )
        if _unmodelled_body_lines(text):
            # The rest of the container script runs commands this decoder does
            # not model, so its reach is declared incompleteness.
            gaps.append((script, "unmodelled_container_shell_body"))
    return entrypoints, findings, gaps


def derive_deployed_entrypoints(
    root: Path | RepositorySnapshotV2,
) -> tuple[tuple[DeployedEntrypointV2, ...], tuple[ClosureFindingV2, ...], tuple[tuple[str, str], ...]]:
    """Decode every launcher a deployment step installs or a container runs."""

    if not isinstance(root, RepositorySnapshotV2):
        with RepositorySnapshotV2(root) as snapshot:
            result = derive_deployed_entrypoints(snapshot)
            snapshot.verify_stable()
            return result
    root.assert_path_identity()
    entrypoints: list[DeployedEntrypointV2] = []
    findings: list[ClosureFindingV2] = []
    decoded, decoded_findings, installer_gaps = _decode_install_script(root)
    entrypoints.extend(decoded)
    findings.extend(decoded_findings)
    decoded, decoded_findings = _decode_launcher_directory(root)
    entrypoints.extend(decoded)
    findings.extend(decoded_findings)
    container, container_findings, gaps = _decode_container_entrypoints(root)
    entrypoints.extend(container)
    findings.extend(container_findings)
    unique = tuple(sorted(set(entrypoints)))
    findings.extend(_validate_targets(unique, root))
    root.assert_path_identity()
    return unique, tuple(sorted(findings)), tuple(sorted(set(gaps) | set(installer_gaps)))


def _validate_targets(
    entrypoints: tuple[DeployedEntrypointV2, ...], root: Path | RepositorySnapshotV2
) -> list[ClosureFindingV2]:
    findings: list[ClosureFindingV2] = []
    for entrypoint in entrypoints:
        if entrypoint.target.startswith("-m "):
            continue
        if canonical_relative_path(entrypoint.target) is None:
            findings.append(
                ClosureFindingV2(entrypoint.target, "launcher_target_noncanonical", entrypoint.entrypoint_id)
            )
        elif contained_file(_root_path(root) / entrypoint.target, root) is None:
            # Missing, non-regular, dangling, or escaping targets all reject here.
            findings.append(
                ClosureFindingV2(entrypoint.target, "launcher_target_unresolvable", entrypoint.entrypoint_id)
            )
    return findings
