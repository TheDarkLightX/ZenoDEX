"""Replayable bounded-partial O-004 operator-surface registry.

The artifact projects source from one pinned implementation commit through Git
objects.  Checkout qualification is separate, so committing the evidence does
not invalidate the artifact.  This module grants no runtime authority.
"""

from __future__ import annotations

import ast
import hashlib
import json
import os
import selectors
import shutil
import signal
import stat
import subprocess
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Final, NoReturn, cast

import yaml

SCHEMA_V1: Final = "zenodex/operator-surface-registry/v1"
CHECK_SCHEMA_V1: Final = "zenodex/operator-surface-registry-check/v1"
ARTIFACT_RELATIVE_PATH_V1: Final = Path(
    "docs/research/ZENODEX_OPERATOR_SURFACE_REGISTRY_V1.json"
)
IMPLEMENTATION_SUBJECT_COMMIT_V1: Final = (
    "59a3565b77d993a374631c2554734ce152438e15"
)
EVIDENCE_CHANGED_PATHS_V1: Final = (
    "docs/research/ZENODEX_OPERATOR_SURFACE_REGISTRY_V1.json",
    "tests/test_check_operator_surface_registry_v1.py",
    "tests/test_operator_surface_registry_semantic_mutants_v1.py",
    "tools/build_operator_surface_registry_v1.py",
    "tools/check_operator_surface_registry_v1.py",
    "tools/operator_surface_registry_v1.py",
)

SOURCE_BOUND_V1: Final = "SOURCE_BOUND_UNEXECUTED"
QUARANTINED_V1: Final = "QUARANTINED"
RETAINED_V1: Final = "RETAINED_PRESENTATION"
CHECKOUT_DRAFT_V1: Final = "UNCOMMITTED_DRAFT"
CHECKOUT_REPLAYABLE_V1: Final = "CLEAN_COMMITTED_DESCENDANT"

MAX_ARTIFACT_BYTES_V1: Final = 524_288
MAX_SOURCE_BYTES_V1: Final = 2_097_152
MAX_GIT_OUTPUT_BYTES_V1: Final = 4_194_304
MAX_JSON_DEPTH_V1: Final = 32
MAX_JSON_NODES_V1: Final = 16_384
MAX_AST_NODES_V1: Final = 200_000
MAX_JS_TOKENS_V1: Final = 200_000
MAX_STATUS_ROWS_V1: Final = 64
GIT_TIMEOUT_SECONDS_V1: Final = 10
_GIT_STDERR_MAX_BYTES_V1: Final = 65_536
_READ_CHUNK_BYTES_V1: Final = 65_536
_READ_ONLY_GIT_SUBCOMMANDS_V1: Final = frozenset(
    {"cat-file", "diff", "ls-files", "ls-tree", "merge-base", "rev-parse", "status"}
)


@dataclass(frozen=True)
class OperatorSurfaceRegistryRejectV1(ValueError):
    """Stable fail-closed rejection at an untrusted boundary."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


@dataclass(frozen=True)
class _GitBlobV1:
    path: str
    raw: bytes
    sha256: str


@dataclass(frozen=True)
class _JsTokenV1:
    kind: str
    value: str


RouteRowV1 = tuple[str, str, int | None, tuple[str, ...]]

_QUARANTINE_SURFACES_V1: Final = (
    "api-server-startup-admission",
    "local-route-quarantine-core",
    "local-testnet-compose-profile",
    "local-testnet-lifecycle",
    "ui-runtime-route-config",
    "ui-runtime-route-presentation",
)
ROUTE_ROWS_V1: Final[tuple[RouteRowV1, ...]] = (
    ("spot_ledger_api", SOURCE_BOUND_V1, None, ("local-testnet-compose-profile",)),
    ("oracle_api", SOURCE_BOUND_V1, None, ("local-testnet-compose-profile",)),
    ("confidential_attestation_api", SOURCE_BOUND_V1, None, ("local-testnet-compose-profile",)),
    ("perps_wallet_stream_8", QUARANTINED_V1, 8, _QUARANTINE_SURFACES_V1),
    ("zusd_tau_wallet_stream_9", QUARANTINED_V1, 9, _QUARANTINE_SURFACES_V1),
    ("zusd_monetary_wallet_stream_11", QUARANTINED_V1, 11, _QUARANTINE_SURFACES_V1),
    (
        "autotrader_api",
        QUARANTINED_V1,
        None,
        ("api-server-startup-admission", "local-testnet-compose-profile"),
    ),
    ("ui_shell", RETAINED_V1, None, ("ui-application-navigation",)),
    ("perps_ui", RETAINED_V1, None, ("ui-application-navigation",)),
    ("zusd_ui", RETAINED_V1, None, ("ui-application-navigation",)),
    ("strategy_ui", RETAINED_V1, None, ("ui-application-navigation",)),
    ("keys_ui", RETAINED_V1, None, ("ui-application-navigation",)),
)
QUARANTINED_STREAMS_V1: Final = (8, 9, 11)


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise OperatorSurfaceRegistryRejectV1(code, path, detail)


def _sha256_v1(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _is_lower_hex_v1(value: object, length: int) -> bool:
    return (
        type(value) is str
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _validate_json_value_v1(
    value: object,
    *,
    depth: int = 0,
    nodes: list[int] | None = None,
) -> None:
    if depth > MAX_JSON_DEPTH_V1:
        _reject("JSON_DEPTH", "artifact", "JSON depth exceeds the fixed limit")
    counter = nodes if nodes is not None else [0]
    counter[0] += 1
    if counter[0] > MAX_JSON_NODES_V1:
        _reject("JSON_NODE_LIMIT", "artifact", "JSON node count exceeds the fixed limit")
    if value is None or type(value) in {bool, int, str}:
        if type(value) is str and len(value) > 131_072:
            _reject("JSON_STRING_LIMIT", "artifact", "string exceeds the fixed limit")
        return
    if type(value) is list:
        for item in value:
            _validate_json_value_v1(item, depth=depth + 1, nodes=counter)
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                _reject("JSON_KEY_TYPE", "artifact", "object keys must be exact strings")
            _validate_json_value_v1(item, depth=depth + 1, nodes=counter)
        return
    _reject("JSON_VALUE_TYPE", "artifact", f"unsupported type {type(value).__name__}")


def canonical_json_bytes_v1(value: object) -> bytes:
    """Encode the registry's closed JSON language deterministically."""

    _validate_json_value_v1(value)
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def decode_json_object_v1(raw: bytes, label: str) -> dict[str, object]:
    """Decode one duplicate-free object while rejecting floats and constants."""

    if type(raw) is not bytes:
        _reject("JSON_BYTES_TYPE", label, "must be exact bytes")

    def reject_float(_value: str) -> NoReturn:
        _reject("JSON_FLOAT", label, "floating-point values are forbidden")

    def parse_integer(value: str) -> int:
        if len(value.lstrip("-")) > 256:
            _reject("JSON_INTEGER_LIMIT", label, "integer digit limit exceeded")
        return int(value)

    def exact_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                _reject("JSON_DUPLICATE_KEY", label, key)
            result[key] = value
        return result

    try:
        value = json.loads(
            raw.decode("utf-8"),
            parse_float=reject_float,
            parse_constant=reject_float,
            parse_int=parse_integer,
            object_pairs_hook=exact_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("JSON_DECODE", label, type(exc).__name__)
    if type(value) is not dict:
        _reject("JSON_ROOT_TYPE", label, "root must be an object")
    _validate_json_value_v1(value)
    return cast(dict[str, object], value)


def _root_v1(root: Path) -> Path:
    try:
        resolved = root.resolve(strict=True)
    except OSError as exc:
        _reject("ROOT_UNAVAILABLE", str(root), type(exc).__name__)
    if not resolved.is_dir():
        _reject("ROOT_TYPE", str(resolved), "root must be a directory")
    return resolved


def _read_regular_file_v1(path: Path, *, max_bytes: int, label: str) -> bytes:
    try:
        metadata = os.lstat(path)
    except OSError as exc:
        _reject("FILE_UNAVAILABLE", label, type(exc).__name__)
    if not stat.S_ISREG(metadata.st_mode):
        _reject("FILE_TYPE", label, "must be a regular non-symlink file")
    if metadata.st_size < 0 or metadata.st_size > max_bytes:
        _reject("FILE_SIZE", label, f"must be no more than {max_bytes} bytes")
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        _reject("FILE_OPEN", label, type(exc).__name__)
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode):
            _reject("FILE_TYPE", label, "opened file is not regular")
        if (opened.st_dev, opened.st_ino) != (metadata.st_dev, metadata.st_ino):
            _reject("FILE_CHANGED_DURING_OPEN", label, "file identity changed")
        chunks: list[bytes] = []
        remaining = max_bytes + 1
        while remaining > 0:
            chunk = os.read(descriptor, min(65_536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
    finally:
        os.close(descriptor)
    if len(raw) > max_bytes:
        _reject("FILE_SIZE", label, f"must be no more than {max_bytes} bytes")
    return raw


def read_artifact_file_v1(path: Path) -> bytes:
    return _read_regular_file_v1(
        path,
        max_bytes=MAX_ARTIFACT_BYTES_V1,
        label=str(path),
    )


def _git_binary_v1() -> str:
    binary = shutil.which("git", path=os.defpath)
    if binary is None or not os.path.isabs(binary):
        _reject("GIT_EXECUTION", "git", "absolute Git executable unavailable")
    return binary


def _git_environment_v1() -> dict[str, str]:
    return {
        "GIT_ATTR_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_SYSTEM": os.devnull,
        "GIT_EDITOR": "/bin/false",
        "GIT_EXTERNAL_DIFF": "/bin/false",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_PAGER": "",
        "GIT_SEQUENCE_EDITOR": "/bin/false",
        "LC_ALL": "C",
        "PAGER": "",
        "PATH": os.defpath,
        "XDG_CONFIG_HOME": os.devnull,
    }


def _kill_and_wait_git_v1(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except OSError:
        pass
    try:
        process.wait(timeout=1.0)
    except (OSError, subprocess.TimeoutExpired):
        try:
            process.kill()
            process.wait(timeout=1.0)
        except (OSError, subprocess.TimeoutExpired):
            pass


def _git_v1(
    root: Path,
    arguments: tuple[str, ...],
    *,
    allowed_returncodes: frozenset[int] = frozenset((0,)),
    max_stdout_bytes: int = MAX_GIT_OUTPUT_BYTES_V1,
) -> subprocess.CompletedProcess[bytes]:
    if not arguments or arguments[0] not in _READ_ONLY_GIT_SUBCOMMANDS_V1:
        _reject("GIT_COMMAND", "git", "subcommand is outside the closed read-only set")
    checked_root = os.path.abspath(os.fspath(_root_v1(root)))
    argv = (
        _git_binary_v1(),
        "--no-pager",
        "-c",
        "core.attributesFile=/dev/null",
        "-c",
        "core.checkStat=default",
        "-c",
        "core.editor=/bin/false",
        "-c",
        "core.excludesFile=/dev/null",
        "-c",
        "core.fileMode=true",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "core.ignoreStat=false",
        "-c",
        "core.fsmonitor=false",
        "-c",
        "core.pager=",
        "-c",
        "core.trustctime=true",
        "-c",
        f"core.worktree={checked_root}",
        "-c",
        "diff.external=/bin/false",
        "-c",
        "diff.ignoreSubmodules=none",
        "-c",
        "sequence.editor=/bin/false",
        "-c",
        "status.submoduleSummary=false",
        "-C",
        checked_root,
        *arguments,
    )
    environment = _git_environment_v1()
    environment["GIT_WORK_TREE"] = checked_root
    try:
        process = subprocess.Popen(
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            start_new_session=True,
        )
    except OSError as exc:
        _reject("GIT_EXECUTION", "git", type(exc).__name__)
    if process.stdout is None or process.stderr is None:
        _kill_and_wait_git_v1(process)
        _reject("GIT_EXECUTION", "git", "subprocess pipes unavailable")
    output = {"stdout": bytearray(), "stderr": bytearray()}
    selector = selectors.DefaultSelector()
    deadline = time.monotonic() + GIT_TIMEOUT_SECONDS_V1
    try:
        selector.register(process.stdout, selectors.EVENT_READ, "stdout")
        selector.register(process.stderr, selectors.EVENT_READ, "stderr")
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                _kill_and_wait_git_v1(process)
                _reject("GIT_EXECUTION", "git", "TimeoutExpired")
            for key, _mask in selector.select(timeout=min(0.05, remaining)):
                chunk = os.read(key.fd, _READ_CHUNK_BYTES_V1)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                stream = str(key.data)
                output[stream].extend(chunk)
                limit = max_stdout_bytes if stream == "stdout" else _GIT_STDERR_MAX_BYTES_V1
                if len(output[stream]) > limit:
                    _kill_and_wait_git_v1(process)
                    _reject("GIT_OUTPUT_LIMIT", "git", "Git output exceeds the fixed limit")
        returncode = process.wait(timeout=max(0.01, deadline - time.monotonic()))
    except OperatorSurfaceRegistryRejectV1:
        _kill_and_wait_git_v1(process)
        raise
    except (OSError, subprocess.TimeoutExpired) as exc:
        _kill_and_wait_git_v1(process)
        _reject("GIT_EXECUTION", "git", type(exc).__name__)
    except BaseException:
        _kill_and_wait_git_v1(process)
        raise
    finally:
        selector.close()
        process.stdout.close()
        process.stderr.close()
    if returncode not in allowed_returncodes:
        _reject("GIT_COMMAND", "git", f"returncode={returncode}")
    return subprocess.CompletedProcess(
        argv,
        returncode,
        stdout=bytes(output["stdout"]),
        stderr=bytes(output["stderr"]),
    )


def _git_commit_v1(root: Path, revision: str) -> str:
    result = _git_v1(
        root,
        ("rev-parse", "--verify", f"{revision}^{{commit}}"),
        max_stdout_bytes=128,
    )
    try:
        commit = result.stdout.decode("ascii").strip()
    except UnicodeDecodeError:
        _reject("GIT_COMMIT_ENCODING", revision, "commit output must be ASCII")
    if not _is_lower_hex_v1(commit, 40):
        _reject("GIT_COMMIT_TYPE", revision, "commit must be lowercase 40-hex")
    return commit


def _relative_git_path_v1(path: str) -> str:
    candidate = Path(path)
    if candidate.is_absolute() or any(part in {"", ".", ".."} for part in candidate.parts):
        _reject("GIT_PATH", path, "path must remain repository-relative")
    return path


def _git_blob_v1(root: Path, commit: str, path: str) -> _GitBlobV1:
    relative = _relative_git_path_v1(path)
    tree = _git_v1(
        root,
        ("ls-tree", "-z", commit, "--", relative),
        max_stdout_bytes=512,
    ).stdout
    if not tree.endswith(b"\0") or tree.count(b"\0") != 1:
        _reject("GIT_TREE_ROW", relative, "expected exactly one tree row")
    header, separator, observed_path = tree[:-1].partition(b"\t")
    if not separator:
        _reject("GIT_TREE_ROW", relative, "tree row has no path separator")
    try:
        mode, object_type, object_id = header.decode("ascii").split(" ")
        decoded_path = observed_path.decode("utf-8")
    except (UnicodeDecodeError, ValueError):
        _reject("GIT_TREE_ROW", relative, "tree row is not canonical")
    if mode not in {"100644", "100755"} or object_type != "blob":
        _reject("GIT_BLOB_MODE", relative, "source must be a regular Git blob")
    if decoded_path != relative or not _is_lower_hex_v1(object_id, 40):
        _reject("GIT_TREE_IDENTITY", relative, "tree row identity mismatch")
    size_result = _git_v1(
        root,
        ("cat-file", "-s", object_id),
        max_stdout_bytes=64,
    )
    try:
        size = int(size_result.stdout.decode("ascii").strip())
    except (UnicodeDecodeError, ValueError):
        _reject("GIT_BLOB_SIZE", relative, "blob size is invalid")
    if size < 0 or size > MAX_SOURCE_BYTES_V1:
        _reject("GIT_BLOB_SIZE", relative, "blob exceeds the fixed source limit")
    raw = _git_v1(
        root,
        ("cat-file", "blob", object_id),
        max_stdout_bytes=MAX_SOURCE_BYTES_V1,
    ).stdout
    if len(raw) != size:
        _reject("GIT_BLOB_LENGTH", relative, "blob length differs from Git metadata")
    return _GitBlobV1(path=relative, raw=raw, sha256=_sha256_v1(raw))


def _expected_evidence_paths_v1(paths: tuple[str, ...]) -> tuple[str, ...]:
    """Close the candidate set before using it in Git pathspecs or lstat."""

    if not paths:
        _reject("EVIDENCE_PATH_SET", "evidence", "at least one evidence path is required")
    if any(type(path) is not str for path in paths):
        _reject("EVIDENCE_PATH_TYPE", "evidence", "evidence paths must be exact strings")
    if len(set(paths)) != len(paths):
        _reject("EVIDENCE_PATH_DUPLICATE", "evidence", "duplicate evidence path")
    for path in paths:
        _relative_git_path_v1(path)
    return tuple(sorted(paths))


def _reject_grafts_v1(root: Path) -> None:
    """Refuse legacy graft ancestry because raw P..E must have native parents."""

    raw = _git_v1(
        root,
        ("rev-parse", "--git-path", "info/grafts"),
        max_stdout_bytes=4_096,
    ).stdout
    try:
        rendered = raw.decode("utf-8").strip()
    except UnicodeDecodeError:
        _reject("GIT_GRAFTS_PATH", "git", "grafts path is not UTF-8")
    if not rendered:
        _reject("GIT_GRAFTS_PATH", "git", "grafts path is empty")
    candidate = Path(rendered)
    if not candidate.is_absolute():
        candidate = _root_v1(root) / candidate
    try:
        os.lstat(candidate)
    except FileNotFoundError:
        return
    except OSError as exc:
        _reject("GIT_GRAFTS_PATH", str(candidate), type(exc).__name__)
    _reject("GIT_GRAFTS_PRESENT", str(candidate), "legacy graft ancestry is forbidden")


def _reject_index_suppression_v1(root: Path) -> None:
    """Reject index flags that can hide live tracked-file divergence."""

    raw = _git_v1(
        root,
        ("ls-files", "-v", "-z"),
        max_stdout_bytes=MAX_GIT_OUTPUT_BYTES_V1,
    ).stdout
    rows = raw.split(b"\0")
    if rows[-1] != b"":
        _reject("GIT_INDEX_ENCODING", "index", "ls-files output lacks terminator")
    for row in rows[:-1]:
        if len(row) < 3 or row[1:2] != b" ":
            _reject("GIT_INDEX_ENCODING", "index", "invalid ls-files row")
        try:
            tag = row[:1].decode("ascii")
            path = row[2:].decode("utf-8")
        except UnicodeDecodeError:
            _reject("GIT_INDEX_ENCODING", "index", "index row is not canonical")
        _relative_git_path_v1(path)
        if tag != "H":
            _reject(
                "EVIDENCE_INDEX_SUPPRESSION",
                path,
                f"tracked index tag {tag!r} is not admissible",
            )


def _reject_rename_copy_ambiguity_v1(root: Path, subject: str, head: str) -> None:
    """Reject similarity-based identity changes before accepting exact P..E paths."""

    raw = _git_v1(
        root,
        (
            "diff",
            "--no-ext-diff",
            "--no-textconv",
            "--ignore-submodules=none",
            "--find-renames=100%",
            "--find-copies=100%",
            "--find-copies-harder",
            "--name-status",
            "-z",
            "--diff-filter=ACDMRTUXB",
            subject,
            head,
        ),
        max_stdout_bytes=65_536,
    ).stdout
    rows = raw.split(b"\0")
    if rows[-1] != b"":
        _reject("GIT_DIFF_ENCODING", "P..E", "name-status output lacks terminator")
    index = 0
    while index < len(rows) - 1:
        try:
            status = rows[index].decode("ascii")
        except UnicodeDecodeError:
            _reject("GIT_DIFF_ENCODING", "P..E", "status is not ASCII")
        if not status:
            _reject("GIT_DIFF_ENCODING", "P..E", "empty status row")
        code = status[0]
        path_count = 2 if code in {"R", "C"} else 1
        if index + path_count >= len(rows):
            _reject("GIT_DIFF_ENCODING", "P..E", "truncated name-status row")
        if code in {"R", "C"}:
            _reject(
                "EVIDENCE_RENAME_COPY_AMBIGUITY",
                "P..E",
                "rename or copy identity is forbidden in the closed evidence set",
            )
        index += 1 + path_count


def _require_draft_regular_evidence_paths_v1(root: Path, expected: tuple[str, ...]) -> None:
    """Bind each untracked candidate to a regular live inode before draft admission."""

    resolved = _root_v1(root)
    for path in expected:
        try:
            metadata = os.lstat(resolved / path)
        except OSError as exc:
            _reject("EVIDENCE_DRAFT_PATH_UNAVAILABLE", path, type(exc).__name__)
        if not stat.S_ISREG(metadata.st_mode):
            _reject("EVIDENCE_DRAFT_PATH_TYPE", path, "draft evidence must be a regular non-symlink file")


def _require_committed_regular_evidence_paths_v1(
    root: Path,
    head: str,
    expected: tuple[str, ...],
) -> None:
    """Bind every P..E candidate to one regular blob at E, never a link or gitlink."""

    for path in expected:
        _git_blob_v1(root, head, path)


def _parse_status_paths_v1(raw: bytes) -> tuple[tuple[str, str], ...]:
    if not raw:
        return ()
    rows = raw.split(b"\0")
    if rows[-1] != b"":
        _reject("GIT_STATUS_ENCODING", "worktree", "status output lacks terminator")
    parsed: list[tuple[str, str]] = []
    for row in rows[:-1]:
        if len(row) < 4 or row[2:3] != b" ":
            _reject("GIT_STATUS_ENCODING", "worktree", "unsupported status row")
        try:
            status = row[:2].decode("ascii")
            path = row[3:].decode("utf-8")
        except UnicodeDecodeError:
            _reject("GIT_STATUS_ENCODING", "worktree", "status row is not canonical")
        parsed.append((status, path))
        if len(parsed) > MAX_STATUS_ROWS_V1:
            _reject("GIT_STATUS_LIMIT", "worktree", "too many dirty paths")
    return tuple(parsed)


def classify_evidence_checkout_v1(
    root: Path,
    *,
    implementation_subject: str = IMPLEMENTATION_SUBJECT_COMMIT_V1,
    expected_changed_paths: tuple[str, ...] = EVIDENCE_CHANGED_PATHS_V1,
) -> dict[str, object]:
    """Classify P..E without attaching authority to a dirty live checkout."""

    expected = _expected_evidence_paths_v1(expected_changed_paths)
    _reject_grafts_v1(root)
    _reject_index_suppression_v1(root)
    subject = _git_commit_v1(root, implementation_subject)
    head_before = _git_commit_v1(root, "HEAD")
    ancestry = _git_v1(
        root,
        ("merge-base", "--is-ancestor", subject, head_before),
        allowed_returncodes=frozenset((0, 1)),
        max_stdout_bytes=0,
    )
    if ancestry.returncode != 0:
        _reject("EVIDENCE_NOT_DESCENDANT", "HEAD", "evidence HEAD must descend from P")

    _reject_rename_copy_ambiguity_v1(root, subject, head_before)

    excluded = tuple(f":(exclude){path}" for path in expected)
    outside = _git_v1(
        root,
        (
            "diff",
            "--no-ext-diff",
            "--no-textconv",
            "--ignore-submodules=none",
            "--quiet",
            subject,
            head_before,
            "--",
            ".",
            *excluded,
        ),
        allowed_returncodes=frozenset((0, 1)),
        max_stdout_bytes=0,
    )
    if outside.returncode != 0:
        _reject(
            "EVIDENCE_CHANGED_PATH_SCOPE",
            "P..E",
            "committed descendant changes a path outside the closed evidence set",
        )
    changed_raw = _git_v1(
        root,
        (
            "diff",
            "--no-ext-diff",
            "--no-textconv",
            "--ignore-submodules=none",
            "--name-only",
            "-z",
            "--diff-filter=ACDMRTUXB",
            subject,
            head_before,
            "--",
            *expected,
        ),
        max_stdout_bytes=65_536,
    ).stdout
    try:
        changed = tuple(
            sorted(path.decode("utf-8") for path in changed_raw.split(b"\0") if path)
        )
    except UnicodeDecodeError:
        _reject("EVIDENCE_PATH_ENCODING", "P..E", "changed path is not UTF-8")
    status_raw = _git_v1(
        root,
        (
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--ignore-submodules=none",
        ),
        max_stdout_bytes=65_536,
    ).stdout
    status_rows = _parse_status_paths_v1(status_raw)
    head_after = _git_commit_v1(root, "HEAD")
    if head_after != head_before:
        _reject("EVIDENCE_HEAD_RACE", "HEAD", "HEAD changed during evidence capture")

    if head_before == subject:
        draft_paths = tuple(sorted(path for status, path in status_rows if status == "??"))
        if any(status != "??" for status, _path in status_rows) or draft_paths != expected:
            _reject(
                "EVIDENCE_DRAFT_SCOPE",
                "worktree",
                "draft must contain exactly the six untracked evidence paths",
            )
        if changed:
            _reject("EVIDENCE_DRAFT_COMMIT_DRIFT", "P..E", "draft has committed changes")
        _require_draft_regular_evidence_paths_v1(root, expected)
        return {
            "changed_paths": list(expected),
            "evidence_head": head_before,
            "replayable": False,
            "status": CHECKOUT_DRAFT_V1,
        }

    if status_rows:
        _reject("EVIDENCE_WORKTREE_DIRTY", "worktree", "committed replay requires a clean worktree")
    _require_committed_regular_evidence_paths_v1(root, head_before, expected)
    if changed != expected:
        _reject(
            "EVIDENCE_CHANGED_PATH_SET",
            "P..E",
            f"expected={list(expected)} observed={list(changed)}",
        )
    return {
        "changed_paths": list(changed),
        "evidence_head": head_before,
        "replayable": True,
        "status": CHECKOUT_REPLAYABLE_V1,
    }


def _ast_shape_v1(value: object) -> object:
    """Project a Python AST without interpreter-version-only empty fields."""

    if isinstance(value, ast.AST):
        fields = [
            [name, _ast_shape_v1(field)]
            for name, field in ast.iter_fields(value)
            if name not in {"type_comment", "type_params"}
        ]
        return [type(value).__name__, fields]
    if type(value) is list:
        return [_ast_shape_v1(item) for item in cast(list[object], value)]
    if value is None or type(value) in {bool, int, str}:
        return value
    if type(value) in {float, bytes, type(Ellipsis)}:
        return [type(value).__name__, repr(value)]
    _reject("PYTHON_AST_VALUE", "python", type(value).__name__)


def _check_python_shape_v1(
    raw: bytes,
    *,
    path: str,
    names: tuple[str, ...],
    expected_sha256: str,
) -> None:
    try:
        tree = ast.parse(raw.decode("utf-8"), filename=path)
    except (UnicodeDecodeError, SyntaxError) as exc:
        _reject("PYTHON_PARSE", path, type(exc).__name__)
    count = sum(1 for _node in ast.walk(tree))
    if count > MAX_AST_NODES_V1:
        _reject("PYTHON_AST_LIMIT", path, "AST exceeds the fixed node limit")
    rows: dict[str, ast.AST] = {}
    for node in tree.body:
        name = getattr(node, "name", getattr(getattr(node, "target", None), "id", None))
        if type(name) is str:
            if name in rows:
                _reject("PYTHON_AST_DUPLICATE", path, name)
            rows[name] = node
    if any(name not in rows for name in names):
        _reject("PYTHON_AST_MISSING", path, "required structural node is absent")
    shape = [_ast_shape_v1(rows[name]) for name in names]
    if _sha256_v1(canonical_json_bytes_v1(shape)) != expected_sha256:
        _reject("PYTHON_AST_STRUCTURAL_DRIFT", path, "selected structural fingerprint changed")


def project_api_server_v1(raw: bytes) -> dict[str, object]:
    path = "src/integration/api_server.py"
    _check_python_shape_v1(
        raw,
        path=path,
        names=("_load_api_server_config", "_api_startup_refusal_lines", "main"),
        expected_sha256="258f234f7c72db96685213a33800e1237f82663499188de59778cae2e8c99b70",
    )
    return {
        "environment_bindings": {
            "autotrader_live_enabled": "AUTOTRADER_LIVE_API_ENABLED",
            "perps_wallet_enabled": "PERPS_WALLET_API_ENABLED",
            "zusd_monetary_wallet_enabled": "ZUSD_MONETARY_WALLET_API_ENABLED",
            "zusd_tau_wallet_enabled": "ZUSD_TAU_WALLET_API_ENABLED",
        },
        "main_order": ["environment_refusal", "startup_refusal", "server_construction"],
        "terminal_result": "RETURN_2_BEFORE_SERVER_CONSTRUCTION",
    }


def project_local_route_quarantine_v1(raw: bytes) -> dict[str, object]:
    path = "src/integration/local_route_quarantine.py"
    _check_python_shape_v1(
        raw,
        path=path,
        names=(
            "QUARANTINED_ROUTE_ENVIRONMENT_V1",
            "QUARANTINED_ROUTE_ALLOWED_VALUES_V1",
            "current_local_operator_release_admission_v1",
            "refuse_current_local_operator_operation_v1",
            "quarantined_route_environment_rejections_v1",
        ),
        expected_sha256="f12a2125a1702eaaa4d101e60fe280ba90ac9c0058b2a66c0d74fde3eab06825",
    )
    return {
        "allowed_disabled_values": ["0", "false"],
        "authority": "NONE",
        "quarantined_environment": [
            "PERPS_WALLET_API_ENABLED",
            "ZUSD_TAU_WALLET_API_ENABLED",
            "ZUSD_MONETARY_WALLET_API_ENABLED",
        ],
        "release_eligible": False,
        "terminal_operation_result": "RAISES_CURRENT_PROFILE_BLOCKED",
        "vm_gates_closed": [],
    }


def project_lifecycle_v1(raw: bytes) -> dict[str, object]:
    path = "tools/zenoctl_testnet_local/lifecycle.py"
    operations = {
        "_run_perps_wallet_cycle_smoke": "perps_wallet_cycle_smoke",
        "_run_release_flow_smoke": "release_flow_smoke",
        "_zusd_transfer_payload": "zusd_transfer_payload",
    }
    _check_python_shape_v1(
        raw,
        path=path,
        names=tuple(operations),
        expected_sha256="151b7ff68d58081d291131b2d5bebf8bd9324791241cb1906d0a73b4b01cf6f4",
    )
    return {"active_operation_refusals": operations}


def _reject_duplicate_yaml_keys_v1(node: yaml.nodes.Node, path: str) -> None:
    if isinstance(node, yaml.nodes.MappingNode):
        seen: set[str] = set()
        for key_node, value_node in node.value:
            if isinstance(key_node, yaml.nodes.ScalarNode) and key_node.value != "<<":
                if key_node.value in seen:
                    _reject("YAML_DUPLICATE_KEY", path, key_node.value)
                seen.add(key_node.value)
            _reject_duplicate_yaml_keys_v1(value_node, path)
    elif isinstance(node, yaml.nodes.SequenceNode):
        for child in node.value:
            _reject_duplicate_yaml_keys_v1(child, path)


def _exact_mapping_v1(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict or any(type(key) is not str for key in value):
        _reject("MAPPING_TYPE", path, "must be an exact string-keyed object")
    return cast(dict[str, object], value)


def project_compose_v1(raw: bytes) -> dict[str, object]:
    """Project route flags from the parsed Compose data model."""

    path = "docker-compose.local-testnet.yml"
    try:
        text = raw.decode("utf-8")
        composed = yaml.compose(text, Loader=yaml.SafeLoader)
        if composed is None:
            _reject("YAML_PARSE", path, "empty document")
        _reject_duplicate_yaml_keys_v1(composed, path)
        value = yaml.safe_load(text)
    except (UnicodeDecodeError, yaml.YAMLError) as exc:
        _reject("YAML_PARSE", path, type(exc).__name__)
    root = _exact_mapping_v1(value, path)
    services = _exact_mapping_v1(root.get("services"), f"{path}.services")
    api = _exact_mapping_v1(services.get("zenodex-api"), f"{path}.services.zenodex-api")
    environment = _exact_mapping_v1(
        api.get("environment"),
        f"{path}.services.zenodex-api.environment",
    )
    expected = {
        "AUTOTRADER_LIVE_API_ENABLED": "false",
        "CONFIDENTIAL_ATTESTATION_API_ENABLED": "true",
        "DEX_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "false",
        "ZUSD_MONETARY_WALLET_API_ENABLED": "false",
        "ZUSD_TAU_WALLET_API_ENABLED": "false",
    }
    if {name: environment.get(name) for name in expected} != expected:
        _reject("COMPOSE_ROUTE_ENVIRONMENT", path, "typed route environment projection drift")
    if type(services.get("zenodex-oracle")) is not dict:
        _reject("COMPOSE_ORACLE_SERVICE", path, "oracle service declaration is absent")
    return {
        "route_environment": expected,
        "zenodex_oracle_service_declared": True,
    }


def project_ui_config_v1(raw: bytes) -> dict[str, object]:
    """Project exact Boolean route flags from duplicate-free JSON."""

    path = "tools/dex-ui/public/zenodex-config.json"
    value = decode_json_object_v1(raw, path)
    expected = {
        "perpsWalletUiEnabled": False,
        "zusdMonetaryWalletUiEnabled": False,
        "zusdTauWalletUiEnabled": False,
    }
    if {name: value.get(name) for name in expected} != expected:
        _reject("UI_CONFIG_ROUTE_FLAGS", path, "UI value-route flags must remain exact false")
    return {"value_route_flags": expected}


def _tokenize_js_v1(raw: bytes, path: str) -> tuple[_JsTokenV1, ...]:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        _reject("JS_UTF8", path, "source must be UTF-8")
    tokens: list[_JsTokenV1] = []
    index = 0
    operators = ("===", "!==", "=>", "...", "?.", "&&", "||", "==", "!=", "<=", ">=", "++", "--")
    while index < len(text):
        character = text[index]
        if character.isspace():
            index += 1
            continue
        if text.startswith("//", index):
            newline = text.find("\n", index + 2)
            index = len(text) if newline < 0 else newline + 1
            continue
        if text.startswith("/*", index):
            closing = text.find("*/", index + 2)
            if closing < 0:
                _reject("JS_COMMENT", path, "unterminated block comment")
            index = closing + 2
            continue
        if character in {"'", '"', "`"}:
            quote = character
            start = index
            index += 1
            escaped = False
            while index < len(text):
                current = text[index]
                index += 1
                if escaped:
                    escaped = False
                elif current == "\\":
                    escaped = True
                elif current == quote:
                    break
            else:
                _reject("JS_STRING", path, "unterminated string")
            tokens.append(_JsTokenV1("string", text[start:index]))
        elif character.isalpha() or character in {"_", "$"}:
            start = index
            index += 1
            while index < len(text) and (text[index].isalnum() or text[index] in {"_", "$"}):
                index += 1
            tokens.append(_JsTokenV1("identifier", text[start:index]))
        elif character.isdigit():
            start = index
            index += 1
            while index < len(text) and (text[index].isalnum() or text[index] in {"_", "."}):
                index += 1
            tokens.append(_JsTokenV1("number", text[start:index]))
        else:
            operator = next(
                (candidate for candidate in operators if text.startswith(candidate, index)),
                character,
            )
            tokens.append(_JsTokenV1("punctuation", operator))
            index += len(operator)
        if len(tokens) > MAX_JS_TOKENS_V1:
            _reject("JS_TOKEN_LIMIT", path, "token count exceeds the fixed limit")
    return tuple(tokens)


def _matching_token_v1(
    tokens: tuple[_JsTokenV1, ...],
    opening_index: int,
    opening: str,
    closing: str,
    path: str,
) -> int:
    if opening_index >= len(tokens) or tokens[opening_index].value != opening:
        _reject("JS_STRUCTURE", path, f"expected {opening}")
    depth = 0
    for index in range(opening_index, len(tokens)):
        value = tokens[index].value
        if value == opening:
            depth += 1
        elif value == closing:
            depth -= 1
            if depth == 0:
                return index
    _reject("JS_STRUCTURE", path, f"unclosed {opening}")


def _top_level_declaration_v1(
    tokens: tuple[_JsTokenV1, ...],
    prefix: tuple[str, ...],
    path: str,
) -> int:
    depth = 0
    matches: list[int] = []
    values = tuple(token.value for token in tokens)
    for index, value in enumerate(values):
        if depth == 0 and values[index : index + len(prefix)] == prefix:
            matches.append(index)
        if value == "{":
            depth += 1
        elif value == "}":
            depth -= 1
            if depth < 0:
                _reject("JS_STRUCTURE", path, "unbalanced brace")
    if len(matches) != 1:
        _reject("JS_DECLARATION", path, f"expected one declaration {prefix}")
    return matches[0]


def _simple_js_string_v1(token: _JsTokenV1, path: str) -> str:
    if token.kind != "string" or token.value[0] not in {"'", '"'} or "\\" in token.value:
        _reject("JS_SIMPLE_STRING", path, "expected an unescaped quoted string")
    return token.value[1:-1]


def _parse_js_boolean_object_v1(
    tokens: tuple[_JsTokenV1, ...],
    opening_index: int,
    path: str,
) -> tuple[dict[str, bool], int]:
    closing = _matching_token_v1(tokens, opening_index, "{", "}", path)
    index = opening_index + 1
    result: dict[str, bool] = {}
    while index < closing:
        if index + 2 >= closing:
            _reject("JS_BOOLEAN_OBJECT", path, "truncated field")
        key = tokens[index]
        if key.kind != "identifier" or tokens[index + 1].value != ":":
            _reject("JS_BOOLEAN_OBJECT", path, "invalid field")
        value = tokens[index + 2].value
        if value not in {"false", "true"} or key.value in result:
            _reject("JS_BOOLEAN_OBJECT", path, "invalid or duplicate Boolean field")
        result[key.value] = value == "true"
        index += 3
        if index < closing:
            if tokens[index].value != ",":
                _reject("JS_BOOLEAN_OBJECT", path, "missing field separator")
            index += 1
    return result, closing


def project_ui_runtime_guard_v1(raw: bytes) -> dict[str, object]:
    """Project one source-level UI guard fingerprint; runtime semantics are unclaimed."""

    path = "tools/dex-ui/src/lib/api.js"
    tokens = _tokenize_js_v1(raw, path)
    constant = "CURRENT_PROFILE_QUARANTINED_VALUE_ROUTES_V1"
    start = _top_level_declaration_v1(tokens, ("const", constant, "="), path)
    expected_prefix = ("Object", ".", "freeze", "(", "{")
    prefix_start = start + 3
    if tuple(token.value for token in tokens[prefix_start : prefix_start + 5]) != expected_prefix:
        _reject("JS_ROUTE_GUARD", path, "guard must be an Object.freeze object")
    observed, closing = _parse_js_boolean_object_v1(tokens, prefix_start + 4, path)
    expected = {
        "perpsWalletEnabled": False,
        "zusdMonetaryWalletEnabled": False,
        "zusdTauWalletEnabled": False,
    }
    if observed != expected:
        _reject("JS_ROUTE_GUARD", path, "active UI route guard projection drift")
    if tuple(token.value for token in tokens[closing + 1 : closing + 3]) != (")", ";"):
        _reject("JS_ROUTE_GUARD", path, "guard declaration terminator drift")

    function_start = _top_level_declaration_v1(
        tokens,
        ("export", "function", "getRuntimeValueRoutePresentationV1"),
        path,
    )
    body_open = next(
        (index for index in range(function_start, len(tokens)) if tokens[index].value == "{"),
        -1,
    )
    if body_open < 0:
        _reject("JS_ROUTE_GUARD", path, "route projection function has no body")
    body_close = _matching_token_v1(tokens, body_open, "{", "}", path)
    body = tuple(token.value for token in tokens[body_open + 1 : body_close])
    if body != ("void", "runtimeConfig", ";", "return", constant, ";"):
        _reject("JS_ROUTE_GUARD", path, "route projection must directly return the frozen guard")
    return {"frozen_value_route_flags": expected}


def _parse_nav_tabs_v1(
    tokens: tuple[_JsTokenV1, ...],
    opening_index: int,
    path: str,
) -> dict[str, str]:
    closing = _matching_token_v1(tokens, opening_index, "[", "]", path)
    index = opening_index + 1
    tabs: dict[str, str] = {}
    while index < closing:
        if tokens[index].value != "{":
            _reject("JS_NAV_TABS", path, "tab row must be an object")
        row_close = _matching_token_v1(tokens, index, "{", "}", path)
        row = tokens[index + 1 : row_close]
        values = tuple(token.value for token in row)
        if (
            len(values) != 7
            or values[0] != "id"
            or values[1] != ":"
            or values[3] != ","
            or values[4] != "label"
            or values[5] != ":"
        ):
            _reject("JS_NAV_TABS", path, "tab row field shape drift")
        tab_id = _simple_js_string_v1(row[2], path)
        label = _simple_js_string_v1(row[6], path)
        if tab_id in tabs:
            _reject("JS_NAV_TABS", path, f"duplicate tab {tab_id}")
        tabs[tab_id] = label
        index = row_close + 1
        if index < closing:
            if tokens[index].value != ",":
                _reject("JS_NAV_TABS", path, "missing tab separator")
            index += 1
    return tabs


def project_keys_navigation_v1(raw: bytes) -> dict[str, object]:
    """Project a NAV_TABS declaration fingerprint; runtime UI operability stays unclaimed."""

    path = "tools/dex-ui/src/App.jsx"
    tokens = _tokenize_js_v1(raw, path)
    start = _top_level_declaration_v1(tokens, ("const", "NAV_TABS", "="), path)
    tabs = _parse_nav_tabs_v1(tokens, start + 3, path)
    if tabs.get("governance") != "Keys":
        _reject("JS_KEYS_PRESENTATION", path, "governance tab must retain the Keys label")
    return {
        "keys_component_id": "governance",
        "keys_label": "Keys",
        "navigation_tabs": [{"id": key, "label": value} for key, value in tabs.items()],
    }


def _source_row_v1(blob: _GitBlobV1) -> dict[str, str]:
    return {"path": blob.path, "sha256": blob.sha256}


def _route_registry_v1() -> list[dict[str, object]]:
    return [
        {
            "classification": classification,
            "route_id": route_id,
            "stream": stream,
            "supporting_surface_ids": list(surface_ids),
        }
        for route_id, classification, stream, surface_ids in ROUTE_ROWS_V1
    ]


def build_registry_artifact_v1(root: Path) -> dict[str, object]:
    """Build the registry from P's Git blobs, independent of live source."""

    resolved = _root_v1(root)
    subject = _git_commit_v1(resolved, IMPLEMENTATION_SUBJECT_COMMIT_V1)
    cache: dict[str, _GitBlobV1] = {}

    def blob(path: str) -> _GitBlobV1:
        existing = cache.get(path)
        if existing is not None:
            return existing
        captured = _git_blob_v1(resolved, subject, path)
        cache[path] = captured
        return captured

    def surface(
        surface_id: str,
        kind: str,
        source_path: str,
        projection: dict[str, object],
    ) -> dict[str, object]:
        return {
            "classification": SOURCE_BOUND_V1,
            "kind": kind,
            "projection": projection,
            "source": _source_row_v1(blob(source_path)),
            "surface_id": surface_id,
        }

    probe_specs: tuple[tuple[str, str, str, Callable[[bytes], dict[str, object]]], ...] = (
        ("api-server-startup-admission", "PYTHON_AST_STRUCTURAL_FINGERPRINT_V1", "src/integration/api_server.py", project_api_server_v1),
        ("local-route-quarantine-core", "PYTHON_AST_STRUCTURAL_FINGERPRINT_V1", "src/integration/local_route_quarantine.py", project_local_route_quarantine_v1),
        ("local-testnet-compose-profile", "YAML_SOURCE_FINGERPRINT_V1", "docker-compose.local-testnet.yml", project_compose_v1),
        ("local-testnet-lifecycle", "PYTHON_AST_STRUCTURAL_FINGERPRINT_V1", "tools/zenoctl_testnet_local/lifecycle.py", project_lifecycle_v1),
        ("ui-runtime-route-config", "JSON_SOURCE_FINGERPRINT_V1", "tools/dex-ui/public/zenodex-config.json", project_ui_config_v1),
        ("ui-runtime-route-presentation", "JAVASCRIPT_STRUCTURAL_FINGERPRINT_V1", "tools/dex-ui/src/lib/api.js", project_ui_runtime_guard_v1),
        ("ui-application-navigation", "JAVASCRIPT_STRUCTURAL_FINGERPRINT_V1", "tools/dex-ui/src/App.jsx", project_keys_navigation_v1),
    )
    surfaces = [
        surface(surface_id, kind, path, projector(blob(path).raw))
        for surface_id, kind, path, projector in probe_specs
    ]
    source_hashes = [_source_row_v1(cache[path]) for path in sorted(cache)]
    return {
        "authority": {
            "mount": "NONE",
            "production": "NONE",
            "release": "NONE",
            "settlement": "NONE",
            "value_movement": "NONE",
            "vm_gates_closed": [],
        },
        "evidence_model": {
            "claim_scope": "BOUNDED_PARTIAL_RESEARCH_EVIDENCE",
            "clean_descendant_required_for_replay": True,
            "expected_changed_paths": list(EVIDENCE_CHANGED_PATHS_V1),
            "implementation_source_reads": "PINNED_GIT_OBJECTS",
            "p2_split_debt": "DEFERRED_SINGLE_MODULE_HOTSPOT",
            "projector_assurance": "SOURCE_BOUND_STRUCTURAL_FINGERPRINTS_ONLY",
            "semantic_completeness": False,
        },
        "implementation_subject": {"git_commit": subject},
        "nonclaims": [
            "O-004 remains open: mounted-route liveness is not evaluated.",
            "Complete writer reachability is not evaluated.",
            "UI operability is not evaluated.",
            "No runtime receipt is present.",
            "Python and JavaScript projectors are source-bound structural fingerprints and do not establish live runtime semantics.",
            "Git executable integrity and escape-resistant process containment require an external trusted sandbox.",
            "This registry grants no mount, production, release, settlement, or value-moving authority.",
        ],
        "route_registry": _route_registry_v1(),
        "runtime_receipts": [],
        "schema": SCHEMA_V1,
        "source_hashes": source_hashes,
        "source_root_sha256": _sha256_v1(canonical_json_bytes_v1(source_hashes)),
        "surface_registry": sorted(surfaces, key=lambda row: cast(str, row["surface_id"])),
    }


def build_registry_bytes_v1(root: Path) -> bytes:
    return canonical_json_bytes_v1(build_registry_artifact_v1(root))


def _require_closed_non_authority_v1(artifact: dict[str, object]) -> None:
    expected_authority = {
        "mount": "NONE",
        "production": "NONE",
        "release": "NONE",
        "settlement": "NONE",
        "value_movement": "NONE",
        "vm_gates_closed": [],
    }
    if artifact.get("authority") != expected_authority:
        _reject("AUTHORITY_DRIFT", "authority", "all authority must remain closed")
    if artifact.get("runtime_receipts") != []:
        _reject("RUNTIME_RECEIPT_DRIFT", "runtime_receipts", "no executed receipt is admitted")
    routes = artifact.get("route_registry")
    if type(routes) is not list:
        _reject("ROUTE_REGISTRY_SHAPE", "route_registry", "must be a list")
    allowed = {SOURCE_BOUND_V1, QUARANTINED_V1, RETAINED_V1}
    if any(
        type(row) is not dict or cast(dict[str, object], row).get("classification") not in allowed
        for row in routes
    ):
        _reject("ROUTE_CLASSIFICATION", "route_registry", "authority-bearing classification")


def _report_base_v1(*, artifact_sha256: str, ok: bool) -> dict[str, object]:
    return {
        "artifact_sha256": artifact_sha256,
        "complete_writer_reachability": "NOT_EVALUATED",
        "dynamic_runtime_liveness": "NOT_EVALUATED",
        "evidence_replayable": False,
        "liveness_execution_verified": False,
        "mount_authority": "NONE",
        "mounted_routes": [],
        "o004_status": "OPEN_BOUNDED_PARTIAL_RESEARCH_EVIDENCE",
        "p2_split_debt": "DEFERRED_SINGLE_MODULE_HOTSPOT",
        "ok": ok,
        "production_authority": "NONE",
        "quarantined_streams": list(QUARANTINED_STREAMS_V1),
        "release_authority": "NONE",
        "runtime_receipts": [],
        "schema": CHECK_SCHEMA_V1,
        "settlement_authority": "NONE",
        "surface_registry_complete": False,
        "ui_operability": "NOT_EVALUATED",
        "value_movement_authority": "NONE",
        "vm_gates_closed": [],
    }


def _failure_report_v1(
    code: str,
    path: str,
    detail: str,
    artifact_sha256: str = "",
) -> dict[str, object]:
    return _report_base_v1(artifact_sha256=artifact_sha256, ok=False) | {
        "findings": [{"code": code, "detail": detail, "path": path}],
    }


def _success_report_v1(raw_artifact: bytes, checkout: dict[str, object]) -> dict[str, object]:
    return _report_base_v1(artifact_sha256=_sha256_v1(raw_artifact), ok=True) | {
        "evidence_checkout": checkout,
        "evidence_replayable": checkout["replayable"],
        "findings": [],
        "implementation_subject": IMPLEMENTATION_SUBJECT_COMMIT_V1,
    }


def check_registry_v1(root: Path, artifact_path: Path | None = None) -> dict[str, object]:
    """Check canonical bytes, the pinned P projection, and current P..E shape."""

    resolved = _root_v1(root)
    source = artifact_path if artifact_path is not None else resolved / ARTIFACT_RELATIVE_PATH_V1
    raw: bytes | None = None
    try:
        raw = read_artifact_file_v1(source)
        artifact = decode_json_object_v1(raw, "operator surface registry")
        if canonical_json_bytes_v1(artifact) != raw:
            _reject("NONCANONICAL_ARTIFACT", str(source), "artifact bytes are not canonical JSON")
        _require_closed_non_authority_v1(artifact)
        if artifact != build_registry_artifact_v1(resolved):
            _reject("ARTIFACT_PROJECTION_DRIFT", str(source), "artifact differs from P projection")
        checkout = classify_evidence_checkout_v1(resolved)
    except OperatorSurfaceRegistryRejectV1 as exc:
        return _failure_report_v1(
            exc.code,
            exc.path,
            exc.detail,
            "" if raw is None else _sha256_v1(raw),
        )
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return _failure_report_v1(
            "CHECKER_INPUT_ERROR",
            str(source),
            type(exc).__name__,
            "" if raw is None else _sha256_v1(raw),
        )
    return _success_report_v1(raw, checkout)
