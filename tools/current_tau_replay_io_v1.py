"""Bounded filesystem and offline Git shell for current-Tau evidence replay."""

from __future__ import annotations

import argparse
import errno
import importlib.machinery
import os
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from types import FunctionType, ModuleType
from typing import Final, NoReturn

GIT_OUTPUT_MAX_BYTES_V1: Final = 262_144
GIT_TIMEOUT_SECONDS_V1: Final = 5.0
_READ_CHUNK_BYTES_V1: Final = 65_536


@dataclass(frozen=True)
class ShellRejectV1(ValueError):
    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


class FailClosedArgumentParserV1(argparse.ArgumentParser):
    """Translate invalid CLI syntax into the typed no-authority envelope."""

    def error(self, message: str) -> NoReturn:
        _shell_reject("CLI_INPUT", "arguments", "invalid command-line arguments")


def _shell_reject(code: str, path: str, detail: str) -> NoReturn:
    raise ShellRejectV1(code[:64], path[:256], detail[:512])


def _filesystem_reject_v1(prefix: str, path: Path, exc: OSError) -> NoReturn:
    suffix_by_errno = {
        errno.EACCES: "PERMISSION",
        errno.ELOOP: "SYMLINK",
        errno.ENOENT: "MISSING",
        errno.ENOTDIR: "PARENT",
        errno.EPERM: "PERMISSION",
    }
    suffix = suffix_by_errno.get(exc.errno, "IO_ERROR") if exc.errno is not None else "IO_ERROR"
    _shell_reject(f"{prefix}_{suffix}", str(path), f"{type(exc).__name__}; errno={exc.errno}")


def _unbound_runtime_repository_imports_v1(
    root: Path,
    allowed_paths: tuple[str, ...],
) -> tuple[str, ...]:
    """Return exact repository modules executing outside the source manifest."""

    try:
        resolved_root = root.resolve(strict=True)
    except OSError as exc:
        _filesystem_reject_v1("RUNTIME_ROOT", root, exc)
    allowed = frozenset(allowed_paths)
    observed: set[str] = set()
    for module in tuple(sys.modules.values()):
        if type(module) is not ModuleType:
            continue
        candidates: set[str] = set()
        path_value = module.__dict__.get("__file__")
        if type(path_value) is str:
            candidates.add(path_value)
        spec = module.__dict__.get("__spec__")
        if type(spec) is importlib.machinery.ModuleSpec and type(spec.origin) is str:
            candidates.add(spec.origin)
        for value in tuple(module.__dict__.values()):
            if type(value) is FunctionType and type(value.__code__.co_filename) is str:
                candidates.add(value.__code__.co_filename)
            if type(value) is not type or value.__dict__.get("__module__") != module.__name__:
                continue
            for class_value in tuple(value.__dict__.values()):
                if (
                    type(class_value) is FunctionType
                    and type(class_value.__code__.co_filename) is str
                ):
                    candidates.add(class_value.__code__.co_filename)
        for candidate in candidates:
            try:
                relative = Path(candidate).resolve(strict=True).relative_to(resolved_root)
            except (OSError, ValueError):
                continue
            observed.add(relative.as_posix())
    return tuple(sorted(observed - allowed))


def _git_binary_v1() -> str:
    binary = shutil.which("git", path=os.defpath)
    if binary is None or not os.path.isabs(binary):
        _shell_reject("GIT_NOT_FOUND", "git", "absolute Git executable unavailable")
    return binary


def _git_environment_v1() -> dict[str, str]:
    return {
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "LC_ALL": "C",
        "PATH": os.defpath,
        "XDG_CONFIG_HOME": os.devnull,
    }


def _kill_and_wait_v1(process: subprocess.Popen[bytes]) -> None:
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


def _run_git_v1(
    root: Path,
    arguments: tuple[str, ...],
    *,
    allowed_statuses: frozenset[int] = frozenset({0}),
) -> tuple[int, str, str]:
    """Run fixed-argv Git with no lazy fetch and bounded output/time."""

    argv = (
        _git_binary_v1(),
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "core.fsmonitor=false",
        "-C",
        os.path.abspath(os.fspath(root)),
        *arguments,
    )
    try:
        process = subprocess.Popen(
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=_git_environment_v1(),
            start_new_session=True,
        )
    except OSError as exc:
        _shell_reject("GIT_EXEC_ERROR", "git", type(exc).__name__)
    if process.stdout is None or process.stderr is None:
        _kill_and_wait_v1(process)
        _shell_reject("GIT_PIPE_ERROR", "git", "subprocess pipes unavailable")
    output = {"stdout": bytearray(), "stderr": bytearray()}
    selector = selectors.DefaultSelector()
    deadline = time.monotonic() + GIT_TIMEOUT_SECONDS_V1
    total = 0
    try:
        selector.register(process.stdout, selectors.EVENT_READ, "stdout")
        selector.register(process.stderr, selectors.EVENT_READ, "stderr")
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                _kill_and_wait_v1(process)
                _shell_reject("GIT_TIMEOUT", "git", "Git command exceeded time ceiling")
            for key, _mask in selector.select(timeout=min(0.05, remaining)):
                chunk = os.read(key.fd, _READ_CHUNK_BYTES_V1)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                total += len(chunk)
                if total > GIT_OUTPUT_MAX_BYTES_V1:
                    _kill_and_wait_v1(process)
                    _shell_reject("GIT_OUTPUT_LIMIT", "git", "combined output exceeded ceiling")
                output[str(key.data)].extend(chunk)
        status = process.wait(timeout=max(0.01, deadline - time.monotonic()))
    except ShellRejectV1:
        raise
    except (OSError, subprocess.TimeoutExpired) as exc:
        _kill_and_wait_v1(process)
        _shell_reject("GIT_IO_ERROR", "git", type(exc).__name__)
    finally:
        selector.close()
        process.stdout.close()
        process.stderr.close()
    try:
        stdout = bytes(output["stdout"]).decode("utf-8")
        stderr = bytes(output["stderr"]).decode("utf-8")
    except UnicodeDecodeError as exc:
        _shell_reject("GIT_UTF8", "git", f"invalid UTF-8 at byte {exc.start}")
    if status not in allowed_statuses:
        detail = stderr.strip()[:512] or f"exit status {status}"
        _shell_reject("GIT_EXIT", "git", detail)
    return status, stdout, stderr


def _git_scalar_v1(root: Path, arguments: tuple[str, ...], label: str) -> str:
    _, stdout, stderr = _run_git_v1(root, arguments)
    value = stdout.strip()
    if stderr or not value or "\n" in value or "\x00" in value:
        _shell_reject("GIT_RESULT", label, "expected one clean nonempty scalar")
    return value


def _git_head_v1(root: Path) -> str:
    return _git_scalar_v1(root, ("rev-parse", "--verify", "HEAD^{commit}"), "HEAD")


def _git_tree_v1(root: Path, commit: str) -> str:
    return _git_scalar_v1(
        root, ("rev-parse", "--verify", f"{commit}^{{tree}}"), "source tree"
    )


def _git_is_ancestor_v1(root: Path, ancestor: str, descendant: str) -> bool:
    status, stdout, stderr = _run_git_v1(
        root,
        ("merge-base", "--is-ancestor", ancestor, descendant),
        allowed_statuses=frozenset({0, 1}),
    )
    if stdout or stderr:
        _shell_reject("GIT_RESULT", "ancestry", "unexpected ancestry output")
    return status == 0


def _require_safe_path_v1(path: Path) -> Path:
    absolute = Path(os.path.abspath(os.fspath(path)))
    current = Path(absolute.root)
    for component in absolute.parts[1:-1]:
        current /= component
        try:
            metadata = os.lstat(current)
        except OSError as exc:
            _filesystem_reject_v1("FILE", path, exc)
        if stat.S_ISLNK(metadata.st_mode):
            _shell_reject("FILE_PARENT_SYMLINK", str(path), str(current))
        if not stat.S_ISDIR(metadata.st_mode):
            _shell_reject("FILE_PARENT_REJECTED", str(path), str(current))
    return absolute


def _read_bounded_regular_file_v1(path: Path, max_bytes: int, label: str) -> bytes:
    absolute = _require_safe_path_v1(path)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(absolute, flags)
    except OSError as exc:
        _filesystem_reject_v1("FILE", path, exc)
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            _shell_reject("FILE_NOT_REGULAR", str(path), label)
        if metadata.st_size > max_bytes:
            _shell_reject("FILE_SIZE_LIMIT", str(path), label)
        output = bytearray()
        while len(output) <= max_bytes:
            chunk = os.read(descriptor, min(_READ_CHUNK_BYTES_V1, max_bytes + 1 - len(output)))
            if not chunk:
                break
            output.extend(chunk)
        if len(output) > max_bytes:
            _shell_reject("FILE_SIZE_LIMIT", str(path), label)
        return bytes(output)
    except OSError as exc:
        _filesystem_reject_v1("FILE", path, exc)
    finally:
        os.close(descriptor)


def _atomic_replace_regular_file_v1(path: Path, data: bytes) -> None:
    absolute = _require_safe_path_v1(path)
    parent = absolute.parent
    try:
        descriptor, temporary = tempfile.mkstemp(prefix=f".{absolute.name}.", dir=parent)
    except OSError as exc:
        _filesystem_reject_v1("WRITE", path, exc)
    try:
        with os.fdopen(descriptor, "wb", closefd=True) as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temporary, 0o644)
        os.replace(temporary, absolute)
        directory = os.open(parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except OSError as exc:
        try:
            os.unlink(temporary)
        except OSError:
            pass
        _filesystem_reject_v1("WRITE", path, exc)
