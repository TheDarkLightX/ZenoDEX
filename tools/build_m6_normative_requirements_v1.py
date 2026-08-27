#!/usr/bin/env python3
"""Generate the exact source-pinned M6 normative requirements V1 artifacts."""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import selectors
import shutil
import signal
import stat
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Final, NoReturn

try:
    from tools.m6_normative_requirements_v1 import (
        MAX_JSON_BYTES_V1,
        SOURCE_PINS_V1,
        SOURCE_SUBJECT_COMMIT_V1,
        SOURCE_SUBJECT_TREE_V1,
        RequirementsRejectV1,
        SourceSnapshotV1,
        build_requirements_registry_v1,
        canonical_json_bytes_v1,
        render_registry_markdown_v1,
    )
except ModuleNotFoundError:
    from m6_normative_requirements_v1 import (  # type: ignore[no-redef]
        MAX_JSON_BYTES_V1,
        SOURCE_PINS_V1,
        SOURCE_SUBJECT_COMMIT_V1,
        SOURCE_SUBJECT_TREE_V1,
        RequirementsRejectV1,
        SourceSnapshotV1,
        build_requirements_registry_v1,
        canonical_json_bytes_v1,
        render_registry_markdown_v1,
    )


REPO_ROOT: Final = Path(__file__).resolve().parents[1]
JSON_OUTPUT: Final = Path("docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json")
MARKDOWN_OUTPUT: Final = Path("docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.md")
SOURCE_MAX_BYTES_V1: Final = MAX_JSON_BYTES_V1
ARTIFACT_MAX_BYTES_V1: Final = MAX_JSON_BYTES_V1
MARKDOWN_MAX_BYTES_V1: Final = 262_144
GIT_OUTPUT_MAX_BYTES_V1 = 65_536
GIT_TIMEOUT_SECONDS_V1 = 5.0
_READ_CHUNK_BYTES_V1: Final = 65_536
_SHELL_PATH_LIMIT_V1: Final = 256
_SHELL_DETAIL_LIMIT_V1: Final = 512


@dataclass(frozen=True)
class ShellRejectV1(ValueError):
    """Stable rejection for bounded filesystem or Git acquisition failures."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def _shell_reject(code: str, path: str, detail: str) -> NoReturn:
    def clean(value: str, limit: int) -> str:
        sanitized = "".join(
            character if ord(character) >= 32 and not 0xD800 <= ord(character) <= 0xDFFF else "?"
            for character in value
        )
        return sanitized if len(sanitized) <= limit else sanitized[: limit - 3] + "..."

    raise ShellRejectV1(
        clean(code, 64),
        clean(path, _SHELL_PATH_LIMIT_V1),
        clean(detail, _SHELL_DETAIL_LIMIT_V1),
    )


def _filesystem_reject_v1(prefix: str, path: str, exc: OSError) -> NoReturn:
    code_by_errno = {
        errno.EACCES: f"{prefix}_PERMISSION",
        errno.EINTR: f"{prefix}_INTERRUPTED",
        errno.ELOOP: f"{prefix}_SYMLINK",
        errno.ENAMETOOLONG: f"{prefix}_NAME_TOO_LONG",
        errno.EPERM: f"{prefix}_PERMISSION",
    }
    code = (
        code_by_errno.get(exc.errno, f"{prefix}_IO_ERROR")
        if exc.errno is not None
        else f"{prefix}_IO_ERROR"
    )
    _shell_reject(code, path, f"{type(exc).__name__}; errno={exc.errno}")


def _git_binary_v1() -> str:
    binary = shutil.which("git", path=os.defpath)
    if binary is None or not os.path.isabs(binary):
        _shell_reject("GIT_NOT_FOUND", "git", "absolute Git executable unavailable")
    return binary


def _git_environment_v1() -> dict[str, str]:
    return {
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "HOME": "/dev/null",
        "LC_ALL": "C",
        "PATH": os.defpath,
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
        except OSError:
            pass
        try:
            process.wait(timeout=1.0)
        except (OSError, subprocess.TimeoutExpired):
            pass


def _run_git_v1(
    root: Path,
    arguments: tuple[str, ...],
    *,
    allowed_statuses: frozenset[int] = frozenset({0}),
) -> tuple[int, str, str]:
    """Run fixed-argv Git with isolated configuration and bounded output/time."""

    root_text = os.path.abspath(os.fspath(root))
    argv = (
        _git_binary_v1(),
        "-c",
        "core.hooksPath=/dev/null",
        "-C",
        root_text,
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
        _shell_reject("GIT_EXEC_ERROR", "git", f"{type(exc).__name__}: {exc}")
    if process.stdout is None or process.stderr is None:
        _kill_and_wait_v1(process)
        _shell_reject("GIT_PIPE_ERROR", "git", "subprocess pipes were not created")

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
            for key, _ in selector.select(timeout=min(0.05, remaining)):
                try:
                    chunk = os.read(key.fd, _READ_CHUNK_BYTES_V1)
                except BlockingIOError:
                    continue
                except OSError as exc:
                    _kill_and_wait_v1(process)
                    _shell_reject("GIT_IO_ERROR", "git", f"{type(exc).__name__}; errno={exc.errno}")
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                total += len(chunk)
                if total > GIT_OUTPUT_MAX_BYTES_V1:
                    _kill_and_wait_v1(process)
                    _shell_reject(
                        "GIT_OUTPUT_LIMIT", "git", "combined Git output exceeded byte ceiling"
                    )
                output[str(key.data)].extend(chunk)
        try:
            status = process.wait(timeout=max(0.01, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            _kill_and_wait_v1(process)
            _shell_reject("GIT_TIMEOUT", "git", "Git command exceeded time ceiling")
    except ShellRejectV1:
        raise
    except OSError as exc:
        _kill_and_wait_v1(process)
        _shell_reject("GIT_IO_ERROR", "git", f"{type(exc).__name__}; errno={exc.errno}")
    finally:
        try:
            selector.close()
        except OSError:
            pass
        try:
            process.stdout.close()
        except OSError:
            pass
        try:
            process.stderr.close()
        except OSError:
            pass

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
    _, stdout, _ = _run_git_v1(root, arguments)
    value = stdout.strip()
    if "\n" in value or "\x00" in value or not value:
        _shell_reject("GIT_RESULT", label, "expected one nonempty scalar result")
    return value


def _git_head_v1(root: Path) -> str:
    return _git_scalar_v1(root, ("rev-parse", "--verify", "HEAD^{commit}"), "HEAD")


def _git_tree_v1(root: Path, commit: str) -> str:
    return _git_scalar_v1(
        root, ("rev-parse", "--verify", f"{commit}^{{tree}}"), "source subject tree"
    )


def _git_is_ancestor_v1(root: Path, ancestor: str, descendant: str) -> bool:
    status, stdout, stderr = _run_git_v1(
        root,
        ("merge-base", "--is-ancestor", ancestor, descendant),
        allowed_statuses=frozenset({0, 1}),
    )
    if stdout or stderr:
        _shell_reject("GIT_RESULT", "ancestry", "ancestry check emitted unexpected output")
    return status == 0


def _git_tree_entry_v1(root: Path, commit: str, path: str) -> tuple[str, str, str, str]:
    _, stdout, stderr = _run_git_v1(root, ("ls-tree", "-z", "--full-tree", commit, "--", path))
    if stderr or not stdout.endswith("\x00") or stdout.count("\x00") != 1:
        _shell_reject("GIT_TREE_ENTRY", path, "expected exactly one NUL-terminated tree entry")
    record = stdout[:-1]
    if "\t" not in record:
        _shell_reject("GIT_TREE_ENTRY", path, "tree entry lacks path separator")
    metadata, recorded_path = record.split("\t", 1)
    parts = metadata.split(" ")
    if len(parts) != 3 or recorded_path != path:
        _shell_reject("GIT_TREE_ENTRY", path, "path or metadata shape drift")
    mode, object_type, blob = parts
    return (recorded_path, mode, object_type, blob)


def _open_parent_dir_v1(path: Path) -> tuple[int, str]:
    absolute = Path(os.path.abspath(os.fspath(path)))
    parts = absolute.parts
    if len(parts) < 2 or parts[0] != os.sep or parts[-1] in {"", ".", ".."}:
        _shell_reject("FILE_PATH", str(path), "path must name an absolute file")
    flags = os.O_RDONLY | os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        directory_fd = os.open(os.sep, flags)
    except OSError as exc:
        _filesystem_reject_v1("FILE", str(path), exc)
    try:
        for component in parts[1:-1]:
            if component in {"", ".", ".."}:
                _shell_reject("FILE_PATH", str(path), "unsafe path component")
            try:
                component_stat = os.stat(component, dir_fd=directory_fd, follow_symlinks=False)
                if stat.S_ISLNK(component_stat.st_mode):
                    _shell_reject("FILE_PARENT_SYMLINK", str(path), "symlinked parent rejected")
                if not stat.S_ISDIR(component_stat.st_mode):
                    _shell_reject("FILE_PARENT_REJECTED", str(path), "parent is not a directory")
                next_fd = os.open(component, flags, dir_fd=directory_fd)
            except ShellRejectV1:
                raise
            except OSError as exc:
                _filesystem_reject_v1("FILE", str(path), exc)
            previous_fd = directory_fd
            try:
                os.close(previous_fd)
            except OSError as exc:
                directory_fd = -1
                try:
                    os.close(next_fd)
                except OSError:
                    pass
                _filesystem_reject_v1("FILE", str(path), exc)
            directory_fd = next_fd
        return directory_fd, parts[-1]
    except BaseException:
        try:
            os.close(directory_fd)
        except OSError:
            pass
        raise


def _read_bounded_regular_file_v1(path: Path, max_bytes: int, role: str) -> bytes:
    """Read once through no-follow descriptors after regular-file and size checks."""

    if type(max_bytes) is not int or max_bytes < 0:
        _shell_reject("FILE_LIMIT_TYPE", role, "byte ceiling must be a nonnegative exact int")
    directory_fd, name = _open_parent_dir_v1(path)
    file_fd = -1
    try:
        try:
            before = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
        except FileNotFoundError:
            _shell_reject("FILE_NOT_FOUND", role, str(path))
        except OSError as exc:
            _filesystem_reject_v1("FILE", role, exc)
        if stat.S_ISLNK(before.st_mode):
            _shell_reject("FILE_SYMLINK", role, str(path))
        if not stat.S_ISREG(before.st_mode):
            _shell_reject("FILE_NONREGULAR", role, str(path))
        if before.st_size > max_bytes:
            _shell_reject("FILE_SIZE_LIMIT", role, f"{before.st_size}>{max_bytes}")
        flags = os.O_RDONLY
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        try:
            file_fd = os.open(name, flags, dir_fd=directory_fd)
        except OSError as exc:
            _filesystem_reject_v1("FILE", role, exc)
        opened = os.fstat(file_fd)
        if (
            not stat.S_ISREG(opened.st_mode)
            or opened.st_dev != before.st_dev
            or opened.st_ino != before.st_ino
            or opened.st_size != before.st_size
        ):
            _shell_reject("FILE_CHANGED", role, "file identity changed before read")
        buffer = bytearray(opened.st_size)
        offset = 0
        while offset < opened.st_size:
            try:
                chunk = os.read(file_fd, min(_READ_CHUNK_BYTES_V1, opened.st_size - offset))
            except OSError as exc:
                _filesystem_reject_v1("FILE", role, exc)
            if not chunk:
                _shell_reject("FILE_CHANGED", role, "file shrank during read")
            buffer[offset : offset + len(chunk)] = chunk
            offset += len(chunk)
        try:
            extra = os.read(file_fd, 1)
        except OSError as exc:
            _filesystem_reject_v1("FILE", role, exc)
        if extra:
            _shell_reject("FILE_CHANGED", role, "file grew during read")
        after = os.fstat(file_fd)
        if (
            after.st_dev != opened.st_dev
            or after.st_ino != opened.st_ino
            or after.st_size != opened.st_size
        ):
            _shell_reject("FILE_CHANGED", role, "file changed during read")
        return bytes(buffer)
    except ShellRejectV1:
        raise
    except OSError as exc:
        _filesystem_reject_v1("FILE", role, exc)
    finally:
        if file_fd >= 0:
            try:
                os.close(file_fd)
            except OSError:
                pass
        try:
            os.close(directory_fd)
        except OSError:
            pass


def _validate_output_target_v1(directory_fd: int, name: str, path: Path) -> None:
    try:
        current = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    except OSError as exc:
        _filesystem_reject_v1("OUTPUT", str(path), exc)
    if stat.S_ISLNK(current.st_mode):
        _shell_reject("OUTPUT_SYMLINK", str(path), "refusing to replace symlink")
    if not stat.S_ISREG(current.st_mode):
        _shell_reject("OUTPUT_NONREGULAR", str(path), "refusing to replace nonregular output")


def _atomic_replace_regular_file_v1(path: Path, data: bytes) -> None:
    """Replace one file under the research-only trusted-directory premise.

    The temporary descriptor remains open across rename.  Inode, type, and
    bytes are checked before and after the linearization point.  This detects
    substitution; it cannot protect a directory writable by the same OS
    authority as this process.
    """

    if type(data) is not bytes:
        _shell_reject("OUTPUT_BYTES_TYPE", str(path), "output must have exact bytes type")
    directory_fd, name = _open_parent_dir_v1(path)
    temporary_name: str | None = None
    temporary_fd = -1
    try:
        _validate_output_target_v1(directory_fd, name, path)
        flags = os.O_RDWR | os.O_CREAT | os.O_EXCL
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        for ordinal in range(128):
            candidate = f".{name}.tmp.{os.getpid()}.{ordinal}"
            try:
                temporary_fd = os.open(candidate, flags, 0o644, dir_fd=directory_fd)
                temporary_name = candidate
                break
            except FileExistsError:
                continue
            except OSError as exc:
                _filesystem_reject_v1("OUTPUT", str(path), exc)
        if temporary_name is None or temporary_fd < 0:
            _shell_reject("OUTPUT_TEMP_EXHAUSTED", str(path), "no exclusive temp name available")
        view = memoryview(data)
        written = 0
        while written < len(view):
            try:
                count = os.write(temporary_fd, view[written:])
            except OSError as exc:
                _filesystem_reject_v1("OUTPUT", str(path), exc)
            if count <= 0:
                _shell_reject("OUTPUT_WRITE_ERROR", str(path), "short write")
            written += count
        try:
            os.fsync(temporary_fd)
            descriptor_before = os.fstat(temporary_fd)
            path_before = os.stat(temporary_name, dir_fd=directory_fd, follow_symlinks=False)
        except OSError as exc:
            _filesystem_reject_v1("OUTPUT", str(path), exc)
        if (
            not stat.S_ISREG(descriptor_before.st_mode)
            or not stat.S_ISREG(path_before.st_mode)
            or descriptor_before.st_dev != path_before.st_dev
            or descriptor_before.st_ino != path_before.st_ino
            or descriptor_before.st_size != len(data)
        ):
            _shell_reject(
                "OUTPUT_TEMP_BINDING_MISMATCH", str(path), "temp name and descriptor differ"
            )
        _validate_output_target_v1(directory_fd, name, path)
        try:
            os.replace(
                temporary_name,
                name,
                src_dir_fd=directory_fd,
                dst_dir_fd=directory_fd,
            )
        except OSError as exc:
            _filesystem_reject_v1("OUTPUT", str(path), exc)
        temporary_name = None
        try:
            destination = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            descriptor_after = os.fstat(temporary_fd)
        except OSError as exc:
            _filesystem_reject_v1("OUTPUT", str(path), exc)
        if (
            not stat.S_ISREG(destination.st_mode)
            or not stat.S_ISREG(descriptor_after.st_mode)
            or destination.st_dev != descriptor_after.st_dev
            or destination.st_ino != descriptor_after.st_ino
        ):
            _shell_reject(
                "OUTPUT_SUBSTITUTION_RACE", str(path), "destination is not the written inode"
            )
        try:
            os.lseek(temporary_fd, 0, os.SEEK_SET)
            observed = bytearray()
            while len(observed) <= len(data):
                chunk = os.read(
                    temporary_fd,
                    min(_READ_CHUNK_BYTES_V1, len(data) + 1 - len(observed)),
                )
                if not chunk:
                    break
                observed.extend(chunk)
            os.fsync(directory_fd)
        except OSError as exc:
            _filesystem_reject_v1("OUTPUT", str(path), exc)
        if bytes(observed) != data:
            _shell_reject("OUTPUT_BYTE_MISMATCH", str(path), "post-rename bytes differ")
    except ShellRejectV1:
        raise
    except OSError as exc:
        _filesystem_reject_v1("OUTPUT", str(path), exc)
    finally:
        if temporary_fd >= 0:
            try:
                os.close(temporary_fd)
            except OSError:
                pass
        if temporary_name is not None:
            try:
                os.unlink(temporary_name, dir_fd=directory_fd)
            except OSError:
                pass
        try:
            os.close(directory_fd)
        except OSError:
            pass


def load_source_snapshot_v1(root: Path) -> SourceSnapshotV1:
    """Acquire exact source bytes and immutable Git tree bindings."""

    captured_head = _git_head_v1(root)
    source_tree = _git_tree_v1(root, SOURCE_SUBJECT_COMMIT_V1)
    if source_tree != SOURCE_SUBJECT_TREE_V1:
        _shell_reject("SOURCE_SUBJECT_TREE", "Git", "immutable source subject tree drift")
    ancestry = _git_is_ancestor_v1(root, SOURCE_SUBJECT_COMMIT_V1, captured_head)
    source_entries = tuple(
        _git_tree_entry_v1(root, SOURCE_SUBJECT_COMMIT_V1, pin.path) for pin in SOURCE_PINS_V1
    )
    current_entries = tuple(
        _git_tree_entry_v1(root, captured_head, pin.path) for pin in SOURCE_PINS_V1
    )
    documents = tuple(
        (
            pin.path,
            _read_bounded_regular_file_v1(root / pin.path, SOURCE_MAX_BYTES_V1, pin.path),
        )
        for pin in SOURCE_PINS_V1
    )
    rechecked_head = _git_head_v1(root)
    return SourceSnapshotV1(
        captured_git_head=captured_head,
        rechecked_git_head=rechecked_head,
        source_subject_tree=source_tree,
        source_subject_is_ancestor=ancestry,
        document_bytes=documents,
        source_subject_entries=source_entries,
        current_head_entries=current_entries,
    )


def build_artifacts_v1(root: Path) -> tuple[bytes, str]:
    """Build both rendered forms from one pure registry value."""

    registry = build_requirements_registry_v1(load_source_snapshot_v1(root))
    return canonical_json_bytes_v1(registry.to_json()), render_registry_markdown_v1(registry)


def write_artifacts_v1(root: Path) -> dict[str, str]:
    """Write only the two fixed generated artifacts owned by this generator."""

    json_bytes, markdown = build_artifacts_v1(root)
    markdown_bytes = markdown.encode("utf-8")
    _atomic_replace_regular_file_v1(root / JSON_OUTPUT, json_bytes)
    _atomic_replace_regular_file_v1(root / MARKDOWN_OUTPUT, markdown_bytes)
    return {
        "json_sha256": hashlib.sha256(json_bytes).hexdigest(),
        "json_path": str(JSON_OUTPUT),
        "markdown_path": str(MARKDOWN_OUTPUT),
    }


def _write_built_artifacts_v1(root: Path, json_bytes: bytes, markdown: str) -> dict[str, str]:
    markdown_bytes = markdown.encode("utf-8")
    _atomic_replace_regular_file_v1(root / JSON_OUTPUT, json_bytes)
    _atomic_replace_regular_file_v1(root / MARKDOWN_OUTPUT, markdown_bytes)
    return {
        "json_sha256": hashlib.sha256(json_bytes).hexdigest(),
        "json_path": str(JSON_OUTPUT),
        "markdown_path": str(MARKDOWN_OUTPUT),
    }


def _failure_payload_v1(exc: ShellRejectV1 | RequirementsRejectV1) -> dict[str, object]:
    return {
        "finding": {"code": exc.code, "detail": exc.detail, "path": exc.path},
        "ok": False,
        "production_authority": "NONE",
        "schema": "zenodex/m6-normative-requirements-build/v1",
        "settlement_authority": "NONE",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        json_bytes, markdown = build_artifacts_v1(args.root)
        json_path = args.root / JSON_OUTPUT
        markdown_path = args.root / MARKDOWN_OUTPUT
        if args.check:
            actual_json = _read_bounded_regular_file_v1(
                json_path, ARTIFACT_MAX_BYTES_V1, "generated JSON artifact"
            )
            actual_markdown = _read_bounded_regular_file_v1(
                markdown_path, MARKDOWN_MAX_BYTES_V1, "generated Markdown artifact"
            )
            ok = actual_json == json_bytes and actual_markdown == markdown.encode("utf-8")
            print(
                json.dumps(
                    {
                        "ok": ok,
                        "production_authority": "NONE",
                        "schema": "zenodex/m6-normative-requirements-build/v1",
                        "settlement_authority": "NONE",
                    },
                    sort_keys=True,
                )
            )
            return 0 if ok else 1
        result = _write_built_artifacts_v1(args.root, json_bytes, markdown)
        print(
            json.dumps(
                {
                    **result,
                    "ok": True,
                    "production_authority": "NONE",
                    "schema": "zenodex/m6-normative-requirements-build/v1",
                    "settlement_authority": "NONE",
                },
                sort_keys=True,
            )
        )
        return 0
    except (ShellRejectV1, RequirementsRejectV1) as exc:
        print(json.dumps(_failure_payload_v1(exc), sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
