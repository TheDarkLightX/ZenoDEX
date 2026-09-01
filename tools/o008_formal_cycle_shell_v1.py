#!/usr/bin/env python3
"""Imperative shell for the O-008 formal-cycle admission checker.

Everything with an effect lives here: a read-only Git port, worktree byte reads,
hashing of the executing tool sources, and the proof-replay runner. The shell
produces plain values consumed by the pure core in
``tools/o008_formal_cycle_admission_v1.py`` and never decides admission itself.
"""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Final

if str(Path(__file__).resolve().parents[1]) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import o008_formal_cycle_admission_v1 as core
from tools import scan_lean_proof_placeholders_v1 as scanner

GIT_ENV_V1: Final[dict[str, str]] = {
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_NO_REPLACE_OBJECTS": "1",
    "GIT_OPTIONAL_LOCKS": "0",
    "GIT_NO_LAZY_FETCH": "1",
    "GIT_LITERAL_PATHSPECS": "1",
    "HOME": "/nonexistent",
    "LANG": "C",
    "LC_ALL": "C",
    "PATH": "/usr/bin:/bin",
}
GIT_TIMEOUT_SECONDS_V1: Final = 20
REPLAY_TOOLS_V1: Final[tuple[str, ...]] = ("cargo", "rustc", "lake", "lean")
REPLAY_FIXED_ENV_V1: Final[dict[str, str]] = {
    "LANG": "C.UTF-8",
    "LC_ALL": "C.UTF-8",
    "PYTHONDONTWRITEBYTECODE": "1",
    "PYTHONHASHSEED": "0",
}
REPLAY_CARGO_ENV_V1: Final[dict[str, str]] = {"CARGO_INCREMENTAL": "0", "CARGO_BUILD_JOBS": "8"}


@dataclass(frozen=True, slots=True)
class GitReadPortV1:
    """Read-only Git access with a fixed environment and bounded run time."""

    root: Path

    def _invoke(self, *args: str) -> subprocess.CompletedProcess[bytes]:
        try:
            return subprocess.run(
                (
                    "git",
                    "--no-replace-objects",
                    "-c",
                    "core.fsmonitor=false",
                    "-c",
                    "core.hooksPath=/dev/null",
                    "-c",
                    "core.attributesFile=/dev/null",
                    "-C",
                    str(self.root),
                    *args,
                ),
                check=False,
                capture_output=True,
                stdin=subprocess.DEVNULL,
                env=dict(GIT_ENV_V1),
                timeout=GIT_TIMEOUT_SECONDS_V1,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            core._reject("INFRA_GIT_COMMAND", "git", f"{args[0]}: {type(exc).__name__}")

    def run(self, *args: str) -> bytes:
        result = self._invoke(*args)
        if result.returncode != 0 or result.stderr:
            core._reject("INFRA_GIT_COMMAND", "git", f"{args[0]} failed")
        return result.stdout

    def succeeds(self, *args: str) -> bool:
        return self._invoke(*args).returncode == 0


def resolve_repo_root_v1(root: Path) -> Path:
    if not root.is_absolute():
        core._reject("INFRA_ROOT_UNRESOLVABLE", str(root), "absolute --root required")
    try:
        resolved = root.resolve(strict=True)
    except OSError as exc:
        core._reject("INFRA_ROOT_UNRESOLVABLE", str(root), type(exc).__name__)
    if not resolved.is_dir():
        core._reject("INFRA_ROOT_UNRESOLVABLE", str(root), "not a directory")
    top = GitReadPortV1(resolved).run("rev-parse", "--show-toplevel").decode("utf-8").strip()
    try:
        if Path(top).resolve(strict=True) != resolved:
            core._reject("INFRA_ROOT_NOT_TOPLEVEL", str(root), top)
    except OSError as exc:
        core._reject("INFRA_ROOT_UNRESOLVABLE", str(root), type(exc).__name__)
    return resolved


def _oid(raw: bytes, context: str) -> str:
    text = raw.decode("ascii", "replace").strip()
    if core._HEX40_RE.fullmatch(text) is None:
        core._reject("INFRA_GIT_COMMAND", context, "malformed object id")
    return text


def head_commit_v1(git: GitReadPortV1) -> str:
    return _oid(git.run("rev-parse", "--verify", "HEAD^{commit}"), "HEAD")


def validate_commit_v1(git: GitReadPortV1, commit: str, context: str) -> str:
    if core._HEX40_RE.fullmatch(commit) is None:
        core._reject("SUBJECT_COMMIT_INVALID", context, "full lowercase commit hash required")
    if not git.succeeds("rev-parse", "--verify", f"{commit}^{{commit}}"):
        core._reject("SUBJECT_COMMIT_UNAVAILABLE", context, commit)
    actual = _oid(git.run("rev-parse", "--verify", f"{commit}^{{commit}}"), context)
    if actual != commit:
        core._reject("SUBJECT_COMMIT_INVALID", context, "does not resolve to its exact hash")
    return commit


def parents_v1(git: GitReadPortV1, commit: str) -> tuple[str, ...]:
    tokens = git.run("rev-list", "--parents", "-n", "1", commit).decode("ascii", "replace").split()
    if not tokens or tokens[0] != commit:
        core._reject("INFRA_GIT_COMMAND", commit, "rev-list --parents mismatch")
    return tuple(_oid(token.encode("ascii"), commit) for token in tokens[1:])


def tree_entry_v1(git: GitReadPortV1, commit: str, path: str) -> tuple[str, str] | None:
    """Return (mode, blob oid) for ``path`` at ``commit`` or None when absent."""

    raw = git.run("ls-tree", "-z", "--full-tree", commit, "--", path)
    rows = [row for row in raw.split(b"\0") if row]
    if not rows:
        return None
    if len(rows) != 1 or b"\t" not in rows[0]:
        core._reject("INFRA_GIT_COMMAND", path, "ambiguous tree entry")
    metadata, raw_path = rows[0].split(b"\t", 1)
    mode, object_type, oid = metadata.decode("ascii", "replace").split(" ")
    if raw_path.decode("utf-8", "replace") != path or object_type != "blob":
        core._reject("SOURCE_PIN_MODE_DRIFT", path, f"{object_type} is not a blob")
    return mode, _oid(oid.encode("ascii"), path)


def read_blob_v1(git: GitReadPortV1, oid: str, path: str) -> bytes:
    size = int(git.run("cat-file", "-s", oid).decode("ascii", "replace").strip())
    if size > core.MAX_SOURCE_BLOB_BYTES_V1:
        core._reject("SOURCE_BLOB_BYTE_CEILING", path, str(size))
    data = git.run("cat-file", "blob", oid)
    if len(data) != size:
        core._reject("INFRA_GIT_COMMAND", path, "blob size changed while reading")
    return data


def read_subject_snapshot_v1(git: GitReadPortV1, subject_commit: str) -> core.SubjectSnapshotV1:
    validate_commit_v1(git, subject_commit, "subject_commit")
    parents = parents_v1(git, subject_commit)
    if len(parents) != 1:
        core._reject("SUBJECT_PARENT_TOPOLOGY", subject_commit, f"{len(parents)} parents")
    tree = _oid(git.run("rev-parse", f"{subject_commit}^{{tree}}"), subject_commit)
    blobs: dict[str, core.SourceBlobV1] = {}
    for path in core.SOURCE_PIN_PATHS_V1:
        entry = tree_entry_v1(git, subject_commit, path)
        if entry is None:
            continue
        mode, oid = entry
        data = read_blob_v1(git, oid, path)
        blobs[path] = _source_blob(path, mode, oid, data)
    forbidden = tuple(
        path for path in core.CARGO_CONFIG_FORBIDDEN_PATHS_V1 if tree_entry_v1(git, subject_commit, path) is not None
    )
    return core.SubjectSnapshotV1(
        subject_commit, parents[0], tree, blobs, _read_hygiene_packets(git, subject_commit), forbidden
    )


def _source_blob(path: str, mode: str, oid: str, data: bytes) -> core.SourceBlobV1:
    return core.SourceBlobV1(
        path=path, mode=mode, git_blob=oid, sha256=core.sha256_hex_v1(data), size=len(data), data=data
    )


def _read_hygiene_packets(git: GitReadPortV1, commit: str) -> dict[str, core.SourceBlobV1]:
    """Read every ``*.json`` regular file under the hygiene evidence directory at the commit."""

    raw = git.run("ls-tree", "-z", "--full-tree", commit, "--", core.HYGIENE_EVIDENCE_DIR_V1 + "/")
    packets: dict[str, core.SourceBlobV1] = {}
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        meta, _, path_bytes = entry.partition(b"\t")
        parts = meta.decode("ascii", errors="replace").split()
        path = path_bytes.decode("utf-8", errors="replace")
        if len(parts) != 3 or parts[1] != "blob" or not path.endswith(".json"):
            continue
        if parts[0] != core.GIT_BLOB_MODE_V1:
            core._reject("SOURCE_PIN_MODE_DRIFT", path, parts[0])
        data = read_blob_v1(git, parts[2], path)
        packets[path] = _source_blob(path, parts[0], parts[2], data)
    return packets


def working_bytes_v1(root: Path, path: str) -> bytes | None:
    """Return regular-file bytes under the size ceiling, or None (missing, symlink, oversize)."""

    target = root / path
    try:
        metadata = target.lstat()
    except OSError:
        return None
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > core.MAX_SOURCE_BLOB_BYTES_V1:
        return None
    try:
        raw = target.read_bytes()
    except OSError:
        return None
    return raw if len(raw) == metadata.st_size else None


def blob_at_v1(git: GitReadPortV1, commit: str, path: str) -> bytes | None:
    entry = tree_entry_v1(git, commit, path)
    if entry is None:
        return None
    return read_blob_v1(git, entry[1], path)


def _write_set_v1(git: GitReadPortV1, parent: str, commit: str) -> tuple[tuple[str, str], ...]:
    raw = git.run(
        "diff-tree", "--no-commit-id", "--name-status", "--no-renames", "-r", "-z", parent, commit
    )
    parts = [part for part in raw.split(b"\0") if part]
    if len(parts) % 2:
        core._reject("INFRA_GIT_COMMAND", commit, "malformed name-status output")
    rows = [
        (parts[i].decode("ascii", "replace"), parts[i + 1].decode("utf-8", "replace"))
        for i in range(0, len(parts), 2)
    ]
    return tuple(sorted(rows, key=lambda row: row[1]))


def read_packet_topology_v1(git: GitReadPortV1, root: Path, head: str) -> core.PacketTopologyV1:
    history = git.run("rev-list", "-n", "1", head, "--", core.PACKET_JSON_PATH_V1)
    if not history.strip():
        core._reject("PACKET_HISTORY_EMPTY", core.PACKET_JSON_PATH_V1, "no packet commit in history")
    packet_commit = _oid(history, core.PACKET_JSON_PATH_V1)
    parents = parents_v1(git, packet_commit)
    write_set = _write_set_v1(git, parents[0], packet_commit) if len(parents) == 1 else ()
    packet_blob = blob_at_v1(git, packet_commit, core.PACKET_JSON_PATH_V1)
    markdown_blob = blob_at_v1(git, packet_commit, core.PACKET_MD_PATH_V1)
    if packet_blob is None or markdown_blob is None:
        core._reject("PACKET_MISSING_AT_P", packet_commit, "packet or markdown absent at P")
    return core.PacketTopologyV1(
        packet_commit=packet_commit,
        packet_parents=parents,
        write_set=write_set,
        head_commit=head,
        packet_in_head_history=git.succeeds("merge-base", "--is-ancestor", packet_commit, head),
        packet_blob_at_p=packet_blob,
        markdown_blob_at_p=markdown_blob,
        packet_blob_at_head=blob_at_v1(git, head, core.PACKET_JSON_PATH_V1),
        markdown_blob_at_head=blob_at_v1(git, head, core.PACKET_MD_PATH_V1),
        worktree_packet=working_bytes_v1(root, core.PACKET_JSON_PATH_V1),
        worktree_markdown=working_bytes_v1(root, core.PACKET_MD_PATH_V1),
    )


def read_current_source_state_v1(
    git: GitReadPortV1, root: Path, head: str, paths: tuple[str, ...]
) -> core.CurrentSourceStateV1:
    head_blob_ids: dict[str, str | None] = {}
    worktree_sha256: dict[str, str | None] = {}
    for path in paths:
        entry = tree_entry_v1(git, head, path)
        head_blob_ids[path] = None if entry is None else entry[1]
        raw = working_bytes_v1(root, path)
        worktree_sha256[path] = None if raw is None else core.sha256_hex_v1(raw)
    forbidden = tuple(
        path
        for path in core.CARGO_CONFIG_FORBIDDEN_PATHS_V1
        if tree_entry_v1(git, head, path) is not None or (root / path).exists()
    )
    return core.CurrentSourceStateV1(head_blob_ids, worktree_sha256, forbidden)


def read_executing_tools_v1(cli_file: Path) -> core.ExecutingToolsV1:
    """Hash the source files of the running CLI, core, shell, and scanner."""

    sources = {
        core.CHECKER_PATH_V1: cli_file,
        core.CORE_PATH_V1: Path(core.__file__),
        core.SHELL_PATH_V1: Path(__file__),
        core.SCANNER_PATH_V1: Path(scanner.__file__),
    }
    hashes: dict[str, str] = {}
    for key, source in sources.items():
        try:
            hashes[key] = core.sha256_hex_v1(source.resolve(strict=True).read_bytes())
        except OSError as exc:
            core._reject("INFRA_IO_ERROR", key, type(exc).__name__)
    return core.ExecutingToolsV1(hashes)


@dataclass(frozen=True, slots=True)
class ReplayEnvironmentV1:
    """Resolved, sanitized inputs of one replay run (see ``core.REPLAY_ENV_POLICY_V1``)."""

    python: str
    esso_python: str | None
    esso_pythonpath: str | None
    tmp_dir: Path
    tool_path: str
    rustup_home: str | None
    elan_home: str | None
    esso_python_user_base: str | None


def _host_dir(env_name: str, default: Path) -> Path:
    value = os.environ.get(env_name)
    return Path(value) if value else default


def prepare_replay_environment_v1(
    *, python: str, esso_python: str | None, esso_pythonpath: str | None, tmp_dir: Path
) -> ReplayEnvironmentV1:
    """Create the sanitized replay homes and resolve the replay tools once.

    Codex C1'' P2: nothing from the invoking user's environment reaches a replayed tool
    beyond ``core.REPLAY_ENV_POLICY_V1``. HOME and TMPDIR are empty replay-local
    directories, the Cargo home holds only a link to the host crate registry (offline
    sources) and no config file, PATH is rebuilt from the resolved tool locations, and the
    rustup and elan homes are passed as toolchain stores only.
    """

    host_home = Path(os.path.expanduser("~"))
    tool_dirs: list[str] = []
    for tool in REPLAY_TOOLS_V1:
        location = shutil.which(tool)
        if location is None:
            core._reject("INFRA_REPLAY_TOOL_UNAVAILABLE", tool, "not on PATH")
        directory = str(Path(location).parent)
        if directory not in tool_dirs:
            tool_dirs.append(directory)
    for name in ("home", "tmp", "cargo-home"):
        (tmp_dir / name).mkdir(parents=True, exist_ok=False)
    registry = _host_dir("CARGO_HOME", host_home / ".cargo") / "registry"
    if not registry.is_dir():
        core._reject("INFRA_REPLAY_TOOL_UNAVAILABLE", "cargo", "host crate registry missing")
    (tmp_dir / "cargo-home" / "registry").symlink_to(registry, target_is_directory=True)
    rustup_home = _host_dir("RUSTUP_HOME", host_home / ".rustup")
    elan_home = _host_dir("ELAN_HOME", host_home / ".elan")
    user_base = _host_dir("PYTHONUSERBASE", host_home / ".local")
    return ReplayEnvironmentV1(
        python=python,
        esso_python=esso_python,
        esso_pythonpath=esso_pythonpath,
        tmp_dir=tmp_dir,
        tool_path=":".join([*tool_dirs, "/usr/bin", "/bin"]),
        rustup_home=str(rustup_home) if rustup_home.is_dir() else None,
        elan_home=str(elan_home) if elan_home.is_dir() else None,
        esso_python_user_base=str(user_base) if user_base.is_dir() else None,
    )


def _replay_env(command: core.ReplayCommandV1, environment: ReplayEnvironmentV1) -> dict[str, str]:
    env = dict(REPLAY_FIXED_ENV_V1)
    env["HOME"] = str(environment.tmp_dir / "home")
    env["TMPDIR"] = str(environment.tmp_dir / "tmp")
    env["PATH"] = environment.tool_path
    env["CARGO_HOME"] = str(environment.tmp_dir / "cargo-home")
    if environment.rustup_home:
        env["RUSTUP_HOME"] = environment.rustup_home
    if environment.elan_home:
        env["ELAN_HOME"] = environment.elan_home
    esso_command = "PYTHONPATH" in command.env_names or "ZENO_ESSO_PYTHON" in command.env_names
    if esso_command and environment.esso_python_user_base:
        env["PYTHONUSERBASE"] = environment.esso_python_user_base
    if "PYTHONPATH" in command.env_names and environment.esso_pythonpath:
        env["PYTHONPATH"] = environment.esso_pythonpath
    if "ZENO_ESSO_PYTHON" in command.env_names and environment.esso_python:
        env["ZENO_ESSO_PYTHON"] = environment.esso_python
    if "CARGO_TARGET_DIR" in command.env_names:
        env["CARGO_TARGET_DIR"] = str(environment.tmp_dir / "cargo-target")
        env.update(REPLAY_CARGO_ENV_V1)
    return env


def _probe_file(root: Path, environment: ReplayEnvironmentV1) -> tuple[Path, str]:
    proof = (root / core.LEAN_PROOF_PATH_V1).read_text(encoding="utf-8")
    namespace = ".".join(core.LEAN_NAMESPACE_V1)
    probes = "\n".join(f"#print axioms {namespace}.{name}" for _, name in core.THEOREM_INVENTORY_V1)
    text = proof + "\n" + probes + "\n"
    target = environment.tmp_dir / "GlobalClaimantCustodyRelationV1Axioms.lean"
    target.write_text(text, encoding="utf-8")
    return target, core.sha256_hex_v1(text.encode("utf-8"))


def _argv(command: core.ReplayCommandV1, environment: ReplayEnvironmentV1, probe: Path) -> list[str]:
    substitutions = {
        core.PYTHON_TOKEN_V1: environment.python,
        core.ESSO_PYTHON_TOKEN_V1: environment.esso_python or "",
        "<PROBE>": str(probe),
    }
    argv = [substitutions.get(token, token) for token in command.argv]
    if "" in argv:
        core._reject("INFRA_REPLAY_TOOL_UNAVAILABLE", command.command_id, "ESSO interpreter not set")
    return argv


def run_proof_replay_v1(
    root: Path, environment: ReplayEnvironmentV1
) -> tuple[core.ReplayObservationV1, ...]:
    """Execute the closed replay command list and return raw observations."""

    probe, probe_sha256 = _probe_file(root, environment)
    observations: list[core.ReplayObservationV1] = []
    for command in core.REPLAY_COMMANDS_V1:
        argv = _argv(command, environment, probe)
        try:
            result = subprocess.run(
                argv,
                cwd=root / command.cwd,
                env=_replay_env(command, environment),
                stdin=subprocess.DEVNULL,
                capture_output=True,
                check=False,
                timeout=command.timeout_seconds,
            )
        except subprocess.TimeoutExpired:
            observations.append(core.ReplayObservationV1(command.command_id, -1, b"", b"", True))
            continue
        except OSError as exc:
            core._reject("INFRA_REPLAY_TOOL_UNAVAILABLE", command.command_id, type(exc).__name__)
        observations.append(
            core.ReplayObservationV1(
                command.command_id,
                result.returncode,
                result.stdout,
                result.stderr,
                False,
                probe_sha256 if command.command_id == "lean_axioms_probe" else None,
            )
        )
    return tuple(observations)


__all__ = [
    "GitReadPortV1",
    "ReplayEnvironmentV1",
    "blob_at_v1",
    "head_commit_v1",
    "parents_v1",
    "read_current_source_state_v1",
    "read_executing_tools_v1",
    "read_packet_topology_v1",
    "read_subject_snapshot_v1",
    "resolve_repo_root_v1",
    "run_proof_replay_v1",
    "tree_entry_v1",
    "validate_commit_v1",
    "working_bytes_v1",
]
