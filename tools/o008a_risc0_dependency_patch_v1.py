"""Deterministic validation for the O-008A RISC0 dependency patch.

The patch is build-time research infrastructure.  A successful check only
establishes the exact local source and selected Cargo graph described here.  It
does not qualify a build host, prove a guest, or grant runtime authority.
"""

from __future__ import annotations

import hashlib
import json
import re
import stat
import subprocess
import tempfile
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NoReturn, cast

SCHEMA = "zenodex/o008a-risc0-dependency-patch-check/v1"
SUBJECT_PARENT_COMMIT = "b6655bf0c7ef7e099c9430485010baf4df15fd65"
PRIMARY_PATCH_DONOR_COMMIT = "8b589e373f2ff6018d2f952b0a104f4f9f28a438"
WORKSPACE_PATH = Path("zk/economic_initial_state_risc0/Cargo.toml")
LOCK_PATH = Path("zk/economic_initial_state_risc0/Cargo.lock")
THV_PATH = Path("tests/evidence/test_hygiene/THV1-20260831-o008a-risc0-dependency-patch-v1.json")
VENDOR_ROOT = Path("vendor/risc0-3.0.6-patches")
GIT_BINARY = Path("/usr/bin/git")
SCRATCH_PARENT = Path("/tmp")
FULL_COMMIT_SHA_RE = re.compile(r"[0-9a-f]{40}\Z")

NON_VENDOR_WRITE_SET = frozenset(
    {
        ".gitattributes",
        ".gitignore",
        "docs/dependency-approvals/2026-08-31-risc0-3-0-6-source-pinned-patches.md",
        "tests/evidence/test_hygiene/THV1-20260831-o008a-risc0-dependency-patch-v1.json",
        "tests/test_o008a_risc0_dependency_patch_v1.py",
        "tools/check_o008a_risc0_dependency_patch_v1.py",
        "tools/o008a_risc0_dependency_patch_v1.py",
        "zk/economic_initial_state_risc0/Cargo.lock",
        "zk/economic_initial_state_risc0/Cargo.toml",
    }
)
EXECUTABLE_PATH = "vendor/risc0-3.0.6-patches/rzup-0.5.2/install"
TRACING_CACHED_UPSTREAM_RESTORED_PATHS = (
    "vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/src/filter/env/builder.rs",
    "vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/src/filter/env/directive.rs",
    "vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/src/filter/env/field.rs",
    "vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/src/filter/env/mod.rs",
)

NO_AUTHORITY = {
    "build_host_authority": "NONE",
    "migration_authority": "NONE",
    "production_authority": "NONE",
    "release_authority": "NONE",
    "settlement_authority": "NONE",
    "value_movement_authority": "NONE",
    "verifier_authority": "NONE",
}


@dataclass(frozen=True)
class VendorIdentityV1:
    directory: str
    package: str
    version: str
    license: str
    repository: str
    recorded_crates_io_archive_sha256: str
    upstream_vcs_sha1: str
    upstream_tree_sha256: str
    patched_tree_sha256: str
    file_count: int
    total_size_bytes: int


VENDOR_IDENTITIES = (
    VendorIdentityV1(
        directory="ark-relations-0.5.1",
        package="ark-relations",
        version="0.5.1",
        license="MIT/Apache-2.0",
        repository="https://github.com/arkworks-rs/snark",
        recorded_crates_io_archive_sha256="ec46ddc93e7af44bcab5230937635b06fb5744464dd6a7e7b083e80ebd274384",
        upstream_vcs_sha1="b34f11d670c2667de3eda6e33daed8027f35043e",
        upstream_tree_sha256="b11451965067b35e7fa6f43cd01c66ab61f9b02f17f02e74b47bc5d450835810",
        patched_tree_sha256="b4837fda182b33c8fe5212b25ba6b263fbabdd730671d156618ee719ba2e69dd",
        file_count=11,
        total_size_bytes=90_897,
    ),
    VendorIdentityV1(
        directory="rzup-0.5.2",
        package="rzup",
        version="0.5.2",
        license="Apache-2.0",
        repository="https://github.com/risc0/risc0/",
        recorded_crates_io_archive_sha256="96909a7ea8fdf7e18da727d7facbc43eea8a4f77635e7ec75a69794dede16fb6",
        upstream_vcs_sha1="8c215e2f4ccdd935f0517bf05d90f1ae032840a9",
        upstream_tree_sha256="7de15d39a6474bf4490fc5b0deaba0c8226791df975b2e10ba45112a93e2769e",
        patched_tree_sha256="fbe364913e8dd4627008a6a590fdef69cffa82d76d42b94d44cb6f4f5d8652cc",
        file_count=27,
        total_size_bytes=298_999,
    ),
    VendorIdentityV1(
        directory="tracing-subscriber-0.3.22",
        package="tracing-subscriber",
        version="0.3.22",
        license="MIT",
        repository="https://github.com/tokio-rs/tracing",
        recorded_crates_io_archive_sha256="2f30143827ddab0d256fd843b7a66d164e9f271cfa0dde49142c5ca0ca291f1e",
        upstream_vcs_sha1="cc44064b3a41cb586bd633f8a024354928e25819",
        upstream_tree_sha256="0e36c6b8e465689117c83fc2dd29acf7b846a9f4a6133730ef61d3c328aa2a12",
        patched_tree_sha256="0e36c6b8e465689117c83fc2dd29acf7b846a9f4a6133730ef61d3c328aa2a12",
        file_count=86,
        total_size_bytes=1_050_965,
    ),
)

EXPECTED_VENDOR_FILE_COUNT = 1 + sum(
    identity.file_count for identity in VENDOR_IDENTITIES
)  # subtree README plus the three crate trees

EXPECTED_PATCH_PATHS = {
    "ark-relations": "../../vendor/risc0-3.0.6-patches/ark-relations-0.5.1",
    "rzup": "../../vendor/risc0-3.0.6-patches/rzup-0.5.2",
    "tracing-subscriber": ("../../vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22"),
}


class DependencyPatchRejectV1(ValueError):
    """Typed deterministic rejection from the dependency-patch checker."""

    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code}:{path}:{detail}")
        self.code = code
        self.path = path
        self.detail = detail


def _reject(code: str, path: str | Path, detail: str) -> NoReturn:
    raise DependencyPatchRejectV1(code, str(path), detail)


def _expect(condition: bool, code: str, path: str | Path, detail: str) -> None:
    if not condition:
        _reject(code, path, detail)


@dataclass(frozen=True)
class GitTreeEntryV1:
    mode: str
    object_id: str
    object_type: str


@dataclass(frozen=True)
class SubjectSnapshotV1:
    subject: str
    parent: str
    tree: str
    entries: dict[str, GitTreeEntryV1]
    changed_paths: frozenset[str]


def validate_subject_literal_v1(subject: str) -> None:
    _expect(
        FULL_COMMIT_SHA_RE.fullmatch(subject) is not None,
        "SUBJECT_LITERAL",
        "--subject",
        "literal lowercase 40-hex commit SHA required",
    )


def _git_v1(root: Path, *args: str) -> bytes:
    _expect(GIT_BINARY.is_file(), "GIT_BINARY", GIT_BINARY, "exact Git binary required")
    try:
        completed = subprocess.run(
            [
                str(GIT_BINARY),
                "-C",
                str(root),
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "core.attributesFile=/dev/null",
                *args,
            ],
            check=False,
            capture_output=True,
            env={
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_NO_REPLACE_OBJECTS": "1",
                "GIT_OPTIONAL_LOCKS": "0",
                "HOME": "/nonexistent",
                "LANG": "C",
                "LC_ALL": "C",
                "PATH": "/usr/bin:/bin",
            },
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        _reject("GIT_OBJECT", " ".join(args), str(error))
    _expect(
        completed.returncode == 0,
        "GIT_OBJECT",
        " ".join(args),
        completed.stderr.decode("utf-8", errors="replace"),
    )
    return completed.stdout


def validate_repository_root_v1(root: Path) -> Path:
    try:
        sanitized = root.resolve(strict=True)
    except OSError as error:
        _reject("REPOSITORY_ROOT", root, str(error))
    _expect(sanitized.is_dir(), "REPOSITORY_ROOT", root, "directory required")
    raw_top = _git_v1(sanitized, "rev-parse", "--show-toplevel")
    try:
        rendered_top = raw_top.decode("utf-8")
    except UnicodeDecodeError as error:
        _reject("REPOSITORY_ROOT", root, str(error))
    _expect(
        rendered_top.endswith("\n") and "\n" not in rendered_top[:-1],
        "REPOSITORY_ROOT",
        root,
        "one canonical Git top-level path required",
    )
    top_text = rendered_top[:-1]
    _expect(bool(top_text), "REPOSITORY_ROOT", root, "nonempty Git top-level required")
    top_path = Path(top_text)
    _expect(top_path.is_absolute(), "REPOSITORY_ROOT", top_path, "absolute path required")
    try:
        canonical_top = top_path.resolve(strict=True)
    except OSError as error:
        _reject("REPOSITORY_ROOT", top_path, str(error))
    _expect(
        canonical_top == sanitized,
        "REPOSITORY_ROOT",
        root,
        "checker root must equal the sanitized Git top level",
    )
    return sanitized


def validate_scratch_parent_v1(parent: Path) -> Path:
    _expect(parent.is_absolute(), "SCRATCH_PARENT", parent, "absolute path required")
    try:
        metadata = parent.lstat()
        canonical = parent.resolve(strict=True)
        root_device = Path("/").stat().st_dev
    except OSError as error:
        _reject("SCRATCH_PARENT", parent, str(error))
    _expect(
        not stat.S_ISLNK(metadata.st_mode) and canonical == parent,
        "SCRATCH_SYMLINK",
        parent,
        "real nonsymlinked path required",
    )
    _expect(stat.S_ISDIR(metadata.st_mode), "SCRATCH_PARENT", parent, "directory required")
    _expect(
        metadata.st_dev == root_device,
        "SCRATCH_DEVICE",
        parent,
        "scratch parent must use the root filesystem device",
    )
    return parent


def validate_canonical_git_path_v1(path: str) -> None:
    parts = path.split("/")
    _expect(
        bool(path)
        and not path.startswith("/")
        and "\\" not in path
        and all(part not in {"", ".", ".."} for part in parts),
        "SUBJECT_PATH",
        path,
        "canonical relative slash-separated path required",
    )


def _parse_commit_header_v1(raw: bytes, subject: str) -> tuple[str, str]:
    header, separator, _message = raw.partition(b"\n\n")
    _expect(bool(separator), "SUBJECT_COMMIT", subject, "commit header terminator required")
    try:
        lines = header.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        _reject("SUBJECT_COMMIT", subject, str(error))
    trees = [line.removeprefix("tree ") for line in lines if line.startswith("tree ")]
    parents = [line.removeprefix("parent ") for line in lines if line.startswith("parent ")]
    _expect(len(trees) == 1, "SUBJECT_TREE", subject, "exactly one tree required")
    _expect(len(parents) == 1, "SUBJECT_PARENT", subject, "exactly one parent required")
    _expect(
        parents[0] == SUBJECT_PARENT_COMMIT,
        "SUBJECT_PARENT",
        subject,
        f"exact parent {SUBJECT_PARENT_COMMIT} required",
    )
    _expect(
        FULL_COMMIT_SHA_RE.fullmatch(trees[0]) is not None,
        "SUBJECT_TREE",
        subject,
        "literal tree object ID required",
    )
    return parents[0], trees[0]


def _parse_ls_tree_v1(raw: bytes) -> dict[str, GitTreeEntryV1]:
    entries: dict[str, GitTreeEntryV1] = {}
    for record in raw.split(b"\0"):
        if not record:
            continue
        header, separator, raw_path = record.partition(b"\t")
        _expect(bool(separator), "SUBJECT_LS_TREE", "subject", "malformed tree row")
        try:
            mode, object_type, object_id = header.decode("ascii").split()
            path = raw_path.decode("utf-8")
        except (UnicodeDecodeError, ValueError) as error:
            _reject("SUBJECT_LS_TREE", "subject", str(error))
        validate_canonical_git_path_v1(path)
        _expect(path not in entries, "SUBJECT_LS_TREE", path, "duplicate path")
        entries[path] = GitTreeEntryV1(mode, object_id, object_type)
    return entries


def validate_closed_write_set_v1(
    changed_paths: frozenset[str],
    entries: dict[str, GitTreeEntryV1],
) -> dict[str, object]:
    vendor_paths = frozenset(
        path for path in entries if path.startswith(f"{VENDOR_ROOT.as_posix()}/")
    )
    _expect(
        len(vendor_paths) == EXPECTED_VENDOR_FILE_COUNT,
        "WRITE_SET_VENDOR_COUNT",
        VENDOR_ROOT,
        f"exactly {EXPECTED_VENDOR_FILE_COUNT} committed vendor files required",
    )
    expected_paths = NON_VENDOR_WRITE_SET | vendor_paths
    _expect(
        changed_paths == expected_paths,
        "WRITE_SET_PATHS",
        "subject",
        "subject diff must equal the exact closed Stage-A write set",
    )
    for path in sorted(expected_paths):
        entry = entries.get(path)
        if entry is None:
            _reject("WRITE_SET_MISSING", path, "committed blob required")
        _expect(entry.object_type == "blob", "WRITE_SET_TYPE", path, "blob required")
        expected_mode = "100755" if path == EXECUTABLE_PATH else "100644"
        _expect(
            entry.mode == expected_mode,
            "WRITE_SET_MODE",
            path,
            f"exact mode {expected_mode} required",
        )
    rows = [
        {
            "mode": entries[path].mode,
            "object_id": entries[path].object_id,
            "path": path,
        }
        for path in sorted(expected_paths)
    ]
    return {
        "file_count": len(rows),
        "root_sha256": sha256_hex_v1(canonical_json_bytes_v1(rows)),
        "vendor_file_count": len(vendor_paths),
    }


def read_subject_snapshot_v1(root: Path, subject: str) -> SubjectSnapshotV1:
    validate_subject_literal_v1(subject)
    object_type = _git_v1(root, "cat-file", "-t", subject).strip()
    _expect(object_type == b"commit", "SUBJECT_TYPE", subject, "commit object required")
    parent, tree = _parse_commit_header_v1(_git_v1(root, "cat-file", "-p", subject), subject)
    entries = _parse_ls_tree_v1(_git_v1(root, "ls-tree", "--full-tree", "-r", "-z", subject))
    raw_paths = _git_v1(
        root,
        "diff-tree",
        "--no-relative",
        "--no-commit-id",
        "--name-only",
        "-r",
        "-z",
        parent,
        subject,
        "--",
    )
    try:
        paths = [path.decode("utf-8") for path in raw_paths.split(b"\0") if path]
    except UnicodeDecodeError as error:
        _reject("WRITE_SET_PATHS", subject, str(error))
    for path in paths:
        validate_canonical_git_path_v1(path)
    _expect(len(paths) == len(set(paths)), "WRITE_SET_PATHS", subject, "duplicate path")
    snapshot = SubjectSnapshotV1(subject, parent, tree, entries, frozenset(paths))
    validate_closed_write_set_v1(snapshot.changed_paths, snapshot.entries)
    return snapshot


def read_subject_blob_v1(root: Path, snapshot: SubjectSnapshotV1, path: str) -> bytes:
    entry = snapshot.entries.get(path)
    if entry is None:
        _reject("SUBJECT_BLOB", path, "committed path required")
    _expect(entry.object_type == "blob", "SUBJECT_BLOB", path, "blob required")
    return _git_v1(root, "cat-file", "blob", entry.object_id)


def canonical_json_bytes_v1(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def sha256_hex_v1(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob_sha1_v1(raw: bytes) -> str:
    header = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(header + raw, usedforsecurity=False).hexdigest()


def validate_repository_policy_v1(root: Path) -> None:
    attributes = (root / ".gitattributes").read_text(encoding="utf-8").splitlines()
    _expect(
        attributes
        == [
            "# Preserve reviewed upstream crate bytes exactly, including inherited whitespace.",
            "/vendor/risc0-3.0.6-patches/** -text -whitespace linguist-vendored",
        ],
        "GIT_ATTRIBUTES",
        ".gitattributes",
        "exact anchored vendored-byte policy required",
    )
    ignore_lines = (root / ".gitignore").read_text(encoding="utf-8").splitlines()
    expected = [
        "!/vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/src/filter/env/",
        "!/vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/src/filter/env/*.rs",
    ]
    for line in expected:
        _expect(
            ignore_lines.count(line) == 1,
            "GIT_IGNORE",
            ".gitignore",
            f"exact anchored exception required: {line}",
        )


def _validate_thv_source_pins_v1(root: Path, source_pin_rows: list[object]) -> None:
    expected_source_paths = {
        ".gitattributes",
        ".gitignore",
        "docs/dependency-approvals/2026-08-31-risc0-3-0-6-source-pinned-patches.md",
        "tools/check_o008a_risc0_dependency_patch_v1.py",
        "tools/o008a_risc0_dependency_patch_v1.py",
        "vendor/risc0-3.0.6-patches/README.md",
        "zk/economic_initial_state_risc0/Cargo.lock",
        "zk/economic_initial_state_risc0/Cargo.toml",
    }
    actual_source_paths: set[str] = set()
    for raw_row in source_pin_rows:
        _expect(type(raw_row) is dict, "THV1_PINS", THV_PATH, "pin row required")
        row = cast(dict[str, object], raw_row)
        path = row.get("path")
        digest = row.get("sha256")
        if type(path) is not str:
            _reject("THV1_PINS", THV_PATH, "pin path required")
        _expect(path not in actual_source_paths, "THV1_PINS", path, "duplicate pin")
        actual_source_paths.add(path)
        if type(digest) is not str:
            _reject("THV1_PINS", path, "pin digest required")
        _expect(
            digest == sha256_hex_v1((root / path).read_bytes()),
            "THV1_PIN_HASH",
            path,
            "committed source digest differs",
        )
    _expect(
        actual_source_paths == expected_source_paths,
        "THV1_PINS",
        THV_PATH,
        "exact closed source-pin set required",
    )


def validate_thv1_v1(root: Path) -> None:
    try:
        thv = json.loads((root / THV_PATH).read_bytes())
    except (OSError, json.JSONDecodeError) as error:
        _reject("THV1", THV_PATH, str(error))
    _expect(
        type(thv) is dict and thv.get("schema") == "zenodex/test-hygiene-evidence/v1",
        "THV1",
        THV_PATH,
        "exact THV1 schema required",
    )
    claim_scope = thv.get("claim_scope")
    _expect(
        type(claim_scope) is str and SUBJECT_PARENT_COMMIT in claim_scope,
        "THV1_PARENT",
        THV_PATH,
        "exact parent must appear in claim scope",
    )
    source_pins = thv.get("source_pins")
    _expect(type(source_pins) is list, "THV1_PINS", THV_PATH, "source pins required")
    _validate_thv_source_pins_v1(root, cast(list[object], source_pins))
    test_pins = thv.get("test_pins")
    _expect(
        type(test_pins) is list and len(test_pins) == 1,
        "THV1_TEST",
        THV_PATH,
        "one test pin required",
    )
    test_row = cast(dict[str, object], test_pins[0])
    test_path = "tests/test_o008a_risc0_dependency_patch_v1.py"
    _expect(test_row.get("path") == test_path, "THV1_TEST", THV_PATH, "exact test path required")
    _expect(
        test_row.get("sha256") == sha256_hex_v1((root / test_path).read_bytes()),
        "THV1_TEST_HASH",
        test_path,
        "committed test digest differs",
    )


def decode_toml_v1(raw: bytes, path: str | Path) -> dict[str, Any]:
    try:
        decoded = tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        _reject("TOML", path, str(error))
    _expect(type(decoded) is dict, "TOML", path, "top level must be a table")
    return decoded


def vendor_tree_entries_v1(crate_root: Path) -> list[dict[str, object]]:
    _expect(crate_root.is_dir(), "VENDOR_ROOT", crate_root, "directory required")
    entries: list[dict[str, object]] = []
    for path in sorted(crate_root.rglob("*")):
        relative = path.relative_to(crate_root).as_posix()
        if path.is_symlink():
            _reject("VENDOR_SYMLINK", relative, "symlinks are forbidden")
        if path.is_dir():
            continue
        _expect(path.is_file(), "VENDOR_NODE", relative, "regular file required")
        _expect(
            path.name not in {".cargo-ok", "Cargo.lock"},
            "VENDOR_GENERATED_FILE",
            relative,
            "registry marker and upstream lock files are excluded",
        )
        raw = path.read_bytes()
        entries.append(
            {
                "executable": bool(path.stat().st_mode & stat.S_IXUSR),
                "path": relative,
                "sha256": sha256_hex_v1(raw),
                "size_bytes": len(raw),
            }
        )
    return entries


def vendor_tree_summary_v1(crate_root: Path) -> dict[str, object]:
    entries = vendor_tree_entries_v1(crate_root)
    return {
        "file_count": len(entries),
        "total_size_bytes": sum(cast(int, row["size_bytes"]) for row in entries),
        "tree_sha256": sha256_hex_v1(canonical_json_bytes_v1(entries)),
    }


def _package_table_v1(cargo: dict[str, Any], path: str | Path) -> dict[str, Any]:
    package = cargo.get("package")
    if type(package) is not dict:
        _reject("PACKAGE", path, "package table required")
    return cast(dict[str, Any], package)


def _cached_upstream_restored_paths_v1(
    root: Path,
    identity: VendorIdentityV1,
) -> tuple[str, ...]:
    if identity.package != "tracing-subscriber":
        return ()
    for restored_path in TRACING_CACHED_UPSTREAM_RESTORED_PATHS:
        _expect(
            (root / restored_path).is_file(),
            "VENDOR_CACHED_UPSTREAM_RESTORE",
            restored_path,
            "restored cached-upstream source must be in the closed crate tree",
        )
    return TRACING_CACHED_UPSTREAM_RESTORED_PATHS


def validate_vendor_identity_v1(root: Path, identity: VendorIdentityV1) -> dict[str, object]:
    crate_root = root / VENDOR_ROOT / identity.directory
    summary = vendor_tree_summary_v1(crate_root)
    _expect(
        summary
        == {
            "file_count": identity.file_count,
            "total_size_bytes": identity.total_size_bytes,
            "tree_sha256": identity.patched_tree_sha256,
        },
        "VENDOR_TREE",
        crate_root,
        "closed vendored source tree differs from the reviewed identity",
    )

    cargo_path = crate_root / "Cargo.toml"
    package = _package_table_v1(decode_toml_v1(cargo_path.read_bytes(), cargo_path), cargo_path)
    expected_package = {
        "name": identity.package,
        "version": identity.version,
        "license": identity.license,
        "repository": identity.repository,
    }
    _expect(
        {key: package.get(key) for key in expected_package} == expected_package,
        "VENDOR_PACKAGE",
        cargo_path,
        "package identity, license, or repository differs",
    )

    vcs_path = crate_root / ".cargo_vcs_info.json"
    try:
        vcs = json.loads(vcs_path.read_bytes())
    except (OSError, json.JSONDecodeError) as error:
        _reject("VENDOR_VCS", vcs_path, str(error))
    _expect(
        vcs.get("git", {}).get("sha1") == identity.upstream_vcs_sha1,
        "VENDOR_VCS",
        vcs_path,
        "upstream VCS identity differs",
    )
    restored_paths = _cached_upstream_restored_paths_v1(root, identity)
    return {
        "archive_rehashed_in_this_restage": False,
        "cached_upstream_restored_paths": list(restored_paths),
        "directory": identity.directory,
        "file_count": summary["file_count"],
        "license": identity.license,
        "package": identity.package,
        "patched_tree_sha256": summary["tree_sha256"],
        "repository": identity.repository,
        "total_size_bytes": summary["total_size_bytes"],
        "recorded_crates_io_archive_sha256": identity.recorded_crates_io_archive_sha256,
        "upstream_tree_sha256": identity.upstream_tree_sha256,
        "upstream_vcs_sha1": identity.upstream_vcs_sha1,
        "version": identity.version,
    }


def validate_workspace_patch_v1(workspace: dict[str, Any]) -> None:
    patch = workspace.get("patch")
    crates_io = patch.get("crates-io") if type(patch) is dict else None
    if type(crates_io) is not dict:
        _reject("WORKSPACE_PATCH", WORKSPACE_PATH, "patch table required")
    crates_io_table = cast(dict[str, Any], crates_io)
    actual = {
        name: value.get("path") if type(value) is dict else None
        for name, value in crates_io_table.items()
    }
    _expect(
        actual == EXPECTED_PATCH_PATHS,
        "WORKSPACE_PATCH",
        WORKSPACE_PATH,
        "exact closed patch mapping required",
    )


def _lock_packages_v1(lock: dict[str, Any]) -> list[dict[str, Any]]:
    packages = lock.get("package")
    if type(packages) is not list:
        _reject("LOCK", LOCK_PATH, "package array required")
    _expect(
        all(type(package) is dict for package in packages),
        "LOCK",
        LOCK_PATH,
        "package rows must be tables",
    )
    return cast(list[dict[str, Any]], packages)


def validate_lock_v1(lock: dict[str, Any]) -> None:
    packages = _lock_packages_v1(lock)
    by_name: dict[str, list[dict[str, Any]]] = {}
    for package in packages:
        name = package.get("name")
        if type(name) is not str:
            _reject("LOCK", LOCK_PATH, "package name required")
        by_name.setdefault(name, []).append(package)

    _expect("rsa" not in by_name, "LOCK_FORBIDDEN_PACKAGE", LOCK_PATH, "rsa must be absent")
    expected = {
        "ark-relations": "0.5.1",
        "risc0-build": "3.0.6",
        "risc0-zkvm": "3.0.6",
        "rzup": "0.5.2",
        "tracing-subscriber": "0.3.22",
    }
    for name, version in expected.items():
        rows = by_name.get(name, [])
        _expect(
            len(rows) == 1 and rows[0].get("version") == version,
            "LOCK_VERSION",
            LOCK_PATH,
            f"exact {name} {version} required",
        )

    for name in ("ark-relations", "rzup", "tracing-subscriber"):
        row = by_name[name][0]
        _expect(
            "source" not in row and "checksum" not in row,
            "LOCK_PATCH_SOURCE",
            LOCK_PATH,
            f"{name} must resolve through the local patch",
        )
    _expect(
        "rsa" not in by_name["rzup"][0].get("dependencies", []),
        "LOCK_RZUP_RSA",
        LOCK_PATH,
        "selected rzup feature graph must not include rsa",
    )


def validate_rzup_policy_v1(cargo: dict[str, Any], signature_source: str) -> None:
    features = cargo.get("features")
    dependencies = cargo.get("dependencies")
    if type(features) is not dict:
        _reject("RZUP_FEATURE_POLICY", "rzup/Cargo.toml", "features required")
    if type(dependencies) is not dict:
        _reject("RZUP_FEATURE_POLICY", "rzup/Cargo.toml", "dependencies required")
    feature_table = cast(dict[str, Any], features)
    dependency_table = cast(dict[str, Any], dependencies)
    _expect(
        feature_table.get("signature") == ["dep:rsa"],
        "RZUP_FEATURE_POLICY",
        "rzup/Cargo.toml",
        "signature must be the only rsa feature gate",
    )
    for feature in ("install", "publish"):
        values = feature_table.get(feature)
        _expect(
            type(values) is list and "signature" in values,
            "RZUP_FEATURE_POLICY",
            "rzup/Cargo.toml",
            f"{feature} must retain signature verification",
        )
    rsa = dependency_table.get("rsa")
    _expect(
        type(rsa) is dict and rsa.get("optional") is True and rsa.get("version") == "0.9",
        "RZUP_FEATURE_POLICY",
        "rzup/Cargo.toml",
        "rsa must be optional and pinned to the upstream compatibility line",
    )
    _expect(
        '#[cfg(not(feature = "signature"))]' in signature_source,
        "RZUP_FAIL_CLOSED",
        "rzup/src/distribution/signature.rs",
        "non-signature implementation required",
    )
    _expect(
        'Err(RzupError::Other("signature feature not enabled".into()))' in signature_source,
        "RZUP_FAIL_CLOSED",
        "rzup/src/distribution/signature.rs",
        "signature-disabled operations must reject",
    )
    _expect(
        "pub fn verify(&self, _data: &[u8], _signature: &Signature) -> Result<()>"
        in signature_source,
        "RZUP_FAIL_CLOSED",
        "rzup/src/distribution/signature.rs",
        "signature-disabled verification entrypoint required",
    )
    _expect(
        "fn signature_disabled_operations_fail_closed()" in signature_source,
        "RZUP_FAIL_CLOSED",
        "rzup/src/distribution/signature.rs",
        "signature-disabled regression test required",
    )


def validate_rzup_test_profile_v1(lib_source: str, components_source: str) -> None:
    complete_profile_gate = '#[cfg(all(test, feature = "install", feature = "publish"))]'
    for relative_path, source in (
        ("rzup/src/lib.rs", lib_source),
        ("rzup/src/components.rs", components_source),
    ):
        _expect(
            complete_profile_gate in source,
            "RZUP_TEST_PROFILE",
            relative_path,
            "feature-dependent upstream tests require the complete install-and-publish profile",
        )


def validate_ark_policy_v1(cargo: dict[str, Any], trace_source: str) -> None:
    dependencies = cargo.get("dependencies")
    if type(dependencies) is not dict:
        _reject(
            "ARK_TRACING_VERSION",
            "ark-relations/Cargo.toml",
            "dependencies required",
        )
    dependency_table = cast(dict[str, Any], dependencies)
    tracing = dependency_table.get("tracing-subscriber")
    _expect(
        type(tracing) is dict
        and tracing.get("version") == "0.3.20"
        and tracing.get("optional") is True
        and tracing.get("default-features") is False,
        "ARK_TRACING_VERSION",
        "ark-relations/Cargo.toml",
        "patched tracing-subscriber compatibility floor required",
    )
    _expect(
        "fn on_new_span(" in trace_source and "fn new_span(" not in trace_source,
        "ARK_TRACING_API",
        "ark-relations/src/r1cs/trace.rs",
        "tracing-subscriber 0.3 Layer API required",
    )


def _materialize_subject_v1(
    repository_root: Path,
    snapshot: SubjectSnapshotV1,
    destination: Path,
) -> None:
    for path in sorted(snapshot.changed_paths):
        entry = snapshot.entries[path]
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(read_subject_blob_v1(repository_root, snapshot, path))
        target.chmod(0o755 if entry.mode == "100755" else 0o644)


def _build_content_report_v1(root: Path) -> dict[str, object]:
    validate_repository_policy_v1(root)
    validate_thv1_v1(root)
    workspace_path = root / WORKSPACE_PATH
    lock_path = root / LOCK_PATH
    workspace = decode_toml_v1(workspace_path.read_bytes(), workspace_path)
    lock = decode_toml_v1(lock_path.read_bytes(), lock_path)
    validate_workspace_patch_v1(workspace)
    validate_lock_v1(lock)

    rzup_root = root / VENDOR_ROOT / "rzup-0.5.2"
    validate_rzup_policy_v1(
        decode_toml_v1((rzup_root / "Cargo.toml").read_bytes(), rzup_root / "Cargo.toml"),
        (rzup_root / "src/distribution/signature.rs").read_text(encoding="utf-8"),
    )
    validate_rzup_test_profile_v1(
        (rzup_root / "src/lib.rs").read_text(encoding="utf-8"),
        (rzup_root / "src/components.rs").read_text(encoding="utf-8"),
    )
    ark_root = root / VENDOR_ROOT / "ark-relations-0.5.1"
    validate_ark_policy_v1(
        decode_toml_v1((ark_root / "Cargo.toml").read_bytes(), ark_root / "Cargo.toml"),
        (ark_root / "src/r1cs/trace.rs").read_text(encoding="utf-8"),
    )
    identities = [validate_vendor_identity_v1(root, identity) for identity in VENDOR_IDENTITIES]
    return {
        "authority": NO_AUTHORITY,
        "build_host_qualified": False,
        "dependency_patch": "SOURCE_PINNED_SELECTED_GRAPH",
        "implementation_subject": {
            "parent_commit": SUBJECT_PARENT_COMMIT,
            "primary_patch_donor_commit": PRIMARY_PATCH_DONOR_COMMIT,
        },
        "lock_sha256": sha256_hex_v1(lock_path.read_bytes()),
        "ok": True,
        "proof_validity": "NOT_CLAIMED",
        "release_ready": False,
        "resolved_advisories": ["RUSTSEC-2023-0071", "RUSTSEC-2025-0055"],
        "schema": SCHEMA,
        "selected_graph_audit_expectation": "ZERO_VULNERABILITIES",
        "status": "PATCH_GRAPH_VALIDATED",
        "vendor_identities": identities,
    }


def build_report_v1(root: Path, subject: str) -> dict[str, object]:
    repository_root = validate_repository_root_v1(root)
    snapshot = read_subject_snapshot_v1(repository_root, subject)
    write_set = validate_closed_write_set_v1(snapshot.changed_paths, snapshot.entries)
    scratch_parent = validate_scratch_parent_v1(SCRATCH_PARENT)
    with tempfile.TemporaryDirectory(
        prefix="zenodex-o008a-stage-a-",
        dir=scratch_parent,
    ) as temporary:
        snapshot_root = Path(temporary)
        _materialize_subject_v1(repository_root, snapshot, snapshot_root)
        report = _build_content_report_v1(snapshot_root)
    report["implementation_subject"] = {
        "commit": snapshot.subject,
        "parent_commit": snapshot.parent,
        "primary_patch_donor_commit": PRIMARY_PATCH_DONOR_COMMIT,
        "tree": snapshot.tree,
    }
    report["write_set"] = write_set
    return report


def check_v1(root: Path, subject: str) -> dict[str, object]:
    try:
        return build_report_v1(root.resolve(), subject)
    except (DependencyPatchRejectV1, OSError) as error:
        if isinstance(error, DependencyPatchRejectV1):
            finding = {"code": error.code, "detail": error.detail, "path": error.path}
        else:
            finding = {"code": "IO", "detail": str(error), "path": str(root)}
        return {
            "authority": NO_AUTHORITY,
            "build_host_qualified": False,
            "finding": finding,
            "ok": False,
            "proof_validity": "NOT_CLAIMED",
            "release_ready": False,
            "schema": SCHEMA,
            "status": "PATCH_GRAPH_REJECTED",
        }
