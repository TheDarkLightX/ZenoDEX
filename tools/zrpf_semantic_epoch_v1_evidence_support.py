"""Fail-closed byte and filesystem support for Semantic Epoch V1 evidence."""

from __future__ import annotations

import base64
import binascii
import copy
import hashlib
import json
import os
import re
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = (
    REPO_ROOT / "docs/research/ZRPF_SEMANTIC_EPOCH_V1_LOCAL_PROOF_EVIDENCE_20260711.json"
)
SCHEMA = "zenodex/zrpf_semantic_epoch_v1_local_proof_evidence/v1"
REPORT_SCHEMA = "zenodex/zrpf_semantic_epoch_v1_local_proof_evidence_check/v1"

# This remains empty until the final evidence object and artifact inventory are
# reviewed together. An unanchored default invocation fails closed.
EXPECTED_MANIFEST_SHA256 = ""

MAX_MANIFEST_BYTES = 512 * 1024
MAX_ARTIFACT_BYTES = 16 * 1024 * 1024
MAX_REPORT_BYTES = 64 * 1024
MAX_JOURNAL_BYTES = 4_096
HEX_DIGEST = re.compile(r"[0-9a-f]{64}")
HEX_GIT_COMMIT = re.compile(r"[0-9a-f]{40}")

JSON_ENCODING_MODES = frozenset(
    {
        "json_compact_insertion",
        "json_sorted_compact",
        "json_sorted_compact_newline",
    }
)
SOURCE_PROOF_FIELDS = {
    "meta",
    "proof",
    "proof_type",
    "schema",
    "schema_version",
    "state_hash",
}
SOURCE_PROOF_TYPE = "risc0.zenodex_recursive_spot_leaf.v1"
SOURCE_CLOSURE_FIELDS = {
    "definition",
    "file_count",
    "files",
    "git_commit",
    "schema",
    "sha256",
    "status",
    "worktree_clean",
}
SOURCE_CLOSURE_ROW_FIELDS = {"path", "role", "sha256", "size_bytes"}
SOURCE_CLOSURE_DEFINITION = (
    "sha256 of sorted role, path, sha256, and size records with NUL field "
    "separators and LF record separators"
)


class EvidenceInputError(ValueError):
    """Evidence input is ambiguous, noncanonical, or outside its bounds."""


@dataclass(frozen=True)
class LoadedJson:
    """One strict JSON object together with its authenticated raw bytes."""

    document: Any
    raw: bytes


@dataclass(frozen=True)
class ArtifactMaterial:
    """Bytes and optional strict JSON decoded from one declared artifact."""

    raw: bytes
    document: Any | None


@dataclass(frozen=True)
class SealMutationFacts:
    word_count: int
    word_index: int
    original_word: int
    mutated_word: int


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def is_digest(value: Any) -> bool:
    return isinstance(value, str) and HEX_DIGEST.fullmatch(value) is not None


def is_safe_relative_path(value: Any) -> bool:
    if not isinstance(value, str) or not value or "\\" in value or "\x00" in value:
        return False
    path = PurePosixPath(value)
    return (
        not path.is_absolute()
        and "." not in path.parts
        and ".." not in path.parts
        and str(path) == value
    )


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceInputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise EvidenceInputError(f"non-finite JSON number: {value}")


def _reject_float(value: str) -> None:
    raise EvidenceInputError(f"floating-point JSON number: {value}")


def strict_json_loads(raw: bytes) -> Any:
    """Decode bounded UTF-8 JSON while rejecting ambiguous numeric/object forms."""

    try:
        return json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
            parse_float=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as exc:
        raise EvidenceInputError(str(exc)) from exc


def canonical_manifest_bytes(document: Any) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode(
        "ascii"
    )


def canonical_artifact_bytes(document: Any, mode: str) -> bytes:
    if mode == "json_compact_insertion":
        rendered = json.dumps(document, separators=(",", ":"), ensure_ascii=True)
        return rendered.encode("ascii")
    if mode == "json_sorted_compact":
        rendered = json.dumps(
            document,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
        return rendered.encode("ascii")
    if mode == "json_sorted_compact_newline":
        rendered = json.dumps(
            document,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
        return (rendered + "\n").encode("ascii")
    raise EvidenceInputError(f"unsupported artifact JSON encoding: {mode}")


def load_manifest(path: Path) -> LoadedJson:
    try:
        path_metadata = path.lstat()
    except OSError as exc:
        raise EvidenceInputError("manifest read failed") from exc
    if stat.S_ISLNK(path_metadata.st_mode) or not stat.S_ISREG(path_metadata.st_mode):
        raise EvidenceInputError("manifest must be a non-symlink regular file")
    if path_metadata.st_size <= 0 or path_metadata.st_size > MAX_MANIFEST_BYTES:
        raise EvidenceInputError("manifest byte length is empty or exceeds the cap")
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise EvidenceInputError("manifest read failed") from exc
    try:
        opened_metadata = os.fstat(descriptor)
        if _stable_stat_identity(path_metadata) != _stable_stat_identity(opened_metadata):
            raise EvidenceInputError("manifest changed while it was opened")
        remaining = opened_metadata.st_size + 1
        chunks: list[bytes] = []
        while remaining > 0:
            chunk = os.read(descriptor, min(1_048_576, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
        final_metadata = os.fstat(descriptor)
        if _stable_stat_identity(opened_metadata) != _stable_stat_identity(final_metadata):
            raise EvidenceInputError("manifest changed while it was read")
    finally:
        os.close(descriptor)
    if len(raw) != path_metadata.st_size:
        raise EvidenceInputError("manifest length changed while it was read")
    document = strict_json_loads(raw)
    if raw != canonical_manifest_bytes(document):
        raise EvidenceInputError("manifest JSON bytes are not canonical")
    return LoadedJson(document=document, raw=raw)


def resolve_relative_directory(repo_root: Path, relative: str) -> Path:
    """Resolve one directory while rejecting traversal and every symlink hop."""

    if not is_safe_relative_path(relative):
        raise EvidenceInputError("artifact_root is not a safe relative path")
    try:
        root = repo_root.resolve(strict=True)
    except OSError as exc:
        raise EvidenceInputError("repository root is unavailable") from exc
    if not root.is_dir():
        raise EvidenceInputError("repository root is not a directory")

    current = root
    for component in PurePosixPath(relative).parts:
        current = current / component
        try:
            metadata = current.lstat()
        except OSError as exc:
            raise EvidenceInputError("artifact_root is unavailable") from exc
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
            raise EvidenceInputError("artifact_root contains a symlink or non-directory component")
    return current


def _stable_stat_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def read_relative_regular_file(
    root: Path,
    relative: str,
    *,
    max_bytes: int = MAX_ARTIFACT_BYTES,
) -> bytes:
    """Read through no-follow descriptors and bind the opened file version."""

    if not is_safe_relative_path(relative):
        raise EvidenceInputError("artifact path is not a safe relative path")
    components = PurePosixPath(relative).parts
    directory_flags = os.O_RDONLY | os.O_CLOEXEC | os.O_DIRECTORY
    file_flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        directory_flags |= os.O_NOFOLLOW
        file_flags |= os.O_NOFOLLOW

    descriptors: list[int] = []
    try:
        current_fd = os.open(root, directory_flags)
        descriptors.append(current_fd)
        for component in components[:-1]:
            current_fd = os.open(component, directory_flags, dir_fd=current_fd)
            descriptors.append(current_fd)
        file_fd = os.open(components[-1], file_flags, dir_fd=current_fd)
        descriptors.append(file_fd)
        before = os.fstat(file_fd)
        if not stat.S_ISREG(before.st_mode):
            raise EvidenceInputError("artifact is not a regular file")
        if before.st_size <= 0 or before.st_size > max_bytes:
            raise EvidenceInputError("artifact byte length is empty or exceeds the cap")

        remaining = before.st_size + 1
        chunks: list[bytes] = []
        while remaining > 0:
            chunk = os.read(file_fd, min(1_048_576, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
        after = os.fstat(file_fd)
        if _stable_stat_identity(before) != _stable_stat_identity(after):
            raise EvidenceInputError("artifact changed while it was read")
        if len(raw) != before.st_size:
            raise EvidenceInputError("artifact length changed while it was read")
        return raw
    except OSError as exc:
        raise EvidenceInputError("artifact open or read failed") from exc
    finally:
        for descriptor in reversed(descriptors):
            try:
                os.close(descriptor)
            except OSError:
                pass


def artifact_inventory(root: Path) -> tuple[list[str], list[str]]:
    """Return sorted regular-file inventory and all special/symlink rejects."""

    files: list[str] = []
    errors: list[str] = []
    try:
        for directory, directory_names, file_names in os.walk(
            root, topdown=True, followlinks=False
        ):
            directory_path = Path(directory)
            retained_directories: list[str] = []
            for name in sorted(directory_names):
                child = directory_path / name
                try:
                    mode = child.lstat().st_mode
                except OSError:
                    errors.append("artifact inventory entry became unavailable")
                    continue
                relative = child.relative_to(root).as_posix()
                if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
                    errors.append(f"artifact inventory directory rejected: {relative}")
                else:
                    retained_directories.append(name)
            directory_names[:] = retained_directories

            for name in sorted(file_names):
                child = directory_path / name
                relative = child.relative_to(root).as_posix()
                try:
                    mode = child.lstat().st_mode
                except OSError:
                    errors.append("artifact inventory entry became unavailable")
                    continue
                if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
                    errors.append(f"artifact inventory file rejected: {relative}")
                else:
                    files.append(relative)
    except OSError:
        errors.append("artifact inventory walk failed")
    return sorted(files), errors


def load_artifact(
    artifact_root: Path,
    row: dict[str, Any],
) -> ArtifactMaterial:
    relative = row["path"]
    kind = row.get("kind")
    cap = (
        MAX_REPORT_BYTES
        if isinstance(kind, str) and kind.endswith("report")
        else MAX_ARTIFACT_BYTES
    )
    raw = read_relative_regular_file(artifact_root, relative, max_bytes=cap)
    if len(raw) != row["size_bytes"]:
        raise EvidenceInputError(f"artifact size mismatch: {row['id']}")
    if sha256_bytes(raw) != row["sha256"]:
        raise EvidenceInputError(f"artifact SHA-256 mismatch: {row['id']}")
    mode = row["encoding"]
    if not isinstance(mode, str) or mode not in JSON_ENCODING_MODES:
        raise EvidenceInputError(f"artifact encoding is unsupported: {row['id']}")
    document = strict_json_loads(raw)
    if raw != canonical_artifact_bytes(document, mode):
        raise EvidenceInputError(f"artifact JSON bytes are not canonical: {row['id']}")
    return ArtifactMaterial(raw=raw, document=document)


def receipt_journal_facts(document: Any) -> tuple[int, str]:
    """Check the outer receipt envelope without claiming seal verification."""

    if not isinstance(document, dict) or set(document) != {
        "inner",
        "journal",
        "metadata",
    }:
        raise EvidenceInputError("RISC0 receipt outer field set mismatch")
    inner = document.get("inner")
    if not isinstance(inner, dict) or set(inner) != {"Succinct"}:
        raise EvidenceInputError("RISC0 receipt is not structurally labeled Succinct")
    journal = document.get("journal")
    if not isinstance(journal, dict) or set(journal) != {"bytes"}:
        raise EvidenceInputError("RISC0 receipt journal envelope mismatch")
    values = journal.get("bytes")
    if (
        not isinstance(values, list)
        or not values
        or len(values) > MAX_JOURNAL_BYTES
        or any(type(value) is not int or value < 0 or value > 255 for value in values)
    ):
        raise EvidenceInputError("RISC0 receipt journal bytes are invalid")
    raw = bytes(values)
    return len(raw), sha256_bytes(raw)


def source_proof_receipt_sha256(document: Any) -> str:
    """Bind the canonical embedded source receipt without verifying its seal."""

    if not isinstance(document, dict) or set(document) != SOURCE_PROOF_FIELDS:
        raise EvidenceInputError("source proof artifact outer field set mismatch")
    if (
        document.get("schema") != "tau_state_proof"
        or type(document.get("schema_version")) is not int
        or document.get("schema_version") != 1
        or document.get("proof_type") != SOURCE_PROOF_TYPE
        or not is_digest(document.get("state_hash"))
    ):
        raise EvidenceInputError("source proof artifact header mismatch")
    metadata = document.get("meta")
    if not isinstance(metadata, dict) or any(
        (
            metadata.get("proof_type") != SOURCE_PROOF_TYPE,
            metadata.get("proof_profile") != "recursive_spot_leaf_v1",
            metadata.get("receipt_codec") != "risc0_receipt_canonical_serde_json_depth128_v1",
            metadata.get("receipt_kind") != "succinct",
            metadata.get("receipt_hashfn") != "poseidon2",
        )
    ):
        raise EvidenceInputError("source proof governed metadata mismatch")
    proof = document.get("proof")
    if not isinstance(proof, str) or not proof or len(proof) > MAX_ARTIFACT_BYTES * 2:
        raise EvidenceInputError("source proof base64 is invalid or oversized")
    try:
        receipt_bytes = base64.b64decode(proof.encode("ascii"), validate=True)
    except (UnicodeEncodeError, binascii.Error) as exc:
        raise EvidenceInputError("source proof base64 is invalid") from exc
    if (
        not receipt_bytes
        or len(receipt_bytes) > MAX_ARTIFACT_BYTES
        or base64.b64encode(receipt_bytes).decode("ascii") != proof
    ):
        raise EvidenceInputError("source proof base64 is noncanonical or oversized")
    receipt = strict_json_loads(receipt_bytes)
    if receipt_bytes != canonical_artifact_bytes(receipt, "json_compact_insertion"):
        raise EvidenceInputError("embedded source receipt JSON bytes are not canonical")
    receipt_journal_facts(receipt)
    return sha256_bytes(receipt_bytes)


def exact_succinct_seal_word_one_xor_one(
    source: Any,
    candidate: Any,
) -> SealMutationFacts:
    """Require one exact word-1 XOR-1 mutation and no other JSON change."""

    receipt_journal_facts(source)
    receipt_journal_facts(candidate)
    try:
        source_seal = source["inner"]["Succinct"]["seal"]
        candidate_seal = candidate["inner"]["Succinct"]["seal"]
    except (KeyError, TypeError) as exc:
        raise EvidenceInputError("Succinct seal envelope is malformed") from exc
    if (
        not isinstance(source_seal, list)
        or not isinstance(candidate_seal, list)
        or len(source_seal) <= 1
        or len(source_seal) != len(candidate_seal)
        or any(
            type(word) is not int or word < 0 or word > 0xFFFF_FFFF
            for word in (*source_seal, *candidate_seal)
        )
    ):
        raise EvidenceInputError("Succinct seal words are invalid")
    differences = [
        (index, original, mutated)
        for index, (original, mutated) in enumerate(zip(source_seal, candidate_seal, strict=True))
        if original != mutated
    ]
    if len(differences) != 1:
        raise EvidenceInputError("Succinct seal candidate must change exactly one word")
    word_index, original_word, mutated_word = differences[0]
    if word_index != 1 or original_word ^ mutated_word != 1:
        raise EvidenceInputError("Succinct seal candidate must XOR word 1 by exactly 1")
    restored = copy.deepcopy(candidate)
    restored["inner"]["Succinct"]["seal"][word_index] = original_word
    if canonical_artifact_bytes(restored, "json_compact_insertion") != canonical_artifact_bytes(
        source, "json_compact_insertion"
    ):
        raise EvidenceInputError("Succinct mutation changes non-seal receipt bytes")
    return SealMutationFacts(
        word_count=len(source_seal),
        word_index=word_index,
        original_word=original_word,
        mutated_word=mutated_word,
    )


def source_closure_facts(document: Any) -> tuple[int, str]:
    """Recompute the exact retained source-closure record root."""

    if not isinstance(document, dict) or set(document) != SOURCE_CLOSURE_FIELDS:
        raise EvidenceInputError("source closure outer field set mismatch")
    files = document.get("files")
    if not isinstance(files, list) or not files:
        raise EvidenceInputError("source closure files are missing")
    if (
        document.get("schema") != "zenodex/zrpf_v3_frozen_source_closure/v1"
        or document.get("status") != "frozen_source_closure"
        or document.get("definition") != SOURCE_CLOSURE_DEFINITION
        or document.get("worktree_clean") is not True
        or not isinstance(document.get("git_commit"), str)
        or HEX_GIT_COMMIT.fullmatch(document["git_commit"]) is None
        or type(document.get("file_count")) is not int
        or document.get("file_count") != len(files)
        or not is_digest(document.get("sha256"))
    ):
        raise EvidenceInputError("source closure header mismatch")
    paths: list[str] = []
    hasher = hashlib.sha256()
    for index, row in enumerate(files):
        if not isinstance(row, dict) or set(row) != SOURCE_CLOSURE_ROW_FIELDS:
            raise EvidenceInputError(f"source closure row field mismatch: {index}")
        path = row.get("path")
        role = row.get("role")
        digest = row.get("sha256")
        size = row.get("size_bytes")
        if (
            not isinstance(path, str)
            or not is_safe_relative_path(path)
            or not isinstance(role, str)
            or not role
            or not isinstance(digest, str)
            or not is_digest(digest)
            or type(size) is not int
            or size <= 0
            or size > MAX_ARTIFACT_BYTES
        ):
            raise EvidenceInputError(f"source closure row is invalid: {index}")
        paths.append(path)
        hasher.update(role.encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(path.encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(digest.encode("ascii"))
        hasher.update(b"\0")
        hasher.update(str(size).encode("ascii"))
        hasher.update(b"\n")
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        raise EvidenceInputError("source closure paths must be unique and sorted")
    computed = hasher.hexdigest()
    if computed != document.get("sha256"):
        raise EvidenceInputError("source closure SHA-256 mismatch")
    return len(files), computed
