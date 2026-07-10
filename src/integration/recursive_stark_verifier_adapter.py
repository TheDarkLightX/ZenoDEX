"""Authenticated adapter from the pinned RISC0 CLI to exact-once admission.

The adapter owns the process boundary. It never accepts caller-projected
``verified`` booleans. The pinned CLI must verify the aggregate receipt, match
ledger-owned recursive expectations, recompose the disclosed recursive input,
and emit root-bound element facts before this module admits anything.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import resource
import selectors
import signal
import stat
import struct
import subprocess
import time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, BinaryIO, Mapping, cast

from src.core.recursive_stark_admission import (
    RecursiveStarkAdmissionResult,
    RecursiveStarkAdmissionState,
    TrustedRecursiveStarkAdmissionPolicy,
    VerifiedRecursiveStarkRootFacts,
    admit_verified_recursive_stark_root,
)

VERIFIED_FACTS_SCHEMA_V1 = "zenodex.verified_recursive_stark_root_facts.v1"
AUTHORITY_MANIFEST_SCHEMA_V1 = "zenodex.recursive_stark_verifier_authority.v1"
RECEIPT_CODEC_V1 = "risc0_receipt_canonical_serde_json_depth128_v1"
MAX_AUTHORITY_MANIFEST_BYTES = 1024 * 1024
MAX_VERIFIER_REQUEST_BYTES = 64 * 1024 * 1024
MAX_VERIFIER_STDOUT_BYTES = 16 * 1024 * 1024
MAX_VERIFIER_STDERR_BYTES = 1024 * 1024
MAX_VERIFIER_EXECUTABLE_BYTES = 256 * 1024 * 1024
DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES = 2 * 1024 * 1024 * 1024
DEFAULT_VERIFIER_STACK_BYTES = 32 * 1024 * 1024

_FACT_KEYS = frozenset(
    {
        "schema",
        "aggregate_image_id",
        "receipt_codec",
        "receipt_kind",
        "receipt_hashfn",
        "receipt_verifier_parameters",
        "receipt_control_id",
        "chain_id",
        "epoch_id",
        "proof_profile",
        "root_journal_hash",
        "verifier_set_root",
        "public_policy_hash",
        "child_verification_claim_hashes",
        "child_verification_claims_root",
        "accepted_receipt_ids",
        "accepted_receipts_root",
        "cross_shard_message_ids",
        "cross_shard_message_ids_root",
    }
)


class RecursiveStarkVerificationError(ValueError):
    """Stable failure at the authenticated verifier-process boundary."""


class RecursiveVerifierExecutableFormat(str, Enum):
    """Dependency-closure policy for the pinned verifier executable."""

    STATIC_ELF_X86_64 = "static_elf_x86_64"
    TEST_SCRIPT = "test_script"


@dataclass(frozen=True)
class PinnedRecursiveStarkVerifier:
    """Verifier binary and policy derived from one authenticated manifest.

    ``authority_manifest_sha256`` is a bootstrap identifier. Release code must
    obtain it from separately governed ledger or release state. The executable
    digest, format, and trusted expectations are derived exclusively from the
    canonical manifest bytes matching that identifier. Constructing both from
    proof-supplied data provides local test evidence only.
    """

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 60
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)
    trusted_expectations: Mapping[str, Any] = field(init=False)
    executable_format: RecursiveVerifierExecutableFormat = field(init=False)
    _trusted_expectations_json: bytes = field(init=False, repr=False)

    def __post_init__(self) -> None:
        if not self.executable.is_absolute():
            raise ValueError("recursive verifier executable must be an absolute path")
        if len(self.authority_manifest_sha256) != 64 or any(
            c not in "0123456789abcdef" for c in self.authority_manifest_sha256
        ):
            raise ValueError(
                "recursive verifier authority_manifest_sha256 must be lowercase 64-character hex"
            )
        if self.timeout_seconds <= 0 or self.timeout_seconds > 300:
            raise ValueError("recursive verifier timeout_seconds must be in 1..300")
        if self.max_address_space_bytes < 256 * 1024 * 1024:
            raise ValueError("recursive verifier address-space limit is too small")
        if self.max_stack_bytes < 1024 * 1024:
            raise ValueError("recursive verifier stack limit is too small")
        executable_sha256, executable_format, canonical_expectations = (
            _parse_authority_manifest_v1(
                self.authority_manifest_json,
                expected_sha256=self.authority_manifest_sha256,
            )
        )
        decoded_expectations = json.loads(canonical_expectations)
        object.__setattr__(self, "sha256", executable_sha256)
        object.__setattr__(self, "executable_format", executable_format)
        object.__setattr__(self, "trusted_expectations", decoded_expectations)
        object.__setattr__(self, "_trusted_expectations_json", canonical_expectations)

    def verify_and_admit(
        self,
        *,
        state: RecursiveStarkAdmissionState,
        proof: Mapping[str, Any],
        recursive_input: Mapping[str, Any],
    ) -> RecursiveStarkAdmissionResult:
        """Verify one root and feed only authenticated facts to the pure kernel."""

        trusted_expectations = json.loads(self._trusted_expectations_json)
        request = _verification_request(
            proof=proof,
            recursive_input=recursive_input,
            trusted_expectations=trusted_expectations,
        )
        request_bytes = _bounded_canonical_json_bytes(request, "verification request")
        executable_fd: int | None = None
        try:
            executable_fd, actual_hash = _sealed_executable_snapshot(
                self.executable,
                executable_format=self.executable_format,
            )
            if actual_hash != self.sha256:
                raise RecursiveStarkVerificationError("recursive verifier binary hash mismatch")
            process = subprocess.Popen(
                [f"/proc/self/fd/{executable_fd}"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
                pass_fds=(executable_fd,),
                cwd="/",
                env=_verifier_environment(),
            )
            try:
                self._apply_resource_limits(process.pid)
            except (OSError, ValueError) as exc:
                _terminate_process_group(process)
                raise RecursiveStarkVerificationError(
                    f"failed to apply recursive verifier resource limits: {exc}"
                ) from exc
            stdout, stderr, completed_returncode = _communicate_bounded(
                process,
                request_bytes=request_bytes,
                timeout_seconds=self.timeout_seconds,
            )
        except subprocess.TimeoutExpired as exc:
            raise RecursiveStarkVerificationError("recursive verifier timed out") from exc
        except OSError as exc:
            raise RecursiveStarkVerificationError(
                f"recursive verifier process failed: {exc}"
            ) from exc
        finally:
            if executable_fd is not None:
                os.close(executable_fd)
        if completed_returncode != 0:
            raise RecursiveStarkVerificationError(
                f"recursive verifier exited with status {completed_returncode}"
            )
        try:
            payload = json.loads(
                stdout,
                object_pairs_hook=_reject_duplicate_object_keys,
                parse_constant=_reject_json_constant,
            )
        except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
            raise RecursiveStarkVerificationError(
                "recursive verifier stdout must be one JSON object"
            ) from exc
        facts = parse_authenticated_recursive_facts(
            payload,
            trusted_expectations=trusted_expectations,
        )
        policy = _trusted_policy(trusted_expectations)
        return admit_verified_recursive_stark_root(state, facts, policy)

    def _apply_resource_limits(self, process_id: int) -> None:
        resource.prlimit(
            process_id,
            resource.RLIMIT_AS,
            (self.max_address_space_bytes, self.max_address_space_bytes),
        )
        resource.prlimit(
            process_id,
            resource.RLIMIT_STACK,
            (self.max_stack_bytes, self.max_stack_bytes),
        )
        cpu_seconds = self.timeout_seconds + 1
        resource.prlimit(
            process_id,
            resource.RLIMIT_CPU,
            (cpu_seconds, cpu_seconds),
        )
        resource.prlimit(process_id, resource.RLIMIT_CORE, (0, 0))
        resource.prlimit(process_id, resource.RLIMIT_FSIZE, (0, 0))
        resource.prlimit(process_id, resource.RLIMIT_NOFILE, (32, 32))
        resource.prlimit(process_id, resource.RLIMIT_NPROC, (1, 1))


def recursive_stark_authority_manifest_bytes_v1(
    *,
    executable_sha256: str,
    trusted_expectations: Mapping[str, Any],
    executable_format: RecursiveVerifierExecutableFormat = (
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64
    ),
) -> bytes:
    """Build canonical bytes for a separately governed authority record."""

    if len(executable_sha256) != 64 or any(
        char not in "0123456789abcdef" for char in executable_sha256
    ):
        raise ValueError("recursive verifier sha256 must be lowercase 64-character hex")
    if not isinstance(executable_format, RecursiveVerifierExecutableFormat):
        raise ValueError("recursive verifier executable_format unsupported")
    expectations_bytes = _bounded_canonical_json_bytes(
        trusted_expectations,
        "trusted expectations",
    )
    expectations = json.loads(expectations_bytes)
    if not isinstance(expectations, dict):
        raise ValueError("recursive verifier trusted_expectations must be an object")
    raw = _canonical_json_bytes(
        {
            "schema": AUTHORITY_MANIFEST_SCHEMA_V1,
            "executable_sha256": executable_sha256,
            "executable_format": executable_format.value,
            "trusted_expectations": expectations,
        }
    )
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError(
            f"recursive verifier authority manifest exceeds {MAX_AUTHORITY_MANIFEST_BYTES} bytes"
        )
    return raw


def _parse_authority_manifest_v1(
    raw: bytes,
    *,
    expected_sha256: str,
) -> tuple[str, RecursiveVerifierExecutableFormat, bytes]:
    if not isinstance(raw, bytes):
        raise ValueError("recursive verifier authority manifest must be bytes")
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError(
            f"recursive verifier authority manifest exceeds {MAX_AUTHORITY_MANIFEST_BYTES} bytes"
        )
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("recursive verifier authority manifest hash mismatch")
    try:
        manifest = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_duplicate_object_keys,
            parse_float=_reject_authority_float,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("recursive verifier authority manifest must be canonical JSON") from exc
    if not isinstance(manifest, dict) or set(manifest) != {
        "schema",
        "executable_sha256",
        "executable_format",
        "trusted_expectations",
    }:
        raise ValueError("recursive verifier authority manifest schema mismatch")
    if manifest.get("schema") != AUTHORITY_MANIFEST_SCHEMA_V1:
        raise ValueError("recursive verifier authority manifest schema mismatch")
    if _canonical_json_bytes(manifest) != raw:
        raise ValueError("recursive verifier authority manifest must be canonical JSON")
    executable_sha256 = manifest.get("executable_sha256")
    if not isinstance(executable_sha256, str) or len(executable_sha256) != 64 or any(
        char not in "0123456789abcdef" for char in executable_sha256
    ):
        raise ValueError("recursive verifier authority executable_sha256 invalid")
    try:
        executable_format = RecursiveVerifierExecutableFormat(
            manifest.get("executable_format")
        )
    except (TypeError, ValueError) as exc:
        raise ValueError("recursive verifier authority executable_format unsupported") from exc
    expectations = manifest.get("trusted_expectations")
    if not isinstance(expectations, dict):
        raise ValueError("recursive verifier authority trusted_expectations must be an object")
    expectations_bytes = _bounded_canonical_json_bytes(
        expectations,
        "trusted expectations",
    )
    return executable_sha256, executable_format, expectations_bytes


def _reject_authority_float(value: str) -> object:
    raise ValueError(f"authority manifest float is forbidden: {value}")


def parse_authenticated_recursive_facts(
    payload: object,
    *,
    trusted_expectations: Mapping[str, Any],
) -> VerifiedRecursiveStarkRootFacts:
    """Parse the strict facts emitted only after successful CLI verification."""

    response = _mapping(payload, "recursive verifier response")
    if set(response) != {"ok", "verified_recursive_facts"}:
        raise RecursiveStarkVerificationError("recursive verifier response schema mismatch")
    if response.get("ok") is not True:
        raise RecursiveStarkVerificationError("recursive verifier did not accept proof")
    facts = _mapping(response.get("verified_recursive_facts"), "verified_recursive_facts")
    if set(facts) != _FACT_KEYS:
        raise RecursiveStarkVerificationError("verified_recursive_facts schema mismatch")
    if facts.get("schema") != VERIFIED_FACTS_SCHEMA_V1:
        raise RecursiveStarkVerificationError("verified_recursive_facts schema unsupported")
    if facts.get("receipt_kind") != "succinct":
        raise RecursiveStarkVerificationError("verified recursive receipt kind mismatch")

    _expect_equal(facts, trusted_expectations, "aggregate_image_id", "risc0_image_id")
    _expect_equal(facts, trusted_expectations, "receipt_codec", "receipt_codec")
    _expect_equal(facts, trusted_expectations, "receipt_kind", "receipt_kind")
    _expect_equal(facts, trusted_expectations, "receipt_hashfn", "receipt_hashfn")
    for key in ("receipt_verifier_parameters", "receipt_control_id"):
        _expect_same_hash(facts, trusted_expectations, key)
    for key in ("chain_id", "epoch_id", "proof_profile"):
        _expect_equal(facts, trusted_expectations, key, key)
    for key in (
        "verifier_set_root",
        "public_policy_hash",
        "child_verification_claims_root",
        "accepted_receipts_root",
        "cross_shard_message_ids_root",
    ):
        _expect_same_hash(facts, trusted_expectations, key)

    return VerifiedRecursiveStarkRootFacts(
        chain_id=_str(facts, "chain_id"),
        epoch_id=_int(facts, "epoch_id"),
        proof_profile=_str(facts, "proof_profile"),
        root_journal_hash=_str(facts, "root_journal_hash"),
        verifier_set_root=_str(facts, "verifier_set_root"),
        public_policy_hash=_str(facts, "public_policy_hash"),
        child_verification_claim_hashes=_str_tuple(facts, "child_verification_claim_hashes"),
        child_verification_claims_root=_str(facts, "child_verification_claims_root"),
        accepted_receipt_ids=_str_tuple(facts, "accepted_receipt_ids"),
        accepted_receipts_root=_str(facts, "accepted_receipts_root"),
        cross_shard_message_ids=_str_tuple(facts, "cross_shard_message_ids"),
        cross_shard_message_ids_root=_str(facts, "cross_shard_message_ids_root"),
    )


def _verification_request(
    *,
    proof: Mapping[str, Any],
    recursive_input: Mapping[str, Any],
    trusted_expectations: Mapping[str, Any],
) -> dict[str, Any]:
    post_state_root = trusted_expectations.get("post_state_root")
    if not isinstance(post_state_root, str):
        raise RecursiveStarkVerificationError(
            "trusted_expectations.post_state_root must be a string"
        )
    return {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": post_state_root,
        "proof": _canonical_copy(proof),
        "recursive_input": _canonical_copy(recursive_input),
        "recursive_expectations": _canonical_copy(trusted_expectations),
    }


def _trusted_policy(
    trusted_expectations: Mapping[str, Any],
) -> TrustedRecursiveStarkAdmissionPolicy:
    return TrustedRecursiveStarkAdmissionPolicy(
        expected_chain_id=_expectation_str(trusted_expectations, "chain_id"),
        expected_epoch_id=_expectation_int(trusted_expectations, "epoch_id"),
        expected_proof_profile=_expectation_str(trusted_expectations, "proof_profile"),
        expected_verifier_set_root=_prefixed_hash(
            _expectation_str(trusted_expectations, "verifier_set_root")
        ),
        expected_public_policy_hash=_prefixed_hash(
            _expectation_str(trusted_expectations, "public_policy_hash")
        ),
    )


def _expect_equal(
    facts: Mapping[str, Any],
    expectations: Mapping[str, Any],
    facts_key: str,
    expectation_key: str,
) -> None:
    if facts.get(facts_key) != expectations.get(expectation_key):
        raise RecursiveStarkVerificationError(
            f"verified_recursive_facts.{facts_key} trusted expectation mismatch"
        )


def _expect_same_hash(
    facts: Mapping[str, Any],
    expectations: Mapping[str, Any],
    key: str,
) -> None:
    fact = facts.get(key)
    expected = expectations.get(key)
    if not isinstance(fact, str) or not isinstance(expected, str):
        raise RecursiveStarkVerificationError(f"{key} must be a hex string")
    if _prefixed_hash(fact) != _prefixed_hash(expected):
        raise RecursiveStarkVerificationError(
            f"verified_recursive_facts.{key} trusted expectation mismatch"
        )


def _prefixed_hash(value: str) -> str:
    normalized = value.removeprefix("0x")
    if len(normalized) != 64 or any(c not in "0123456789abcdef" for c in normalized):
        raise RecursiveStarkVerificationError("hash must be lowercase 32-byte hex")
    return "0x" + normalized


def _mapping(value: object, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise RecursiveStarkVerificationError(f"{name} must be an object")
    return value


def _str(values: Mapping[str, Any], key: str) -> str:
    value = values.get(key)
    if not isinstance(value, str):
        raise RecursiveStarkVerificationError(f"verified_recursive_facts.{key} must be a string")
    return value


def _int(values: Mapping[str, Any], key: str) -> int:
    value = values.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise RecursiveStarkVerificationError(f"verified_recursive_facts.{key} must be an int")
    return value


def _str_tuple(values: Mapping[str, Any], key: str) -> tuple[str, ...]:
    value = values.get(key)
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
        raise RecursiveStarkVerificationError(
            f"verified_recursive_facts.{key} must be a string list"
        )
    return tuple(value)


def _expectation_str(values: Mapping[str, Any], key: str) -> str:
    value = values.get(key)
    if not isinstance(value, str):
        raise RecursiveStarkVerificationError(f"trusted_expectations.{key} must be a string")
    return value


def _expectation_int(values: Mapping[str, Any], key: str) -> int:
    value = values.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise RecursiveStarkVerificationError(f"trusted_expectations.{key} must be an int")
    return value


def _canonical_copy(value: Mapping[str, Any]) -> dict[str, Any]:
    try:
        copied = json.loads(_bounded_canonical_json_bytes(value, "verification input"))
    except RecursiveStarkVerificationError:
        raise
    except (TypeError, ValueError, json.JSONDecodeError, RecursionError) as exc:
        raise RecursiveStarkVerificationError("verification input must be canonical JSON") from exc
    if not isinstance(copied, dict):
        raise RecursiveStarkVerificationError("verification input must be a JSON object")
    return copied


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _bounded_canonical_json_bytes(value: object, label: str) -> bytes:
    try:
        encoded = _canonical_json_bytes(value)
    except (TypeError, ValueError, RecursionError) as exc:
        raise RecursiveStarkVerificationError(f"{label} must be canonical JSON") from exc
    if len(encoded) > MAX_VERIFIER_REQUEST_BYTES:
        raise RecursiveStarkVerificationError(
            f"{label} exceeds {MAX_VERIFIER_REQUEST_BYTES} byte limit"
        )
    return encoded


def _sealed_executable_snapshot(
    path: Path,
    *,
    executable_format: RecursiveVerifierExecutableFormat,
) -> tuple[int, str]:
    if not hasattr(os, "memfd_create"):
        raise RecursiveStarkVerificationError("sealed verifier execution requires memfd_create")
    source_flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        source_flags |= os.O_NOFOLLOW
    source_fd = os.open(path, source_flags)
    memfd = -1
    try:
        source_stat = os.fstat(source_fd)
        if not stat.S_ISREG(source_stat.st_mode):
            raise RecursiveStarkVerificationError(
                "recursive verifier executable must be a regular non-symlink file"
            )
        if source_stat.st_size <= 0 or source_stat.st_size > MAX_VERIFIER_EXECUTABLE_BYTES:
            raise RecursiveStarkVerificationError("recursive verifier executable size is invalid")
        memfd = os.memfd_create(
            "zenodex-recursive-stark-verifier",
            flags=os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING,
        )
        digest = hashlib.sha256()
        copied_bytes = 0
        while True:
            chunk = os.read(source_fd, 1024 * 1024)
            if not chunk:
                break
            copied_bytes += len(chunk)
            if copied_bytes > MAX_VERIFIER_EXECUTABLE_BYTES:
                raise RecursiveStarkVerificationError(
                    "recursive verifier executable exceeds size limit"
                )
            digest.update(chunk)
            view = memoryview(chunk)
            while view:
                written = os.write(memfd, view)
                if written <= 0:
                    raise RecursiveStarkVerificationError(
                        "failed to copy recursive verifier executable"
                    )
                view = view[written:]
        if copied_bytes != source_stat.st_size:
            raise RecursiveStarkVerificationError(
                "recursive verifier executable changed while being copied"
            )
        os.fchmod(memfd, 0o500)
        os.lseek(memfd, 0, os.SEEK_SET)
        if executable_format is RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64:
            _require_static_x86_64_elf(memfd, copied_bytes)
        elif executable_format is not RecursiveVerifierExecutableFormat.TEST_SCRIPT:
            raise RecursiveStarkVerificationError(
                "recursive verifier executable format unsupported"
            )
        seals = (
            fcntl.F_SEAL_WRITE
            | fcntl.F_SEAL_GROW
            | fcntl.F_SEAL_SHRINK
            | fcntl.F_SEAL_SEAL
        )
        fcntl.fcntl(memfd, fcntl.F_ADD_SEALS, seals)
        return memfd, digest.hexdigest()
    except Exception:
        if memfd >= 0:
            os.close(memfd)
        raise
    finally:
        os.close(source_fd)


def _require_static_x86_64_elf(descriptor: int, file_size: int) -> None:
    header = os.pread(descriptor, 64, 0)
    if len(header) != 64 or header[:4] != b"\x7fELF":
        raise RecursiveStarkVerificationError("recursive verifier must be a static ELF")
    if header[4] != 2 or header[5] != 1 or header[6] != 1:
        raise RecursiveStarkVerificationError(
            "recursive verifier ELF class, byte order, or version unsupported"
        )
    elf_type, machine = struct.unpack_from("<HH", header, 16)
    if elf_type not in (2, 3) or machine != 62:
        raise RecursiveStarkVerificationError(
            "recursive verifier must be an x86_64 executable ELF"
        )
    program_header_offset = struct.unpack_from("<Q", header, 32)[0]
    program_header_size, program_header_count = struct.unpack_from("<HH", header, 54)
    if program_header_size < 56 or program_header_count == 0:
        raise RecursiveStarkVerificationError("recursive verifier ELF program headers invalid")
    table_size = program_header_size * program_header_count
    if (
        program_header_offset > file_size
        or table_size > file_size
        or program_header_offset + table_size > file_size
    ):
        raise RecursiveStarkVerificationError("recursive verifier ELF program headers truncated")
    program_headers = os.pread(descriptor, table_size, program_header_offset)
    if len(program_headers) != table_size:
        raise RecursiveStarkVerificationError("recursive verifier ELF program headers truncated")
    for index in range(program_header_count):
        program_type = struct.unpack_from(
            "<I",
            program_headers,
            index * program_header_size,
        )[0]
        if program_type == 3:
            raise RecursiveStarkVerificationError(
                "recursive verifier ELF has a dynamic interpreter"
            )


def _verifier_environment() -> dict[str, str]:
    return {
        "PATH": "/usr/bin:/bin",
        "LANG": "C",
        "LC_ALL": "C",
        "TZ": "UTC",
        "RISC0_DEV_MODE": "0",
    }


def _communicate_bounded(
    process: subprocess.Popen[bytes],
    *,
    request_bytes: bytes,
    timeout_seconds: int,
) -> tuple[bytes, bytes, int]:
    if process.stdin is None or process.stdout is None or process.stderr is None:
        _terminate_process_group(process)
        raise RecursiveStarkVerificationError("recursive verifier pipes unavailable")

    selector = selectors.DefaultSelector()
    streams = (process.stdin, process.stdout, process.stderr)
    for stream in streams:
        os.set_blocking(stream.fileno(), False)
    selector.register(process.stdin, selectors.EVENT_WRITE, "stdin")
    selector.register(process.stdout, selectors.EVENT_READ, "stdout")
    selector.register(process.stderr, selectors.EVENT_READ, "stderr")

    request_offset = 0
    stdout = bytearray()
    stderr = bytearray()
    deadline = time.monotonic() + timeout_seconds
    try:
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise subprocess.TimeoutExpired(process.args, timeout_seconds)
            events = selector.select(remaining)
            if not events:
                raise subprocess.TimeoutExpired(process.args, timeout_seconds)
            for key, _mask in events:
                stream = cast(BinaryIO, key.fileobj)
                if key.data == "stdin":
                    if request_offset == len(request_bytes):
                        selector.unregister(stream)
                        stream.close()
                        continue
                    try:
                        written = os.write(
                            stream.fileno(),
                            request_bytes[request_offset : request_offset + 64 * 1024],
                        )
                    except BrokenPipeError:
                        selector.unregister(stream)
                        stream.close()
                    else:
                        request_offset += written
                        if request_offset == len(request_bytes):
                            selector.unregister(stream)
                            stream.close()
                    continue

                try:
                    chunk = os.read(stream.fileno(), 64 * 1024)
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(stream)
                    stream.close()
                    continue
                output = stdout if key.data == "stdout" else stderr
                output.extend(chunk)
                limit = (
                    MAX_VERIFIER_STDOUT_BYTES
                    if key.data == "stdout"
                    else MAX_VERIFIER_STDERR_BYTES
                )
                if len(output) > limit:
                    raise RecursiveStarkVerificationError(
                        f"recursive verifier {key.data} exceeds limit"
                    )

        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(process.args, timeout_seconds)
        returncode = process.wait(timeout=remaining)
        return bytes(stdout), bytes(stderr), returncode
    except Exception:
        _terminate_process_group(process)
        raise
    finally:
        selector.close()
        for stream in streams:
            if not stream.closed:
                stream.close()


def _terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    if process.poll() is None:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def _reject_duplicate_object_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise ValueError(f"invalid JSON constant: {value}")
