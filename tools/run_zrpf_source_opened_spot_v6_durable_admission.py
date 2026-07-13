#!/usr/bin/env python3
"""Verify, durably admit, reopen, and exactly retry one Spot V6 settlement.

The runner exercises the existing pinned verifier and SQLite transaction store.
Its report is local durability evidence and always preserves settlement,
release, and production authority as false.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import stat
import sys
from pathlib import Path
from typing import Any

from src.integration.zrpf_atomic_settlement_store import (
    SQLiteZrpfAtomicSettlementStoreV1,
)
from src.integration.zrpf_atomic_settlement_store_types import (
    ZrpfAtomicSettlementStoreErrorV1,
)
from src.integration.zrpf_source_opened_spot_v6_verifier_adapter import (
    MAX_SOURCE_OPENED_SPOT_V6_GUEST_INPUT_BYTES,
    MAX_SOURCE_OPENED_SPOT_V6_RECEIPT_BYTES,
    PinnedSourceOpenedSpotSettlementVerifierV6,
    SourceOpenedSpotV6VerificationError,
)
from src.state.canonical import canonical_json_bytes

REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_durable_admission_evidence/v1"
ERROR_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_durable_admission_error/v1"
MAX_AUTHORITY_MANIFEST_INPUT_BYTES = 64 * 1024
MAX_DATABASE_BYTES = 256 * 1024 * 1024
MAX_REPORT_BYTES = 64 * 1024
DEFAULT_BUSY_TIMEOUT_MS = 5_000

_PREFIXED_HASH = re.compile(r"0x[0-9a-f]{64}")
_BARE_HASH = re.compile(r"[0-9a-f]{64}")


class DurableAdmissionEvidenceError(ValueError):
    """Stable fail-closed durable-admission evidence rejection."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(detail)
        self.code = code


def run_durable_admission_evidence(
    *,
    verifier_path: Path,
    authority_manifest_path: Path,
    settlement_receipt_path: Path,
    guest_input_path: Path,
    database_path: Path,
    output_path: Path,
    expected_authority_manifest_sha256: str,
    genesis_settlement_state_root: str,
    busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS,
) -> tuple[dict[str, Any], bytes]:
    """Commit a fresh proof, reopen twice, and require an exact idempotent retry."""

    genesis_root = _require_prefixed_hash(
        genesis_settlement_state_root,
        "genesis settlement state root",
    )
    expected_manifest_sha256 = _require_bare_hash(
        expected_authority_manifest_sha256,
        "expected authority manifest sha256",
    )
    if type(busy_timeout_ms) is not int or not 1 <= busy_timeout_ms <= 60_000:
        raise DurableAdmissionEvidenceError(
            "invalid_busy_timeout",
            "busy timeout must be an integer in 1..60000",
        )
    verifier = _resolve_executable(verifier_path)
    manifest = _read_bounded_regular_file(
        authority_manifest_path,
        maximum=MAX_AUTHORITY_MANIFEST_INPUT_BYTES,
        label="authority manifest",
    )
    receipt = _read_bounded_regular_file(
        settlement_receipt_path,
        maximum=MAX_SOURCE_OPENED_SPOT_V6_RECEIPT_BYTES,
        label="settlement receipt",
    )
    guest_input = _read_bounded_regular_file(
        guest_input_path,
        maximum=MAX_SOURCE_OPENED_SPOT_V6_GUEST_INPUT_BYTES,
        label="guest input",
    )
    database = _resolve_fresh_path(database_path, "database")
    output = _resolve_fresh_path(output_path, "output")
    _require_distinct_paths(
        verifier,
        authority_manifest_path,
        settlement_receipt_path,
        guest_input_path,
        database,
        output,
    )

    manifest_sha256 = hashlib.sha256(manifest).hexdigest()
    if manifest_sha256 != expected_manifest_sha256:
        raise DurableAdmissionEvidenceError(
            "authority_manifest_hash_mismatch",
            "authority manifest does not match the governed expected digest",
        )
    adapter = PinnedSourceOpenedSpotSettlementVerifierV6(
        executable=verifier,
        authority_manifest_json=manifest,
        authority_manifest_sha256=manifest_sha256,
    )
    first_store = SQLiteZrpfAtomicSettlementStoreV1(
        database,
        genesis_settlement_state_root=genesis_root,
        busy_timeout_ms=busy_timeout_ms,
    )
    _require_store_non_authority(first_store)
    first = adapter.verify_and_commit(
        store=first_store,
        expected_admission_cursor=first_store.read_admission_cursor(),
        expected_settlement_cursor=first_store.read_settlement_cursor(),
        settlement_receipt=receipt,
        guest_input=guest_input,
    )
    _require_fresh_commit(first)

    reopened = SQLiteZrpfAtomicSettlementStoreV1(
        database,
        genesis_settlement_state_root=genesis_root,
        busy_timeout_ms=busy_timeout_ms,
    )
    _require_store_non_authority(reopened)
    reopened_admission = reopened.read_admission_cursor()
    reopened_settlement = reopened.read_settlement_cursor()
    if reopened_admission != first.admission_head or reopened_settlement != first.settlement_head:
        raise DurableAdmissionEvidenceError(
            "reopen_cursor_mismatch",
            "reopened durable cursors differ from the committed result",
        )
    retry = adapter.verify_and_commit(
        store=reopened,
        expected_admission_cursor=reopened_admission,
        expected_settlement_cursor=reopened_settlement,
        settlement_receipt=receipt,
        guest_input=guest_input,
    )
    _require_exact_idempotent_retry(first, retry)

    final_store = SQLiteZrpfAtomicSettlementStoreV1(
        database,
        genesis_settlement_state_root=genesis_root,
        busy_timeout_ms=busy_timeout_ms,
    )
    _require_store_non_authority(final_store)
    final_admission = final_store.read_admission_cursor()
    final_settlement = final_store.read_settlement_cursor()
    if final_admission != first.admission_head or final_settlement != first.settlement_head:
        raise DurableAdmissionEvidenceError(
            "retry_mutated_state",
            "exact retry changed durable admission or settlement state",
        )

    database_size, database_sha256 = _stable_file_facts(
        database,
        maximum=MAX_DATABASE_BYTES,
        label="database",
    )
    report = _success_report(
        adapter=adapter,
        genesis_settlement_state_root=genesis_root,
        manifest_sha256=manifest_sha256,
        receipt=receipt,
        guest_input=guest_input,
        database_size=database_size,
        database_sha256=database_sha256,
        first=first,
        retry=retry,
        final_admission=final_admission,
        final_settlement=final_settlement,
        authority_blocked_reason=final_store.authority_blocked_reason,
    )
    raw = _canonical_report_bytes(report)
    _write_new_private_file(output, raw)
    return report, raw


def _success_report(
    *,
    adapter: Any,
    genesis_settlement_state_root: str,
    manifest_sha256: str,
    receipt: bytes,
    guest_input: bytes,
    database_size: int,
    database_sha256: str,
    first: Any,
    retry: Any,
    final_admission: Any,
    final_settlement: Any,
    authority_blocked_reason: str,
) -> dict[str, Any]:
    admission_receipt = first.admission_receipt
    settlement_receipt = first.settlement_receipt
    certificate_receipt = first.certificate_receipt
    if admission_receipt is None or settlement_receipt is None or certificate_receipt is None:
        raise DurableAdmissionEvidenceError(
            "missing_persisted_receipt",
            "committed result lacks one or more durable receipts",
        )
    if certificate_receipt.settlement_authority is not False:
        raise DurableAdmissionEvidenceError(
            "authority_nonclaim_violated",
            "certificate receipt unexpectedly grants settlement authority",
        )
    return {
        "authority_blocked_reason": authority_blocked_reason,
        "authority_manifest_sha256": manifest_sha256,
        "certificate_journal_hash": certificate_receipt.certificate_journal_hash,
        "database_bytes": database_size,
        "database_sha256": database_sha256,
        "exact_retry": _result_summary(retry),
        "first_commit": _result_summary(first),
        "genesis_to_result_state_bound": True,
        "genesis_settlement_state_root": genesis_settlement_state_root,
        "guest_input_sha256": hashlib.sha256(guest_input).hexdigest(),
        "normalized_plan_commitment": certificate_receipt.normalized_plan_commitment,
        "ok": True,
        "production_authority": False,
        "release_authority": False,
        "reopen_count": 2,
        "reopened_final_admission": _admission_cursor_summary(final_admission),
        "reopened_final_settlement": _settlement_cursor_summary(final_settlement),
        "request_sha256": admission_receipt.verification_request_sha256,
        "root_journal_hash": admission_receipt.root_journal_hash,
        "schema": REPORT_SCHEMA,
        "settlement_authority": False,
        "settlement_receipt_sha256": hashlib.sha256(receipt).hexdigest(),
        "verifier_executable_sha256": adapter.sha256,
    }


def _result_summary(result: Any) -> dict[str, Any]:
    return {
        "admission_revision": result.admission_head.revision,
        "committed": result.committed,
        "disposition": result.disposition.value,
        "idempotent_replay": result.idempotent_replay,
        "settlement_authority": False,
        "settlement_revision": result.settlement_head.revision,
    }


def _admission_cursor_summary(cursor: Any) -> dict[str, Any]:
    return {
        "child_claim_count": cursor.child_claim_count,
        "message_count": cursor.message_count,
        "receipt_count": cursor.receipt_count,
        "revision": cursor.revision,
        "root_count": cursor.root_count,
        "state_root": cursor.state_root,
    }


def _settlement_cursor_summary(cursor: Any) -> dict[str, Any]:
    return {
        "plan_count": cursor.plan_count,
        "revision": cursor.revision,
        "state_root": cursor.state_root,
    }


def _require_fresh_commit(result: Any) -> None:
    if (
        result.committed is not True
        or result.idempotent_replay is not False
        or result.settlement_authority is not False
    ):
        raise DurableAdmissionEvidenceError(
            "fresh_commit_required",
            "first admission did not commit a fresh authority-false transaction",
        )


def _require_exact_idempotent_retry(first: Any, retry: Any) -> None:
    if (
        retry.committed is not False
        or retry.idempotent_replay is not True
        or retry.settlement_authority is not False
    ):
        raise DurableAdmissionEvidenceError(
            "idempotent_retry_required",
            "exact retry was not an authority-false idempotent replay",
        )
    if (
        retry.admission_head != first.admission_head
        or retry.settlement_head != first.settlement_head
        or retry.admission_receipt != first.admission_receipt
        or retry.settlement_receipt != first.settlement_receipt
        or retry.certificate_receipt != first.certificate_receipt
    ):
        raise DurableAdmissionEvidenceError(
            "idempotent_retry_mismatch",
            "exact retry changed durable heads or persisted receipts",
        )


def _require_store_non_authority(store: Any) -> None:
    if store.settlement_authority is not False:
        raise DurableAdmissionEvidenceError(
            "authority_nonclaim_violated",
            "durable store unexpectedly grants settlement authority",
        )
    reason = store.authority_blocked_reason
    if type(reason) is not str or not reason:
        raise DurableAdmissionEvidenceError(
            "authority_reason_missing",
            "durable store authority-blocked reason is missing",
        )


def _canonical_report_bytes(report: dict[str, Any]) -> bytes:
    raw = canonical_json_bytes(report) + b"\n"
    if len(raw) > MAX_REPORT_BYTES:
        raise DurableAdmissionEvidenceError(
            "report_too_large",
            "durable admission report exceeds its byte bound",
        )
    return raw


def _read_bounded_regular_file(path: Path, *, maximum: int, label: str) -> bytes:
    resolved = _resolve_input_file(path, label)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(resolved, flags)
    except OSError as exc:
        raise DurableAdmissionEvidenceError(
            "input_open_failed",
            f"{label} could not be opened",
        ) from exc
    try:
        before = os.fstat(descriptor)
        _require_bounded_regular_stat(before, maximum=maximum, label=label)
        raw = _read_exact_descriptor(descriptor, before.st_size, label)
        after = os.fstat(descriptor)
        if _stable_identity(before) != _stable_identity(after):
            raise DurableAdmissionEvidenceError(
                "input_changed",
                f"{label} changed while it was read",
            )
        return raw
    finally:
        os.close(descriptor)


def _stable_file_facts(path: Path, *, maximum: int, label: str) -> tuple[int, str]:
    raw = _read_bounded_regular_file(path, maximum=maximum, label=label)
    return len(raw), hashlib.sha256(raw).hexdigest()


def _resolve_input_file(path: Path, label: str) -> Path:
    if not isinstance(path, Path):
        raise DurableAdmissionEvidenceError("invalid_path", f"{label} path must be pathlib.Path")
    try:
        metadata = path.lstat()
    except OSError as exc:
        raise DurableAdmissionEvidenceError("input_unavailable", f"{label} is unavailable") from exc
    if stat.S_ISLNK(metadata.st_mode):
        raise DurableAdmissionEvidenceError("symlink_rejected", f"{label} symlink is forbidden")
    if not stat.S_ISREG(metadata.st_mode):
        raise DurableAdmissionEvidenceError("regular_file_required", f"{label} must be regular")
    return path.resolve(strict=True)


def _resolve_executable(path: Path) -> Path:
    resolved = _resolve_input_file(path, "verifier executable")
    if not os.access(resolved, os.X_OK):
        raise DurableAdmissionEvidenceError(
            "executable_required",
            "verifier executable is not executable",
        )
    return resolved


def _resolve_fresh_path(path: Path, label: str) -> Path:
    if not isinstance(path, Path) or path.name in {"", ".", ".."}:
        raise DurableAdmissionEvidenceError("invalid_path", f"{label} path is invalid")
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as exc:
        raise DurableAdmissionEvidenceError(
            "parent_unavailable",
            f"{label} parent directory is unavailable",
        ) from exc
    resolved = parent / path.name
    if resolved.exists() or resolved.is_symlink():
        raise DurableAdmissionEvidenceError(
            "fresh_path_required",
            f"{label} must not already exist",
        )
    return resolved


def _require_distinct_paths(*paths: Path) -> None:
    resolved = [path.resolve(strict=False) for path in paths]
    if len(set(resolved)) != len(resolved):
        raise DurableAdmissionEvidenceError(
            "path_alias_rejected",
            "verifier, inputs, database, and output paths must be distinct",
        )


def _require_bounded_regular_stat(metadata: os.stat_result, *, maximum: int, label: str) -> None:
    if not stat.S_ISREG(metadata.st_mode) or not 0 < metadata.st_size <= maximum:
        raise DurableAdmissionEvidenceError(
            "input_size_rejected",
            f"{label} must be a nonempty bounded regular file",
        )


def _read_exact_descriptor(descriptor: int, expected: int, label: str) -> bytes:
    chunks: list[bytes] = []
    remaining = expected
    while remaining:
        chunk = os.read(descriptor, min(remaining, 1024 * 1024))
        if not chunk:
            raise DurableAdmissionEvidenceError("short_read", f"{label} ended early")
        chunks.append(chunk)
        remaining -= len(chunk)
    if os.read(descriptor, 1):
        raise DurableAdmissionEvidenceError("input_grew", f"{label} grew while it was read")
    return b"".join(chunks)


def _stable_identity(metadata: os.stat_result) -> tuple[int, int, int, int, int, int]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _write_new_private_file(path: Path, raw: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    descriptor: int | None = None
    try:
        descriptor = os.open(path, flags, 0o600)
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise OSError("short output write")
            view = view[written:]
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = None
        directory = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except OSError as exc:
        if descriptor is not None:
            os.close(descriptor)
        try:
            path.unlink(missing_ok=True)
        except OSError:
            pass
        raise DurableAdmissionEvidenceError(
            "output_write_failed",
            "durable admission output could not be committed",
        ) from exc


def _require_prefixed_hash(value: str, label: str) -> str:
    if type(value) is not str or _PREFIXED_HASH.fullmatch(value) is None:
        raise DurableAdmissionEvidenceError(
            "invalid_hash",
            f"{label} must be 0x-prefixed lowercase SHA-256 hex",
        )
    return value


def _require_bare_hash(value: str, label: str) -> str:
    if type(value) is not str or _BARE_HASH.fullmatch(value) is None:
        raise DurableAdmissionEvidenceError(
            "invalid_hash",
            f"{label} must be lowercase SHA-256 hex",
        )
    return value


def _failure_report(code: str) -> tuple[dict[str, Any], bytes]:
    report = {
        "error_code": code,
        "ok": False,
        "production_authority": False,
        "release_authority": False,
        "schema": ERROR_SCHEMA,
        "settlement_authority": False,
    }
    return report, _canonical_report_bytes(report)


def _error_code(error: Exception) -> str:
    if isinstance(error, DurableAdmissionEvidenceError):
        return error.code
    if isinstance(error, SourceOpenedSpotV6VerificationError):
        return "verifier_rejected"
    if isinstance(error, ZrpfAtomicSettlementStoreErrorV1):
        return "durable_store_rejected"
    if isinstance(error, OSError):
        return "filesystem_rejected"
    return "input_rejected"


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--authority-manifest", type=Path, required=True)
    parser.add_argument("--settlement-receipt", type=Path, required=True)
    parser.add_argument("--guest-input", type=Path, required=True)
    parser.add_argument("--database", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-authority-manifest-sha256", required=True)
    parser.add_argument("--genesis-settlement-state-root", required=True)
    parser.add_argument(
        "--busy-timeout-ms",
        type=int,
        default=DEFAULT_BUSY_TIMEOUT_MS,
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    arguments = _parser().parse_args(argv)
    try:
        _report, raw = run_durable_admission_evidence(
            verifier_path=arguments.verifier,
            authority_manifest_path=arguments.authority_manifest,
            settlement_receipt_path=arguments.settlement_receipt,
            guest_input_path=arguments.guest_input,
            database_path=arguments.database,
            output_path=arguments.output,
            expected_authority_manifest_sha256=(arguments.expected_authority_manifest_sha256),
            genesis_settlement_state_root=arguments.genesis_settlement_state_root,
            busy_timeout_ms=arguments.busy_timeout_ms,
        )
    except (
        DurableAdmissionEvidenceError,
        SourceOpenedSpotV6VerificationError,
        ZrpfAtomicSettlementStoreErrorV1,
        OSError,
        TypeError,
        ValueError,
    ) as exc:
        _report, raw = _failure_report(_error_code(exc))
        try:
            output = _resolve_fresh_path(arguments.output, "output")
            _write_new_private_file(output, raw)
        except DurableAdmissionEvidenceError:
            pass
        sys.stdout.buffer.write(raw)
        return 1
    sys.stdout.buffer.write(raw)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
