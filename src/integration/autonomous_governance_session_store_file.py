"""File-backed repository for the autonomous-governance session store.

`autonomous_governance_session_store.py` owns the one-live-head admission
contract. This module gives deployments a small durable wrapper around that
contract:

- store state is persisted as a single JSON file;
- writes use an exclusive sidecar lock and atomic replace;
- admission can require the caller's `expected_store_hash`, so stale writers
  are refused before they can advance an old head.

The file wrapper is local deployment state. It is a practical ordering boundary
for one process group using this API, and every stored blob is still replayable
through the underlying receipt audit. A deployment that needs global ordering or
data availability must put this file repository behind that stronger layer.
"""

from __future__ import annotations

import json
import os
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator, Mapping

from src.integration.autonomous_governance_session_store import (
    admit_autonomous_governance_session_continuation_v1,
    current_session_store_head_v1,
    initialize_autonomous_governance_session_store_v1,
    verify_autonomous_governance_session_store_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0

AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_INIT_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store_file_init.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_ADMISSION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store_file_admission.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_VERIFICATION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store_file_verification.v1"
)
AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_HEAD_SCHEMA_V1 = (
    "zenodex.autonomous_governance.session_store_file_head.v1"
)

_FILE_INIT_HASH_TAG = "autonomous_governance_session_store_file_init_v1"
_FILE_ADMISSION_HASH_TAG = "autonomous_governance_session_store_file_admission_v1"
_FILE_VERIFICATION_HASH_TAG = "autonomous_governance_session_store_file_verification_v1"
_FILE_HEAD_HASH_TAG = "autonomous_governance_session_store_file_head_v1"

MAX_SESSION_STORE_FILE_BYTES_V1 = 64 * 1024 * 1024
_LOCK_BYTES_V1 = b"zenodex_autonomous_governance_session_store_file_lock_v1\n"


def _as_path(path: str | os.PathLike[str]) -> Path:
    if not isinstance(path, (str, os.PathLike)):
        raise TypeError("session_store_file_path_must_be_pathlike")
    return Path(path)


def _lock_path(path: Path) -> Path:
    return path.with_name(path.name + ".lock")


@contextmanager
def _exclusive_store_file_lock(path: Path) -> Iterator[tuple[bool, tuple[str, ...]]]:
    lock_path = _lock_path(path)
    try:
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        fd = os.open(str(lock_path), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        yield False, ("session_store_file_lock_exists",)
        return
    except OSError:
        yield False, ("session_store_file_lock_unavailable",)
        return

    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(_LOCK_BYTES_V1)
        yield True, ()
    finally:
        try:
            lock_path.unlink()
        except FileNotFoundError:
            pass
        except OSError:
            pass


def _read_store_file(path: Path) -> tuple[dict[str, Any], tuple[str, ...]]:
    try:
        stat = path.stat()
    except FileNotFoundError:
        return {}, ("session_store_file_missing",)
    except OSError:
        return {}, ("session_store_file_stat_failed",)
    if not path.is_file():
        return {}, ("session_store_file_not_regular",)
    if stat.st_size > MAX_SESSION_STORE_FILE_BYTES_V1:
        return {}, ("session_store_file_too_large",)

    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return {}, ("session_store_file_utf8_invalid",)
    except OSError:
        return {}, ("session_store_file_read_failed",)

    try:
        data = json.loads(text)
    except json.JSONDecodeError:
        return {}, ("session_store_file_json_invalid",)
    if not isinstance(data, Mapping):
        return {}, ("session_store_file_json_must_be_object",)
    return dict(data), ()


def _write_store_file(path: Path, store: Mapping[str, Any]) -> tuple[bool, tuple[str, ...]]:
    try:
        text = json.dumps(dict(store), indent=2, sort_keys=True) + "\n"
        raw = text.encode("utf-8")
    except (TypeError, UnicodeEncodeError, ValueError):
        return False, ("session_store_file_json_encode_failed",)
    if len(raw) > MAX_SESSION_STORE_FILE_BYTES_V1:
        return False, ("session_store_file_store_too_large",)

    temp_name: str | None = None
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            "wb",
            dir=str(path.parent),
            prefix=f".{path.name}.",
            suffix=".tmp",
            delete=False,
        ) as handle:
            temp_name = handle.name
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_name, path)
    except OSError:
        if temp_name is not None:
            try:
                os.unlink(temp_name)
            except FileNotFoundError:
                pass
            except OSError:
                pass
        return False, ("session_store_file_write_failed",)
    return True, ()


def _store_hash(store: Mapping[str, Any] | None) -> str:
    if not isinstance(store, Mapping):
        return ""
    value = store.get("store_hash")
    return value if isinstance(value, str) else ""


def initialize_autonomous_governance_session_store_file_v1(
    *,
    path: str | os.PathLike[str],
    genesis_pin: object,
    genesis_receipt: object,
    policy: object,
    create_only: bool = True,
) -> dict[str, Any]:
    """Initialize and durably write a session store JSON file."""

    store_path = _as_path(path)
    errors: list[str] = []
    init: dict[str, Any] = {}
    created = False
    store: dict[str, Any] = {}

    if type(create_only) is not bool:
        errors.append("session_store_file_create_only_invalid")

    with _exclusive_store_file_lock(store_path) as (locked, lock_errors):
        errors.extend(lock_errors)
        if locked and not errors:
            if create_only and store_path.exists():
                errors.append("session_store_file_exists")
            else:
                init = initialize_autonomous_governance_session_store_v1(
                    genesis_pin=genesis_pin,
                    genesis_receipt=genesis_receipt,
                    policy=policy,
                )
                if init.get("ok") is not True:
                    errors.append("session_store_file_init_refused")
                    errors.extend(str(error) for error in init.get("errors", ()))
                else:
                    candidate = dict(init.get("store", {}))
                    wrote, write_errors = _write_store_file(store_path, candidate)
                    errors.extend(write_errors)
                    if wrote:
                        created = True
                        store = candidate

    ok = not errors and created
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_INIT_SCHEMA_V1,
        "ok": ok,
        "created": created,
        "store_path": str(store_path),
        "store_hash": _store_hash(store),
        "store": store if ok else {},
        "init": init,
        "errors": tuple(errors),
    }
    return {**body, "file_init_hash": hash_v0(_FILE_INIT_HASH_TAG, body)}


def admit_autonomous_governance_session_file_continuation_v1(
    *,
    path: str | os.PathLike[str],
    receipt: object,
    policy: object,
    expected_store_hash: object = None,
) -> dict[str, Any]:
    """Advance the store file only from the caller's expected current head."""

    store_path = _as_path(path)
    errors: list[str] = []
    current_store: dict[str, Any] = {}
    admission: dict[str, Any] = {}
    admitted = False
    base_store_hash = ""
    new_store: dict[str, Any] = {}

    if expected_store_hash is not None and type(expected_store_hash) is not str:
        errors.append("session_store_file_expected_hash_invalid")

    with _exclusive_store_file_lock(store_path) as (locked, lock_errors):
        errors.extend(lock_errors)
        if locked and not errors:
            current_store, read_errors = _read_store_file(store_path)
            errors.extend(read_errors)
            base_store_hash = _store_hash(current_store)
            if (
                not errors
                and expected_store_hash is not None
                and str(expected_store_hash) != base_store_hash
            ):
                errors.append("session_store_file_expected_hash_mismatch")
            if not errors:
                admission = admit_autonomous_governance_session_continuation_v1(
                    store=current_store,
                    receipt=receipt,
                    policy=policy,
                )
                if admission.get("admitted") is not True:
                    errors.append("session_store_file_admission_refused")
                    errors.extend(str(error) for error in admission.get("errors", ()))
                else:
                    reread_store, reread_errors = _read_store_file(store_path)
                    if reread_errors:
                        errors.append("session_store_file_cas_read_failed")
                        errors.extend(reread_errors)
                    elif _store_hash(reread_store) != base_store_hash:
                        errors.append("session_store_file_cas_hash_mismatch")
                    else:
                        candidate = dict(admission.get("store", {}))
                        wrote, write_errors = _write_store_file(store_path, candidate)
                        errors.extend(write_errors)
                        if wrote:
                            admitted = True
                            new_store = candidate

    ok = not errors and admitted
    result_store = new_store if ok else current_store
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_ADMISSION_SCHEMA_V1,
        "ok": ok,
        "admitted": admitted,
        "store_path": str(store_path),
        "expected_store_hash": expected_store_hash if expected_store_hash is not None else "",
        "previous_store_hash": base_store_hash,
        "store_hash": _store_hash(result_store),
        "head_pin_hash": str(admission.get("head_pin_hash", "")) if ok else "",
        "admission": admission,
        "store": result_store if isinstance(result_store, Mapping) else {},
        "errors": tuple(errors),
    }
    return {**body, "file_admission_hash": hash_v0(_FILE_ADMISSION_HASH_TAG, body)}


def verify_autonomous_governance_session_store_file_v1(
    *,
    path: str | os.PathLike[str],
    policy: object,
) -> dict[str, Any]:
    """Replay-audit the store state currently persisted at `path`."""

    store_path = _as_path(path)
    errors: list[str] = []
    store, read_errors = _read_store_file(store_path)
    errors.extend(read_errors)

    verification: dict[str, Any] = {}
    if not errors:
        verification = verify_autonomous_governance_session_store_v1(
            store=store,
            policy=policy,
        )
        if verification.get("ok") is not True:
            errors.append("session_store_file_verification_refused")
            errors.extend(str(error) for error in verification.get("errors", ()))

    ok = not errors
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_VERIFICATION_SCHEMA_V1,
        "ok": ok,
        "authenticity_verified": bool(
            ok and verification.get("authenticity_verified") is True
        ),
        "scope": str(verification.get("scope", "")),
        "store_path": str(store_path),
        "store_hash": _store_hash(store),
        "segment_count": int(verification.get("segment_count", 0))
        if verification
        else 0,
        "head_pin_hash": str(verification.get("head_pin_hash", "")),
        "verification": verification,
        "errors": tuple(errors),
    }
    return {
        **body,
        "file_verification_hash": hash_v0(_FILE_VERIFICATION_HASH_TAG, body),
    }


def current_session_store_file_head_v1(
    *,
    path: str | os.PathLike[str],
) -> dict[str, Any]:
    """Read the persisted store head and committed governance surface state."""

    store_path = _as_path(path)
    errors: list[str] = []
    store, read_errors = _read_store_file(store_path)
    errors.extend(read_errors)

    head: dict[str, Any] = {}
    if not errors:
        head = current_session_store_head_v1(store)
        if head.get("ok") is not True:
            errors.append("session_store_file_head_refused")
            errors.extend(str(error) for error in head.get("errors", ()))

    ok = not errors
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SESSION_STORE_FILE_HEAD_SCHEMA_V1,
        "ok": ok,
        "store_path": str(store_path),
        "store_hash": _store_hash(store),
        "head_pin": dict(head.get("head_pin", {})) if ok else {},
        "surface_state": dict(head.get("surface_state", {})) if ok else {},
        "segment_count": int(head.get("segment_count", 0)) if ok else 0,
        "errors": tuple(errors),
    }
    return {**body, "file_head_hash": hash_v0(_FILE_HEAD_HASH_TAG, body)}
