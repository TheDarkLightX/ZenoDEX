"""File-backed autonomous-governance session store admission tests."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import src.integration.autonomous_governance_session_store_file as session_store_file_module
from src.integration.autonomous_governance_session_store_file import (
    _lock_path,
    _write_store_file,
    admit_autonomous_governance_session_file_continuation_v1,
    current_session_store_file_head_v1,
    initialize_autonomous_governance_session_store_file_v1,
    verify_autonomous_governance_session_store_file_v1,
)
from tests.integration.test_autonomous_governance_session_store import (
    _continue,
    _genesis_pin,
    _genesis_receipt,
    _policy,
)


def _persisted_store(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(data, dict)
    return data


def _init_file(path: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    policy = _policy()
    genesis = _genesis_receipt(policy)
    pin = _genesis_pin(policy, genesis)
    init = initialize_autonomous_governance_session_store_file_v1(
        path=path,
        genesis_pin=pin,
        genesis_receipt=genesis,
        policy=policy,
    )
    assert init["ok"] is True, init["errors"]
    return policy, genesis, init


def test_session_store_file_initialize_verify_and_head(tmp_path: Path) -> None:
    path = tmp_path / "autogov-session-store.json"
    policy, genesis, init = _init_file(path)

    persisted = _persisted_store(path)
    assert persisted["store_hash"] == init["store_hash"]
    assert persisted["segment_count"] == 1

    verified = verify_autonomous_governance_session_store_file_v1(
        path=path,
        policy=policy,
    )
    assert verified["ok"] is True, verified["errors"]
    assert verified["authenticity_verified"] is True
    assert verified["scope"] == "receipts_replayed"
    assert verified["store_hash"] == init["store_hash"]

    head = current_session_store_file_head_v1(path=path)
    assert head["ok"] is True, head["errors"]
    assert head["surface_state"] == genesis["final_state"]
    assert head["store_hash"] == init["store_hash"]


def test_session_store_file_admission_uses_expected_hash_cas(tmp_path: Path) -> None:
    path = tmp_path / "autogov-session-store.json"
    policy, genesis, init = _init_file(path)
    base_hash = str(init["store_hash"])

    first = _continue(policy, genesis, 103)
    admitted = admit_autonomous_governance_session_file_continuation_v1(
        path=path,
        receipt=first,
        policy=policy,
        expected_store_hash=base_hash,
    )
    assert admitted["admitted"] is True, admitted["errors"]
    advanced_hash = str(admitted["store_hash"])
    assert advanced_hash != base_hash
    assert _persisted_store(path)["store_hash"] == advanced_hash

    second = _continue(policy, first, 106)
    stale = admit_autonomous_governance_session_file_continuation_v1(
        path=path,
        receipt=second,
        policy=policy,
        expected_store_hash=base_hash,
    )
    assert stale["admitted"] is False
    assert "session_store_file_expected_hash_mismatch" in stale["errors"]
    assert _persisted_store(path)["store_hash"] == advanced_hash


def test_session_store_file_refuses_forks_and_replays_unchanged(
    tmp_path: Path,
) -> None:
    path = tmp_path / "autogov-session-store.json"
    policy, genesis, init = _init_file(path)

    first = _continue(policy, genesis, 103)
    admitted = admit_autonomous_governance_session_file_continuation_v1(
        path=path,
        receipt=first,
        policy=policy,
        expected_store_hash=init["store_hash"],
    )
    assert admitted["admitted"] is True, admitted["errors"]
    advanced_hash = str(admitted["store_hash"])

    fork = _continue(policy, genesis, 120)
    fork_result = admit_autonomous_governance_session_file_continuation_v1(
        path=path,
        receipt=fork,
        policy=policy,
        expected_store_hash=advanced_hash,
    )
    assert fork_result["admitted"] is False
    assert "session_store_file_admission_refused" in fork_result["errors"]
    assert any("advance_chain_head_mismatch" in str(e) for e in fork_result["errors"])
    assert _persisted_store(path)["store_hash"] == advanced_hash

    replay = admit_autonomous_governance_session_file_continuation_v1(
        path=path,
        receipt=first,
        policy=policy,
        expected_store_hash=advanced_hash,
    )
    assert replay["admitted"] is False
    assert _persisted_store(path)["store_hash"] == advanced_hash


def test_session_store_file_malformed_json_fails_closed(tmp_path: Path) -> None:
    path = tmp_path / "autogov-session-store.json"
    policy = _policy()
    genesis = _genesis_receipt(policy)
    first = _continue(policy, genesis, 103)
    path.write_text("{not-json", encoding="utf-8")

    verified = verify_autonomous_governance_session_store_file_v1(
        path=path,
        policy=policy,
    )
    assert verified["ok"] is False
    assert "session_store_file_json_invalid" in verified["errors"]

    head = current_session_store_file_head_v1(path=path)
    assert head["ok"] is False
    assert "session_store_file_json_invalid" in head["errors"]

    admitted = admit_autonomous_governance_session_file_continuation_v1(
        path=path,
        receipt=first,
        policy=policy,
    )
    assert admitted["admitted"] is False
    assert "session_store_file_json_invalid" in admitted["errors"]
    assert path.read_text(encoding="utf-8") == "{not-json"


def test_session_store_file_existing_lock_refuses_write(tmp_path: Path) -> None:
    path = tmp_path / "autogov-session-store.json"
    policy, genesis, init = _init_file(path)
    lock = _lock_path(path)
    lock.write_text("held by another writer\n", encoding="utf-8")

    first = _continue(policy, genesis, 103)
    refused = admit_autonomous_governance_session_file_continuation_v1(
        path=path,
        receipt=first,
        policy=policy,
        expected_store_hash=init["store_hash"],
    )
    assert refused["admitted"] is False
    assert "session_store_file_lock_exists" in refused["errors"]
    assert _persisted_store(path)["store_hash"] == init["store_hash"]


def test_session_store_file_failed_write_cleans_temp_file(tmp_path: Path, monkeypatch) -> None:
    path = tmp_path / "autogov-session-store.json"
    temp_path = tmp_path / ".autogov-session-store.json.injected.tmp"

    class _FailingTempFile:
        name = str(temp_path)

        def __enter__(self) -> "_FailingTempFile":
            temp_path.write_bytes(b"partial")
            return self

        def __exit__(self, *_args: object) -> None:
            return None

        def write(self, _raw: bytes) -> int:
            raise OSError("simulated write failure")

        def flush(self) -> None:
            return None

        def fileno(self) -> int:
            return 0

    def _failing_named_temporary_file(*_args: object, **_kwargs: object) -> _FailingTempFile:
        return _FailingTempFile()

    monkeypatch.setattr(session_store_file_module.tempfile, "NamedTemporaryFile", _failing_named_temporary_file)

    ok, errors = _write_store_file(path, {"store_hash": "h"})

    assert ok is False
    assert errors == ("session_store_file_write_failed",)
    assert not temp_path.exists()
    assert not path.exists()


def test_cli_session_store_file_lifecycle(tmp_path: Path) -> None:
    policy = _policy()
    genesis = _genesis_receipt(policy)
    pin = _genesis_pin(policy, genesis)
    store_path = tmp_path / "cli-session-store.json"

    init_bundle = tmp_path / "init-session-store-file.json"
    init_bundle.write_text(
        json.dumps(
            {
                "path": str(store_path),
                "policy": policy,
                "genesis_pin": pin,
                "genesis_receipt": genesis,
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    initialized = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "init-session-store-file",
            str(init_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert initialized.returncode == 0, initialized.stderr
    init = json.loads(initialized.stdout)
    assert init["ok"] is True, init["errors"]

    first = _continue(policy, genesis, 103)
    admit_bundle = tmp_path / "admit-session-file-continuation.json"
    admit_bundle.write_text(
        json.dumps(
            {
                "path": str(store_path),
                "policy": policy,
                "trajectory_receipt": first,
                "expected_store_hash": init["store_hash"],
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    admitted = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "admit-session-file-continuation",
            str(admit_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert admitted.returncode == 0, admitted.stderr
    admission = json.loads(admitted.stdout)
    assert admission["admitted"] is True, admission["errors"]

    verify_bundle = tmp_path / "verify-session-store-file.json"
    verify_bundle.write_text(
        json.dumps({"path": str(store_path), "policy": policy}, sort_keys=True),
        encoding="utf-8",
    )
    verified = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "verify-session-store-file",
            str(verify_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert verified.returncode == 0, verified.stderr
    verification = json.loads(verified.stdout)
    assert verification["ok"] is True, verification["errors"]
    assert verification["authenticity_verified"] is True

    headed = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "session-store-file-head",
            str(verify_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert headed.returncode == 0, headed.stderr
    head = json.loads(headed.stdout)
    assert head["ok"] is True, head["errors"]
    assert head["surface_state"] == first["final_state"]
