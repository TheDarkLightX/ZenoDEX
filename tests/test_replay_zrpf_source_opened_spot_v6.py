from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shutil
from pathlib import Path

import pytest

from tools import replay_zrpf_source_opened_spot_v6 as replay


def test_canonical_request_preserves_governed_field_order_without_newline() -> None:
    encoded = replay.canonical_request(
        (("schema", "v1"), ("receipt_hex", "00"), ("guest_input_hex", "11"))
    )

    assert encoded == b'{"schema":"v1","receipt_hex":"00","guest_input_hex":"11"}'


def test_mutation_reject_requires_exact_typed_error_transcript() -> None:
    expected = {
        "ok": False,
        "schema": replay.SETTLEMENT_ERROR_SCHEMA,
        "error_code": replay.MUTATION_ERROR_CODE,
    }
    canonical = (json.dumps(expected, separators=(",", ":")) + "\n").encode()

    replay._require_mutation_reject(replay._CompletedVerifier(1, b"", canonical))

    with pytest.raises(replay.ReplayError, match="transcript mismatch"):
        replay._require_mutation_reject(replay._CompletedVerifier(1, b"", canonical + b"\n"))


def test_success_requires_zero_exit_empty_stderr_and_exact_stdout() -> None:
    replay._require_success(
        replay._CompletedVerifier(0, b'{"ok":true}\n', b""),
        b'{"ok":true}\n',
        "test replay",
    )
    with pytest.raises(replay.ReplayError, match="emitted stderr"):
        replay._require_success(
            replay._CompletedVerifier(0, b'{"ok":true}\n', b"diagnostic"),
            b'{"ok":true}\n',
            "test replay",
        )


def test_sealed_verifier_ignores_path_replacement_after_snapshot(
    tmp_path: Path,
) -> None:
    verifier = tmp_path / "verifier"
    shutil.copyfile("/usr/bin/true", verifier)
    verifier.chmod(0o755)
    expected_sha256 = hashlib.sha256(verifier.read_bytes()).hexdigest()
    attacker = tmp_path / "attacker"
    shutil.copyfile("/usr/bin/false", attacker)
    attacker.chmod(0o755)

    with replay.sealed_executable.SealedExecutable(verifier) as executable:
        attacker.replace(verifier)
        completed = replay._run_verifier(executable, b"{}", ambient_dev=False)

        assert completed.returncode == 0
        assert completed.stdout == b""
        assert completed.stderr == b""
        assert executable.identity.sha256 == expected_sha256
        assert hashlib.sha256(verifier.read_bytes()).hexdigest() != expected_sha256


def test_sealed_verifier_ignores_same_inode_overwrite_and_restore(
    tmp_path: Path,
) -> None:
    verifier = tmp_path / "verifier"
    original = Path("/usr/bin/true").read_bytes()
    verifier.write_bytes(original)
    verifier.chmod(0o755)
    original_inode = verifier.stat().st_ino

    with replay.sealed_executable.SealedExecutable(verifier) as executable:
        verifier.write_bytes(Path("/usr/bin/false").read_bytes())
        assert verifier.stat().st_ino == original_inode
        completed = replay._run_verifier(executable, b"{}", ambient_dev=False)
        verifier.write_bytes(original)

        assert completed.returncode == 0
        assert completed.stdout == b""
        assert completed.stderr == b""
        assert executable.identity.sha256 == hashlib.sha256(original).hexdigest()
        assert hashlib.sha256(verifier.read_bytes()).hexdigest() == (executable.identity.sha256)
        assert (
            fcntl.fcntl(
                executable.pass_fds[0],
                fcntl.F_GET_SEALS,
            )
            == replay.sealed_executable.REQUIRED_SEALS
        )
        with pytest.raises(OSError):
            os.write(executable.pass_fds[0], b"attacker mutation")
