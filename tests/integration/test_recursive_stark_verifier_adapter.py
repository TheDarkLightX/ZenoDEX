from __future__ import annotations

import hashlib
import json
import subprocess
import types
from pathlib import Path

import pytest

import src.integration.recursive_stark_verifier_adapter as verifier_adapter
from src.core.recursive_stark_admission import (
    RecursiveStarkAdmissionRejectReason,
    RecursiveStarkAdmissionState,
    RecursiveStarkRootFacts,
    recursive_child_verification_claims_root_v1,
    recursive_message_ids_root_v1,
    recursive_receipt_ids_root_v1,
)
from src.integration.recursive_stark_admission_store import (
    SQLiteRecursiveStarkAdmissionStore,
)
from src.integration.recursive_stark_release_binding import (
    RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1,
    recursive_stark_release_binding_config_digest_v1,
)
from src.integration.recursive_stark_verifier_adapter import (
    RECEIPT_CODEC_V1,
    PinnedRecursiveStarkVerifier,
    RecursiveStarkVerificationError,
    RecursiveVerifierExecutableFormat,
    parse_recursive_stark_root_facts,
    recursive_stark_authority_manifest_bytes_v1,
)


def _hash(index: int) -> str:
    return f"0x{index:064x}"


def test_pinned_recursive_verifier_cannot_be_subclassed() -> None:
    with pytest.raises(TypeError, match="cannot be subclassed"):
        types.new_class("BypassVerifier", (PinnedRecursiveStarkVerifier,))


def test_recursive_adapter_uses_pre_exec_process_contract() -> None:
    source = Path(verifier_adapter.__file__).read_text(encoding="utf-8")

    assert "execute_pinned_verifier_once" in source
    assert "resource.prlimit" not in source
    assert "subprocess.Popen" not in source


def _facts_payload() -> dict[str, object]:
    child_claims = (_hash(4), _hash(5))
    receipt_ids = (_hash(6), _hash(7))
    message_ids = (_hash(8), _hash(9))
    return {
        "schema": "zenodex.verified_recursive_stark_root_facts.v1",
        "aggregate_image_id": "11" * 32,
        "receipt_codec": RECEIPT_CODEC_V1,
        "receipt_kind": "succinct",
        "receipt_hashfn": "poseidon2",
        "receipt_verifier_parameters": "12" * 32,
        "receipt_control_id": "13" * 32,
        "chain_id": "zenodex-devnet",
        "epoch_id": 7,
        "proof_profile": "recursive_epoch_v1",
        "root_journal_hash": _hash(1),
        "verifier_set_root": _hash(2),
        "public_policy_hash": _hash(3),
        "child_verification_claim_hashes": list(child_claims),
        "child_verification_claims_root": recursive_child_verification_claims_root_v1(child_claims),
        "accepted_receipt_ids": list(receipt_ids),
        "accepted_receipts_root": recursive_receipt_ids_root_v1(receipt_ids),
        "cross_shard_message_ids": list(message_ids),
        "cross_shard_message_ids_root": recursive_message_ids_root_v1(message_ids),
    }


def _response() -> dict[str, object]:
    return {"ok": True, "verified_recursive_facts": _facts_payload()}


def _expectations() -> dict[str, object]:
    facts = _facts_payload()
    return {
        "risc0_image_id": facts["aggregate_image_id"],
        "receipt_codec": facts["receipt_codec"],
        "receipt_kind": facts["receipt_kind"],
        "receipt_hashfn": facts["receipt_hashfn"],
        "receipt_verifier_parameters": facts["receipt_verifier_parameters"],
        "receipt_control_id": facts["receipt_control_id"],
        "chain_id": facts["chain_id"],
        "epoch_id": facts["epoch_id"],
        "proof_profile": facts["proof_profile"],
        "verifier_set_root": str(facts["verifier_set_root"])[2:],
        "public_policy_hash": str(facts["public_policy_hash"])[2:],
        "child_verification_claims_root": str(facts["child_verification_claims_root"])[2:],
        "accepted_receipts_root": str(facts["accepted_receipts_root"])[2:],
        "cross_shard_message_ids_root": str(facts["cross_shard_message_ids_root"])[2:],
        "post_state_root": "22" * 32,
    }


def _adapter(executable: Path, executable_hash: str) -> PinnedRecursiveStarkVerifier:
    authority_manifest = recursive_stark_authority_manifest_bytes_v1(
        executable_sha256=executable_hash,
        trusted_expectations=_expectations(),
        executable_format=RecursiveVerifierExecutableFormat.TEST_SCRIPT,
    )
    return PinnedRecursiveStarkVerifier(
        executable=executable,
        authority_manifest_json=authority_manifest,
        authority_manifest_sha256=hashlib.sha256(authority_manifest).hexdigest(),
    )


def _release_binding(
    *,
    authority_manifest_sha256: str,
    chain_id: str = "zenodex-devnet",
) -> bytes:
    return json.dumps(
        {
            "schema": RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1,
            "chain_id": chain_id,
            "epoch_id": 7,
            "proof_profile": "recursive_epoch_v1",
            "authority_manifest_sha256": authority_manifest_sha256,
            "replay_manifest_sha256": "sha256:" + "44" * 32,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("ascii")


def _write_pinned_verifier(
    path: Path,
    response: dict[str, object],
    *,
    require_sanitized_environment: bool = False,
    require_pre_exec_contract: bool = False,
) -> str:
    environment_check = ""
    if require_sanitized_environment:
        environment_check = (
            "import os\n"
            "assert 'LD_PRELOAD' not in os.environ\n"
            "assert 'LD_LIBRARY_PATH' not in os.environ\n"
            "assert os.environ == {\n"
            "    'LANG': 'C', 'LC_ALL': 'C', 'PATH': '/usr/bin:/bin',\n"
            "    'RISC0_DEV_MODE': '0', 'TZ': 'UTC'\n"
            "}\n"
        )
    pre_exec_check = ""
    if require_pre_exec_contract:
        pre_exec_check = (
            "import errno, resource, socket\n"
            "status = open('/proc/self/status', encoding='ascii').read()\n"
            "assert 'NoNewPrivs:\\t1' in status\n"
            f"assert resource.getrlimit(resource.RLIMIT_AS) == ({2 * 1024 * 1024 * 1024},) * 2\n"
            f"assert resource.getrlimit(resource.RLIMIT_STACK) == ({32 * 1024 * 1024},) * 2\n"
            "assert resource.getrlimit(resource.RLIMIT_CPU) == (61, 61)\n"
            f"assert resource.getrlimit(resource.RLIMIT_FSIZE) == ({16 * 1024 * 1024},) * 2\n"
            "assert resource.getrlimit(resource.RLIMIT_NOFILE) == (32, 32)\n"
            "assert resource.getrlimit(resource.RLIMIT_NPROC) == (1, 1)\n"
            "for family in (socket.AF_INET, socket.AF_UNIX):\n"
            "    try:\n"
            "        socket.socket(family, socket.SOCK_STREAM)\n"
            "    except OSError as exc:\n"
            "        assert exc.errno == errno.EPERM\n"
            "    else:\n"
            "        raise AssertionError('socket creation unexpectedly succeeded')\n"
        )
    script = (
        "#!/usr/bin/env python3\n"
        "import json, sys\n"
        f"{environment_check}"
        f"{pre_exec_check}"
        "json.load(sys.stdin)\n"
        f"print({json.dumps(json.dumps(response, sort_keys=True))})\n"
    )
    path.write_text(script, encoding="ascii")
    path.chmod(0o700)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_static_pinned_verifier(path: Path, response: dict[str, object]) -> str:
    response_text = json.dumps(response, sort_keys=True, separators=(",", ":")) + "\n"
    source = path.with_suffix(".c")
    source.write_text(
        "#include <stdio.h>\n"
        "int main(void) {\n"
        "  char buffer[4096];\n"
        "  while (fread(buffer, 1, sizeof(buffer), stdin) != 0) {}\n"
        f"  fputs({json.dumps(response_text)}, stdout);\n"
        "  return ferror(stdin) || ferror(stdout);\n"
        "}\n",
        encoding="ascii",
    )
    subprocess.run(
        ["/usr/bin/gcc", "-static", "-O2", "-s", "-o", str(path), str(source)],
        check=True,
        capture_output=True,
    )
    path.chmod(0o700)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_shape_parser_accepts_only_root_bound_facts_matching_trusted_expectations() -> None:
    facts = parse_recursive_stark_root_facts(
        _response(),
        trusted_expectations=_expectations(),
    )

    assert isinstance(facts, RecursiveStarkRootFacts)
    assert facts.chain_id == "zenodex-devnet"
    assert facts.child_verification_claims_root == (
        recursive_child_verification_claims_root_v1(facts.child_verification_claim_hashes)
    )


def test_parser_rejects_projected_boolean_report() -> None:
    with pytest.raises(RecursiveStarkVerificationError, match="response schema mismatch"):
        parse_recursive_stark_root_facts(
            {"ok": True, "risc0_verified": True},
            trusted_expectations=_expectations(),
        )


def test_shape_parser_rejects_attacker_matching_facts_against_ledger_policy() -> None:
    attacker_response = _response()
    attacker_response["verified_recursive_facts"]["verifier_set_root"] = _hash(30)  # type: ignore[index]

    with pytest.raises(RecursiveStarkVerificationError, match="trusted expectation mismatch"):
        parse_recursive_stark_root_facts(
            attacker_response,
            trusted_expectations=_expectations(),
        )


def test_pinned_adapter_admits_once_and_rejects_replay(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    adapter = _adapter(executable, executable_hash)

    first = adapter.verify_and_admit(
        state=RecursiveStarkAdmissionState(),
        proof={"proof_type": "risc0.zenodex_recursive_epoch.v1"},
        recursive_input={"disclosure": "fixture"},
    )
    assert first.accepted is True

    replay = adapter.verify_and_admit(
        state=first.state,
        proof={"proof_type": "risc0.zenodex_recursive_epoch.v1"},
        recursive_input={"disclosure": "fixture"},
    )
    assert replay.accepted is False
    assert replay.reject_reason is RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL
    assert replay.state is first.state


def test_pinned_adapter_rejects_binary_hash_drift(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    executable.write_text("#!/bin/sh\nexit 0\n", encoding="ascii")
    executable.chmod(0o700)
    adapter = _adapter(executable, executable_hash)

    with pytest.raises(RecursiveStarkVerificationError, match="binary hash mismatch"):
        adapter.verify_and_admit(
            state=RecursiveStarkAdmissionState(),
            proof={},
            recursive_input={},
        )


def test_pinned_adapter_executes_sealed_snapshot_with_sanitized_environment(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(
        executable,
        _response(),
        require_sanitized_environment=True,
    )
    monkeypatch.setenv("LD_PRELOAD", "/tmp/attacker.so")
    monkeypatch.setenv("LD_LIBRARY_PATH", "/tmp/attacker")
    adapter = _adapter(executable, executable_hash)

    result = adapter.verify_and_admit(
        state=RecursiveStarkAdmissionState(),
        proof={"proof_type": "risc0.zenodex_recursive_epoch.v1"},
        recursive_input={"disclosure": "fixture"},
    )

    assert result.accepted is True


def test_pinned_adapter_observes_pre_exec_security_contract(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(
        executable,
        _response(),
        require_pre_exec_contract=True,
    )
    adapter = _adapter(executable, executable_hash)

    result = adapter.verify_and_admit(
        state=RecursiveStarkAdmissionState(),
        proof={"proof_type": "risc0.zenodex_recursive_epoch.v1"},
        recursive_input={"disclosure": "fixture"},
    )

    assert result.accepted is True


def test_pinned_adapter_rejects_symlinked_executable(tmp_path: Path) -> None:
    target = tmp_path / "recursive-verifier-real"
    executable_hash = _write_pinned_verifier(target, _response())
    executable = tmp_path / "recursive-verifier"
    executable.symlink_to(target)
    adapter = _adapter(executable, executable_hash)

    with pytest.raises(RecursiveStarkVerificationError, match="process failed"):
        adapter.verify_and_admit(
            state=RecursiveStarkAdmissionState(),
            proof={},
            recursive_input={},
        )


def test_pinned_adapter_requires_static_elf_by_default(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    authority_manifest = recursive_stark_authority_manifest_bytes_v1(
        executable_sha256=executable_hash,
        trusted_expectations=_expectations(),
    )
    adapter = PinnedRecursiveStarkVerifier(
        executable=executable,
        authority_manifest_json=authority_manifest,
        authority_manifest_sha256=hashlib.sha256(authority_manifest).hexdigest(),
    )

    with pytest.raises(RecursiveStarkVerificationError, match="must be a static ELF"):
        adapter.verify_and_admit(
            state=RecursiveStarkAdmissionState(),
            proof={},
            recursive_input={},
        )


def test_pinned_adapter_rejects_authority_manifest_digest_mismatch(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    authority_manifest = recursive_stark_authority_manifest_bytes_v1(
        executable_sha256=executable_hash,
        trusted_expectations=_expectations(),
        executable_format=RecursiveVerifierExecutableFormat.TEST_SCRIPT,
    )

    with pytest.raises(ValueError, match="authority manifest hash mismatch"):
        PinnedRecursiveStarkVerifier(
            executable=executable,
            authority_manifest_json=authority_manifest,
            authority_manifest_sha256="00" * 32,
        )


def test_governed_release_constructor_binds_manifest_and_scope(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    authority_manifest = recursive_stark_authority_manifest_bytes_v1(
        executable_sha256=executable_hash,
        trusted_expectations=_expectations(),
        executable_format=RecursiveVerifierExecutableFormat.TEST_SCRIPT,
    )
    authority_sha256 = hashlib.sha256(authority_manifest).hexdigest()
    release_binding = _release_binding(authority_manifest_sha256=authority_sha256)
    config_digest = recursive_stark_release_binding_config_digest_v1(release_binding)

    verifier = PinnedRecursiveStarkVerifier.from_governed_release_binding(
        executable=executable,
        authority_manifest_json=authority_manifest,
        authority_manifest_sha256=authority_sha256,
        release_binding_json=release_binding,
        expected_release_binding_config_digest=config_digest,
    )

    assert verifier._release_binding_config_digest == config_digest
    assert verifier._replay_manifest_sha256 == "sha256:" + "44" * 32


def test_governed_release_constructor_rejects_authority_manifest_substitution(
    tmp_path: Path,
) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    authority_manifest = recursive_stark_authority_manifest_bytes_v1(
        executable_sha256=executable_hash,
        trusted_expectations=_expectations(),
        executable_format=RecursiveVerifierExecutableFormat.TEST_SCRIPT,
    )
    authority_sha256 = hashlib.sha256(authority_manifest).hexdigest()
    release_binding = _release_binding(authority_manifest_sha256="99" * 32)

    with pytest.raises(ValueError, match="release authority manifest mismatch"):
        PinnedRecursiveStarkVerifier.from_governed_release_binding(
            executable=executable,
            authority_manifest_json=authority_manifest,
            authority_manifest_sha256=authority_sha256,
            release_binding_json=release_binding,
            expected_release_binding_config_digest=(
                recursive_stark_release_binding_config_digest_v1(release_binding)
            ),
        )


def test_governed_static_verifier_commits_through_the_only_durable_entry_path(
    tmp_path: Path,
) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_static_pinned_verifier(executable, _response())
    authority_manifest = recursive_stark_authority_manifest_bytes_v1(
        executable_sha256=executable_hash,
        trusted_expectations=_expectations(),
    )
    authority_sha256 = hashlib.sha256(authority_manifest).hexdigest()
    release_binding = _release_binding(authority_manifest_sha256=authority_sha256)
    verifier = PinnedRecursiveStarkVerifier.from_governed_release_binding(
        executable=executable,
        authority_manifest_json=authority_manifest,
        authority_manifest_sha256=authority_sha256,
        release_binding_json=release_binding,
        expected_release_binding_config_digest=(
            recursive_stark_release_binding_config_digest_v1(release_binding)
        ),
    )
    private = tmp_path / "private"
    private.mkdir(mode=0o700)
    store = SQLiteRecursiveStarkAdmissionStore(private / "store.sqlite3")

    result = verifier.verify_and_commit(
        store=store,
        expected_cursor=store.read_cursor(),
        proof={"proof_type": "risc0.zenodex_recursive_epoch.v1"},
        recursive_input={"disclosure": "fixture"},
    )

    assert result.committed is True
    assert result.receipt is not None
    assert result.receipt.authority_manifest_sha256 == authority_sha256
    assert result.receipt.verifier_executable_sha256 == executable_hash


def test_durable_commit_rejects_unbound_or_test_script_verifier_before_execution(
    tmp_path: Path,
) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    verifier = _adapter(executable, executable_hash)
    private = tmp_path / "private"
    private.mkdir(mode=0o700)
    store = SQLiteRecursiveStarkAdmissionStore(private / "store.sqlite3")

    with pytest.raises(RecursiveStarkVerificationError, match="requires a static ELF"):
        verifier.verify_and_commit(
            store=store,
            expected_cursor=store.read_cursor(),
            proof={},
            recursive_input={},
        )

    object.__setattr__(
        verifier,
        "executable_format",
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64,
    )
    with pytest.raises(RecursiveStarkVerificationError, match="governed release binding"):
        verifier.verify_and_commit(
            store=store,
            expected_cursor=store.read_cursor(),
            proof={},
            recursive_input={},
        )


def test_pinned_adapter_rejects_noncanonical_authority_manifest(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    authority_manifest = (
        recursive_stark_authority_manifest_bytes_v1(
            executable_sha256=executable_hash,
            trusted_expectations=_expectations(),
            executable_format=RecursiveVerifierExecutableFormat.TEST_SCRIPT,
        )
        + b"\n"
    )

    with pytest.raises(ValueError, match="authority manifest must be canonical JSON"):
        PinnedRecursiveStarkVerifier(
            executable=executable,
            authority_manifest_json=authority_manifest,
            authority_manifest_sha256=hashlib.sha256(authority_manifest).hexdigest(),
        )


def test_pinned_adapter_rejects_oversized_request_before_process_launch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    adapter = _adapter(executable, executable_hash)
    monkeypatch.setattr(verifier_adapter, "MAX_VERIFIER_REQUEST_BYTES", 128)

    with pytest.raises(RecursiveStarkVerificationError, match="exceeds 128 byte limit"):
        adapter.verify_and_admit(
            state=RecursiveStarkAdmissionState(),
            proof={"proof": "x" * 256},
            recursive_input={},
        )


def test_pinned_adapter_snapshots_authority_expectations(tmp_path: Path) -> None:
    executable = tmp_path / "recursive-verifier"
    executable_hash = _write_pinned_verifier(executable, _response())
    expectations = _expectations()
    authority_manifest = recursive_stark_authority_manifest_bytes_v1(
        executable_sha256=executable_hash,
        trusted_expectations=expectations,
        executable_format=RecursiveVerifierExecutableFormat.TEST_SCRIPT,
    )
    adapter = PinnedRecursiveStarkVerifier(
        executable=executable,
        authority_manifest_json=authority_manifest,
        authority_manifest_sha256=hashlib.sha256(authority_manifest).hexdigest(),
    )
    expectations["chain_id"] = "attacker-chain"
    adapter.trusted_expectations["chain_id"] = "attacker-chain"  # type: ignore[index]

    result = adapter.verify_and_admit(
        state=RecursiveStarkAdmissionState(),
        proof={"proof_type": "risc0.zenodex_recursive_epoch.v1"},
        recursive_input={"disclosure": "fixture"},
    )

    assert result.accepted is True


def test_pinned_adapter_stops_reading_at_stdout_limit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    executable = tmp_path / "recursive-verifier"
    executable.write_text(
        "#!/usr/bin/env python3\n"
        "import sys\n"
        "sys.stdin.read()\n"
        "while True:\n"
        "    sys.stdout.write('x' * 4096)\n"
        "    sys.stdout.flush()\n",
        encoding="ascii",
    )
    executable.chmod(0o700)
    executable_hash = hashlib.sha256(executable.read_bytes()).hexdigest()
    adapter = _adapter(executable, executable_hash)
    monkeypatch.setattr(verifier_adapter, "MAX_VERIFIER_STDOUT_BYTES", 8192)

    with pytest.raises(RecursiveStarkVerificationError, match="stdout exceeds limit"):
        adapter.verify_and_admit(
            state=RecursiveStarkAdmissionState(),
            proof={},
            recursive_input={},
        )
