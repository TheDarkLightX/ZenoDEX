from __future__ import annotations

import base64
import copy
import hashlib
import json
import pickle
import socket
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest

from src.integration import _zeno_ledger_pinned_verifier_process_v1 as pinned_process
from src.integration.zeno_ledger_authenticated_proof_verification_v1 import (
    AUTHORITY_MANIFEST_SCHEMA_V1,
    RESPONSE_SCHEMA_V1,
    AuthenticatedProofVerificationRejectReason,
    PinnedZenoLedgerRisc0VerifierV1,
    ProofVerificationError,
    VerifierExecutableFormatV1,
    _AuthenticatedProofVerificationV1,
    zeno_ledger_risc0_authority_manifest_bytes_v1,
)
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    build_proof_metadata_v0,
    canonical_json_bytes_v0,
    hash_v0,
    proof_metadata_hash_v0,
)
from src.integration.zeno_ledger_verifier_registry_v0 import (
    VERIFIER_STATUS_ACTIVE_V0,
    VERIFIER_STATUS_REVOKED_V0,
    make_verifier_registry_entry_v0,
    make_verifier_registry_v0,
)


def _root(label: str) -> str:
    return hash_v0("test_root_v0", {"label": label})


def _proof_artifact_bytes(*, receipt: bytes = b"retained-risc0-receipt") -> bytes:
    return canonical_json_bytes_v0(
        {
            "schema": "tau_state_proof",
            "schema_version": 1,
            "state_hash": _root("state")[2:],
            "proof_type": "risc0.zenodex_spot_transition.v1",
            "proof": base64.b64encode(receipt).decode("ascii"),
            "meta": {"fixture": "metadata-v0-structural-only"},
        }
    )


def _metadata_and_header(proof_artifact_json: bytes) -> tuple[dict[str, Any], dict[str, Any]]:
    artifact = json.loads(proof_artifact_json)
    roots = {
        name: _root(name)
        for name in (
            "pre-state",
            "post-state",
            "tx",
            "evidence",
            "body",
            "schedule",
            "features",
            "dependency-lock",
            "toolchain-lock",
        )
    }
    metadata = build_proof_metadata_v0(
        chain_id="zeno-ledger-devnet-0",
        height=7,
        proof_kind="risc0_zkvm_v0",
        program_id="risc0:spot:" + _root("image-id")[2:],
        verifier_id="risc0:receipt-verifier:v1:spot",
        proof_commitment=hash_v0("risc0_tau_state_proof_envelope_v0", artifact),
        public_input_hash=_root("public-input"),
        journal_hash=_root("journal"),
        pre_state_root=roots["pre-state"],
        post_state_root=roots["post-state"],
        tx_root=roots["tx"],
        evidence_root=roots["evidence"],
        body_root=roots["body"],
        conflict_schedule_hash=roots["schedule"],
        feature_suite_hash=roots["features"],
        dependency_lock_hash=roots["dependency-lock"],
        toolchain_lock_hash=roots["toolchain-lock"],
    )
    header = build_header_v0(
        chain_id=str(metadata["chain_id"]),
        height=int(metadata["height"]),
        time_ms=1_778_730_000_000,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=_root("ingress"),
        tx_root=str(metadata["tx_root"]),
        pre_state_root=str(metadata["pre_state_root"]),
        post_state_root=str(metadata["post_state_root"]),
        app_hash=_root("app"),
        evidence_root=str(metadata["evidence_root"]),
        body_root=str(metadata["body_root"]),
        data_availability_root=_root("data-availability"),
        proof_journal_hash=proof_metadata_hash_v0(metadata),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT_V0,
    )
    return metadata, header


def _verifier_script(
    path: Path,
    *,
    counter_path: Path,
    response_mutation: tuple[str, object] | None = None,
    legacy_boolean_response: bool = False,
    noncanonical_journal: bool = False,
    persistent_child_socket: Path | None = None,
    persistent_child_sentinel: Path | None = None,
) -> Path:
    if (persistent_child_socket is None) != (persistent_child_sentinel is None):
        raise ValueError("persistent child socket and sentinel must be provided together")
    mutation_json = json.dumps(response_mutation)
    child_socket_path = (
        str(persistent_child_socket) if persistent_child_socket is not None else None
    )
    child_sentinel_path = (
        str(persistent_child_sentinel) if persistent_child_sentinel is not None else None
    )
    source = f"""#!/usr/bin/env python3
import base64
import json
import os
from pathlib import Path
import socket
import sys

counter = Path({str(counter_path)!r})
count = int(counter.read_text()) if counter.exists() else 0
counter.write_text(str(count + 1))
child_socket_path = {child_socket_path!r}
if child_socket_path is not None:
    ready_read, ready_write = os.pipe()
    child_pid = os.fork()
    if child_pid == 0:
        os.close(ready_read)
        server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        server.bind(child_socket_path)
        server.listen(1)
        os.write(ready_write, b"1")
        os.close(ready_write)
        connection, _ = server.accept()
        with connection:
            connection.recv(1)
            Path({child_sentinel_path!r}).write_text("leaked", encoding="utf-8")
            connection.sendall(b"1")
        os._exit(0)
    os.close(ready_write)
    if os.read(ready_read, 1) != b"1":
        raise RuntimeError("persistent verifier child did not start")
    os.close(ready_read)
request = json.load(sys.stdin)
if {legacy_boolean_response!r}:
    response = {{"ok": True, "risc0_verified": True}}
else:
    response = {{
        "schema": {RESPONSE_SCHEMA_V1!r},
        "accepted": True,
        "journal_b64": (
            "YWJ="
            if {noncanonical_journal!r}
            else base64.b64encode(b"verified-risc0-journal").decode("ascii")
        ),
        "verified_facts": request["expected_verified_facts"],
    }}
    mutation = json.loads({mutation_json!r})
    if mutation is not None:
        response["verified_facts"][mutation[0]] = mutation[1]
json.dump(response, sys.stdout, sort_keys=True, separators=(",", ":"))
"""
    path.write_text(source, encoding="utf-8")
    path.chmod(0o700)
    return path


def _make_verifier(
    tmp_path: Path,
    *,
    status: str = VERIFIER_STATUS_ACTIVE_V0,
    valid_from_height: int = 0,
    valid_until_height: int | None = None,
    response_mutation: tuple[str, object] | None = None,
    legacy_boolean_response: bool = False,
    noncanonical_journal: bool = False,
    persistent_child_socket: Path | None = None,
    persistent_child_sentinel: Path | None = None,
) -> tuple[
    PinnedZenoLedgerRisc0VerifierV1,
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    bytes,
    Path,
]:
    artifact = _proof_artifact_bytes()
    metadata, header = _metadata_and_header(artifact)
    entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
        status=status,
        valid_from_height=valid_from_height,
        valid_until_height=valid_until_height,
    )
    registry = make_verifier_registry_v0(entries=[entry])
    counter_path = tmp_path / "verifier-count.txt"
    executable = _verifier_script(
        tmp_path / "verifier.py",
        counter_path=counter_path,
        response_mutation=response_mutation,
        legacy_boolean_response=legacy_boolean_response,
        noncanonical_journal=noncanonical_journal,
        persistent_child_socket=persistent_child_socket,
        persistent_child_sentinel=persistent_child_sentinel,
    )
    executable_sha256 = hashlib.sha256(executable.read_bytes()).hexdigest()
    manifest = zeno_ledger_risc0_authority_manifest_bytes_v1(
        executable_sha256=executable_sha256,
        executable_format=VerifierExecutableFormatV1.TEST_SCRIPT,
        registry_id=str(registry["registry_id"]),
        registry_entry_id=str(entry["entry_id"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
        actual_image_id=_root("image-id"),
        receipt_kind="succinct",
        hash_function="sha-256",
        verifier_parameters_digest=_root("verifier-parameters"),
        control_id=_root("control-id"),
    )
    assert json.loads(manifest)["schema"] == AUTHORITY_MANIFEST_SCHEMA_V1
    verifier = PinnedZenoLedgerRisc0VerifierV1(
        executable=executable.resolve(),
        authority_manifest_json=manifest,
        authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
    )
    return verifier, metadata, header, registry, artifact, counter_path


def _verify(
    verifier: PinnedZenoLedgerRisc0VerifierV1,
    metadata: dict[str, Any],
    header: dict[str, Any],
    registry: dict[str, Any],
    artifact: bytes,
    *,
    checkpoint: dict[str, Any] | None = None,
):
    return verifier.verify_and_bind_header(
        proof_artifact_json=artifact,
        proof_metadata=metadata,
        header=header,
        checkpoint=checkpoint,
        verifier_registry=registry,
    )


def test_verification_executes_once_and_emits_non_promotable_observation(tmp_path: Path) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(tmp_path)

    observation = _verify(
        verifier,
        metadata,
        header,
        registry,
        artifact,
        checkpoint=build_checkpoint_v0(header),
    )

    assert counter.read_text(encoding="utf-8") == "1"
    assert observation.status == "authenticated_metadata_v0_risc0_verification"
    assert observation.production_promotable is False
    assert observation.proof_metadata_schema == "zenodex/zeno_ledger/proof_metadata/v0"
    assert observation.missing_production_bindings == (
        "authority_manifest_sha256",
        "canonical_journal_codec",
        "config_digest",
        "data_availability_root",
        "pre_exec_resource_limits",
        "receipt_security_profile",
        "sandboxed_verifier_execution",
        "verifier_registry_id",
    )
    assert observation.header_proof_journal_hash == header["proof_journal_hash"]
    assert observation.registry_id == registry["registry_id"]


def test_private_authenticated_capability_requires_module_seal() -> None:
    bogus: Any = object()
    with pytest.raises(TypeError, match="private seal"):
        _AuthenticatedProofVerificationV1(
            facts=bogus,
            binding=bogus,
            provenance=bogus,
            seal=object(),
        )

    unsealed = object.__new__(_AuthenticatedProofVerificationV1)
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(unsealed)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(unsealed)


def test_registry_validity_boundaries_are_inclusive(tmp_path: Path) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(
        tmp_path,
        valid_from_height=7,
        valid_until_height=7,
    )

    observation = _verify(verifier, metadata, header, registry, artifact)

    assert observation.height == 7
    assert counter.read_text(encoding="utf-8") == "1"


def test_executable_mutation_after_manifest_construction_rejects(tmp_path: Path) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(tmp_path)
    verifier.executable.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    verifier.executable.chmod(0o700)

    with pytest.raises(ProofVerificationError) as exc_info:
        _verify(verifier, metadata, header, registry, artifact)

    assert (
        exc_info.value.reason is AuthenticatedProofVerificationRejectReason.EXECUTABLE_HASH_MISMATCH
    )
    assert not counter.exists()


@pytest.mark.parametrize(
    ("status", "valid_from", "valid_until", "reason"),
    [
        (
            VERIFIER_STATUS_REVOKED_V0,
            0,
            None,
            AuthenticatedProofVerificationRejectReason.REGISTRY_ENTRY_REVOKED,
        ),
        (
            VERIFIER_STATUS_ACTIVE_V0,
            8,
            None,
            AuthenticatedProofVerificationRejectReason.REGISTRY_HEIGHT_INVALID,
        ),
        (
            VERIFIER_STATUS_ACTIVE_V0,
            0,
            6,
            AuthenticatedProofVerificationRejectReason.REGISTRY_HEIGHT_INVALID,
        ),
    ],
)
def test_registry_status_and_height_are_enforced(
    tmp_path: Path,
    status: str,
    valid_from: int,
    valid_until: int | None,
    reason: AuthenticatedProofVerificationRejectReason,
) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(
        tmp_path,
        status=status,
        valid_from_height=valid_from,
        valid_until_height=valid_until,
    )

    with pytest.raises(ProofVerificationError) as exc_info:
        _verify(verifier, metadata, header, registry, artifact)

    assert exc_info.value.reason is reason
    assert not counter.exists()


def test_registry_snapshot_substitution_is_rejected_before_execution(tmp_path: Path) -> None:
    verifier, metadata, header, _registry, artifact, counter = _make_verifier(tmp_path)
    replacement_entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
        valid_from_height=1,
    )
    replacement_registry = make_verifier_registry_v0(entries=[replacement_entry])

    with pytest.raises(ProofVerificationError) as exc_info:
        _verify(verifier, metadata, header, replacement_registry, artifact)

    assert (
        exc_info.value.reason
        is AuthenticatedProofVerificationRejectReason.REGISTRY_SNAPSHOT_MISMATCH
    )
    assert not counter.exists()


@pytest.mark.parametrize(
    "mutation",
    [
        "header_height",
        "checkpoint_header_hash",
        "proof_artifact",
    ],
)
def test_header_checkpoint_and_artifact_mutations_reject_before_execution(
    tmp_path: Path,
    mutation: str,
) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(tmp_path)
    checkpoint = build_checkpoint_v0(header)
    if mutation == "header_height":
        header = deepcopy(header)
        header["height"] = 8
    elif mutation == "checkpoint_header_hash":
        checkpoint = deepcopy(checkpoint)
        checkpoint["header_hash"] = _root("wrong-header")
    else:
        artifact = _proof_artifact_bytes(receipt=b"different-receipt")

    with pytest.raises((ProofVerificationError, ValueError)):
        _verify(
            verifier,
            metadata,
            header,
            registry,
            artifact,
            checkpoint=checkpoint,
        )

    assert not counter.exists()


@pytest.mark.parametrize(
    ("field", "replacement"),
    [
        ("actual_image_id", _root("wrong-image")),
        ("receipt_kind", "composite"),
        ("control_id", _root("wrong-control-id")),
        ("journal_hash", _root("wrong-journal")),
        ("chain_id", "wrong-chain"),
        ("post_state_root", _root("wrong-state")),
    ],
)
def test_verifier_fact_mutations_reject_after_one_execution(
    tmp_path: Path,
    field: str,
    replacement: object,
) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(
        tmp_path,
        response_mutation=(field, replacement),
    )

    with pytest.raises(ProofVerificationError) as exc_info:
        _verify(verifier, metadata, header, registry, artifact)

    assert (
        exc_info.value.reason
        is AuthenticatedProofVerificationRejectReason.VERIFIER_BINDING_MISMATCH
    )
    assert counter.read_text(encoding="utf-8") == "1"


def test_fabricated_legacy_boolean_response_cannot_mint_authority(tmp_path: Path) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(
        tmp_path,
        legacy_boolean_response=True,
    )

    with pytest.raises(ProofVerificationError) as exc_info:
        _verify(verifier, metadata, header, registry, artifact)

    assert (
        exc_info.value.reason
        is AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID
    )
    assert counter.read_text(encoding="utf-8") == "1"


def test_noncanonical_receipt_base64_rejects_before_execution(tmp_path: Path) -> None:
    artifact = canonical_json_bytes_v0(
        {
            "schema": "tau_state_proof",
            "schema_version": 1,
            "state_hash": _root("state")[2:],
            "proof_type": "risc0.zenodex_spot_transition.v1",
            "proof": "YWJ=",
            "meta": {"fixture": "noncanonical-base64"},
        }
    )
    verifier, _metadata, _header, registry, _original, counter = _make_verifier(tmp_path)
    metadata, header = _metadata_and_header(artifact)

    with pytest.raises(ProofVerificationError) as exc_info:
        _verify(verifier, metadata, header, registry, artifact)

    assert (
        exc_info.value.reason is AuthenticatedProofVerificationRejectReason.PROOF_ARTIFACT_INVALID
    )
    assert not counter.exists()


def test_noncanonical_journal_base64_rejects_after_one_execution(tmp_path: Path) -> None:
    verifier, metadata, header, registry, artifact, counter = _make_verifier(
        tmp_path,
        noncanonical_journal=True,
    )

    with pytest.raises(ProofVerificationError) as exc_info:
        _verify(verifier, metadata, header, registry, artifact)

    assert (
        exc_info.value.reason
        is AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID
    )
    assert counter.read_text(encoding="utf-8") == "1"


@pytest.mark.parametrize("legacy_boolean_response", [False, True])
def test_verifier_descendant_is_terminated_after_leader_exit(
    tmp_path: Path,
    legacy_boolean_response: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def allow_child_processes(
        _process_id: int,
        *,
        timeout_seconds: int,
        max_address_space_bytes: int,
        max_stack_bytes: int,
    ) -> None:
        del timeout_seconds, max_address_space_bytes, max_stack_bytes

    monkeypatch.setattr(pinned_process, "_apply_resource_limits", allow_child_processes)
    child_socket = tmp_path / "persistent-child.sock"
    child_sentinel = tmp_path / "persistent-child-sentinel.txt"
    verifier, metadata, header, registry, artifact, _counter = _make_verifier(
        tmp_path,
        legacy_boolean_response=legacy_boolean_response,
        persistent_child_socket=child_socket,
        persistent_child_sentinel=child_sentinel,
    )

    if legacy_boolean_response:
        with pytest.raises(ProofVerificationError):
            _verify(verifier, metadata, header, registry, artifact)
    else:
        _verify(verifier, metadata, header, registry, artifact)

    probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    try:
        with pytest.raises((ConnectionRefusedError, FileNotFoundError)):
            probe.connect(str(child_socket))
    finally:
        probe.close()
    assert not child_sentinel.exists()
