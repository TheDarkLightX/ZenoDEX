"""BDD and adversarial evidence for the non-authoritative Spot V7 atomic store."""

from __future__ import annotations

import copy
import hashlib
import inspect
import pickle
import sqlite3
import struct
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from threading import Barrier
from unittest.mock import patch

import pytest

import src.integration._zrpf_spot_v7_firecracker_authority as firecracker_authority_module
import src.integration.zrpf_spot_v7_atomic_settlement_store as store_module
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _seal_test_only_spot_v7_settlement_v1,
    _SpotV7SettlementCandidateInputV1,
    _TestOnlySealedSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    SPOT_V7_FIRECRACKER_AUTHORITY_MISSING_CONDITIONS_V1,
    SpotV7FirecrackerAuthorityMissingConditionV1,
    SpotV7FirecrackerAuthorityUnavailableV1,
    _bind_governed_firecracker_spot_v7_settlement_v1,
    _GovernedFirecrackerSpotV7SettlementV1,
    _GovernedJailedFirecrackerExecutionV1,
    _require_governed_firecracker_spot_v7_authority_available_v1,
)
from src.integration._zrpf_spot_v7_firecracker_output import (
    SPOT_V7_COMMITTED_OUTPUT_UNBOUND_CANDIDATE_FIELDS_V1,
    SpotV7CommittedOutputRejectV1,
    _bind_decoded_spot_v7_output_to_candidate_v1,
    _BoundCommittedSpotV7CandidateV1,
    _decode_exact_committed_spot_v7_output_v1,
    _decode_spot_v7_payload_v1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_store import (
    SQLiteSpotV7AtomicSettlementStoreV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SpotV7AssetEffectV1,
    SpotV7AtomicSettlementDispositionV1,
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7AtomicSettlementStoreIdentityV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    spot_v7_cell_transitions_root_v1,
)
from tools import zrpf_v3_firecracker_output_protocol as firecracker_protocol


def _hash(seed: int) -> str:
    return f"0x{seed:064x}"


def _subject(byte: int, length: int) -> str:
    return "0x" + (bytes([byte]) * length).hex()


_SENDER = _subject(0x11, 48)
_POOL = _subject(0x22, 32)
_INPUT_ASSET = _hash(0x33)
_OUTPUT_ASSET = _hash(0x44)
_RECIPIENT = _subject(0x55, 48)


def _opening(
    kind: SpotV7CellKindV1,
    subject_id: str,
    asset_id: str,
    atoms: int,
) -> SpotV7CellOpeningV1:
    return SpotV7CellOpeningV1(
        kind=kind,
        subject_id=subject_id,
        asset_id=asset_id,
        atoms=atoms,
    )


def _transitions(
    values: tuple[int, int, int, int],
    *,
    input_atoms: int,
    output_atoms: int,
) -> tuple[SpotV7CellTransitionV1, ...]:
    sender_input, pool_input, pool_output, recipient_output = values
    rows = (
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.DEBIT,
            pre=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _SENDER,
                _INPUT_ASSET,
                sender_input,
            ),
            post=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _SENDER,
                _INPUT_ASSET,
                sender_input - input_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.CREDIT,
            pre=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _INPUT_ASSET,
                pool_input,
            ),
            post=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _INPUT_ASSET,
                pool_input + input_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.DEBIT,
            pre=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _OUTPUT_ASSET,
                pool_output,
            ),
            post=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _OUTPUT_ASSET,
                pool_output - output_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.CREDIT,
            pre=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _RECIPIENT,
                _OUTPUT_ASSET,
                recipient_output,
            ),
            post=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _RECIPIENT,
                _OUTPUT_ASSET,
                recipient_output + output_atoms,
            ),
        ),
    )
    return tuple(sorted(rows, key=lambda row: row.cell_key))


def _identity() -> SpotV7AtomicSettlementStoreIdentityV1:
    return SpotV7AtomicSettlementStoreIdentityV1(
        application_id=_hash(1),
        chain_or_domain_id=_hash(2),
        verified_program_id=_hash(3),
        verified_profile_id=_hash(4),
        verified_program_manifest_root=_hash(5),
        genesis_state_root=_hash(6),
    )


def _initial_cells() -> tuple[SpotV7CellOpeningV1, ...]:
    return tuple(
        sorted(
            (
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_000),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 25),
            ),
            key=lambda row: row.cell_key,
        )
    )


def _candidate(
    seed: int = 100,
    *,
    pre_state_root: str | None = None,
    post_state_root: str | None = None,
    values: tuple[int, int, int, int] = (1_000, 5_000, 8_000, 25),
    input_atoms: int = 100,
    output_atoms: int = 60,
    action_id: str | None = None,
    authorization_nullifier: str | None = None,
    grant_spend_nullifier: str | None = None,
) -> _TestOnlySealedSpotV7SettlementV1:
    identity = _identity()
    action = action_id or _hash(seed + 1)
    transitions = _transitions(values, input_atoms=input_atoms, output_atoms=output_atoms)
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, _INPUT_ASSET, input_atoms),
                SpotV7AssetEffectV1(action, _OUTPUT_ASSET, output_atoms),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    proposal = _SpotV7SettlementCandidateInputV1(
        application_id=identity.application_id,
        chain_or_domain_id=identity.chain_or_domain_id,
        epoch_id=seed,
        verified_program_id=identity.verified_program_id,
        verified_profile_id=identity.verified_profile_id,
        verified_program_manifest_root=identity.verified_program_manifest_root,
        source_child_claim_binding=_hash(seed + 2),
        source_child_journal_sha256=_hash(seed + 3),
        data_availability_certificate_root=_hash(seed + 4),
        data_root=_hash(seed + 5),
        settlement_effect_plan_commitment=_hash(seed + 6),
        pre_state_root=pre_state_root or identity.genesis_state_root,
        post_state_root=post_state_root or _hash(seed + 7),
        economic_action_id=action,
        authorization_nullifier=authorization_nullifier or _hash(seed + 8),
        authorization_grant_spend_nullifier=grant_spend_nullifier or _hash(seed + 9),
        consumed_object_ids=(_hash(seed + 10), _hash(seed + 11)),
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
        asset_effects=effects,
        exact_v7_receipt_bytes=f"receipt-{seed}".encode(),
        exact_v7_journal_bytes=f"journal-{seed}".encode(),
        exact_plan_b_bytes=f"plan-b-{seed}".encode(),
        exact_firecracker_execution_record_bytes=f"execution-{seed}".encode(),
        exact_firecracker_output_bytes=f"output-{seed}".encode(),
    )
    return _seal_test_only_spot_v7_settlement_v1(proposal)


def _bound_committed_output(
    *,
    seed: int = 100,
) -> tuple[
    _BoundCommittedSpotV7CandidateV1,
    bytes,
    bytes,
]:
    sealed_candidate = _candidate(seed=seed)
    candidate = sealed_candidate._input
    plan = candidate.exact_plan_b_bytes
    semantic = bytes([0x61]) * 310
    source_child_program = _hash_bytes(_hash(seed + 101))
    source_child_profile = _hash_bytes(_hash(seed + 102))
    state_root_host_input_sha256 = _hash_bytes(_hash(seed + 103))
    binding_fields = (
        _hash_bytes(_hash(seed + 104)),
        _hash_bytes(_hash(seed + 105)),
        _hash_bytes(_hash(seed + 106)),
        _hash_bytes(_hash(seed + 107)),
        _hash_bytes(candidate.settlement_effect_plan_commitment),
        _hash_bytes(candidate.cell_transitions_root),
        _hash_bytes(candidate.pre_state_root),
        _hash_bytes(candidate.post_state_root),
        _hash_bytes(candidate.economic_action_id),
        _hash_bytes(_hash(seed + 108)),
        _hash_bytes(_hash(seed + 109)),
        _hash_bytes(_hash(seed + 110)),
    )
    binding = b"\x00\x01" + b"".join(binding_fields)
    binding_domain = b"zenodex.zrpf.spot_settlement_v7_effect_binding_journal.v1"
    binding_commitment = hashlib.sha256(
        len(binding_domain).to_bytes(2, "big") + binding_domain + binding
    ).digest()
    journal_fields = (
        source_child_program,
        source_child_profile,
        _hash_bytes(candidate.source_child_claim_binding),
        _hash_bytes(candidate.source_child_journal_sha256),
        _hash_bytes(candidate.data_availability_certificate_root),
        _hash_bytes(candidate.data_root),
        _hash_bytes(_hash(seed + 111)),
        state_root_host_input_sha256,
        hashlib.sha256(semantic).digest(),
        binding_commitment,
        _hash_bytes(candidate.settlement_effect_plan_commitment),
        hashlib.sha256(plan).digest(),
        _hash_bytes(sealed_candidate.action_ids_root),
    )
    host_input_length = 1_024
    journal_total = 26 + 13 * 32 + len(semantic) + len(binding) + len(plan)
    journal = b"".join(
        (
            b"ZSPTV7J1",
            (1).to_bytes(2, "big"),
            journal_total.to_bytes(4, "big"),
            host_input_length.to_bytes(4, "big"),
            len(semantic).to_bytes(2, "big"),
            len(binding).to_bytes(2, "big"),
            len(plan).to_bytes(4, "big"),
            *journal_fields,
            semantic,
            binding,
            plan,
        )
    )
    output_fields = (
        _hash_bytes(candidate.verified_program_id),
        _hash_bytes(candidate.verified_profile_id),
        _hash_bytes(candidate.verified_program_manifest_root),
        hashlib.sha256(journal).digest(),
        source_child_program,
        source_child_profile,
        _hash_bytes(candidate.source_child_claim_binding),
        _hash_bytes(candidate.source_child_journal_sha256),
        _hash_bytes(candidate.data_availability_certificate_root),
        _hash_bytes(candidate.data_root),
        _hash_bytes(candidate.settlement_effect_plan_commitment),
        hashlib.sha256(plan).digest(),
        _hash_bytes(candidate.pre_state_root),
        _hash_bytes(candidate.post_state_root),
        _hash_bytes(sealed_candidate.action_ids_root),
        _hash_bytes(sealed_candidate.action_authorization_bindings_root),
        _hash_bytes(sealed_candidate.authorization_grant_spends_root),
        _hash_bytes(sealed_candidate.consumed_object_ids_root),
        state_root_host_input_sha256,
    )
    payload_total = 26 + 19 * 32 + len(journal)
    payload = b"".join(
        (
            b"ZSPTV7O1",
            (1).to_bytes(2, "big"),
            payload_total.to_bytes(4, "big"),
            len(journal).to_bytes(4, "big"),
            len(plan).to_bytes(4, "big"),
            host_input_length.to_bytes(4, "big"),
            *output_fields,
            journal,
        )
    )
    candidate = replace(
        candidate,
        exact_v7_journal_bytes=journal,
        exact_firecracker_output_bytes=payload,
    )
    request = firecracker_protocol.FirecrackerRequestV1.validated(
        run_nonce_256=bytes([0x31]) * 32,
        runtime_manifest_sha256=bytes([0x32]) * 32,
        input_drive_sha256=bytes([0x33]) * 32,
        replay_intent_sha256=bytes([0x34]) * 32,
    )
    output_device = firecracker_protocol.build_committed_output(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=payload,
    )
    decoded = _decode_exact_committed_spot_v7_output_v1(
        request_bytes=request.encode(),
        output_device_bytes=output_device,
    )
    return (
        _bind_decoded_spot_v7_output_to_candidate_v1(
            decoded_output=decoded,
            candidate=candidate,
        ),
        request.encode(),
        output_device,
    )


def _mutate_nested_v7_plan_and_recommit(
    request_bytes: bytes,
    output_device: bytes,
) -> bytes:
    """Change Plan B while repairing every outer data-only commitment."""

    payload_length = struct.unpack_from("<I", output_device, 16)[0]
    payload = bytearray(output_device[256 : 256 + payload_length])
    output_header_bytes = 26 + 19 * 32
    journal_offset = output_header_bytes
    semantic_length = int.from_bytes(payload[journal_offset + 18 : journal_offset + 20], "big")
    binding_length = int.from_bytes(payload[journal_offset + 20 : journal_offset + 22], "big")
    plan_length = int.from_bytes(payload[journal_offset + 22 : journal_offset + 26], "big")
    plan_offset = journal_offset + 26 + 13 * 32 + semantic_length + binding_length
    assert plan_length > 0
    assert plan_offset + plan_length == len(payload)
    payload[plan_offset] ^= 1
    payload[26 + 3 * 32 : 26 + 4 * 32] = hashlib.sha256(payload[journal_offset:]).digest()
    request = firecracker_protocol.decode_request(request_bytes)
    return firecracker_protocol.build_committed_output(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=bytes(payload),
    )


def _encode_prior_width_v7_output_and_recommit(
    request_bytes: bytes,
    output_device: bytes,
) -> bytes:
    """Recreate the superseded 18/12-field frame for rejection evidence."""

    payload_length = struct.unpack_from("<I", output_device, 16)[0]
    payload = output_device[256 : 256 + payload_length]
    new_output_header_bytes = 26 + 19 * 32
    journal = payload[new_output_header_bytes:]
    new_journal_header_bytes = 26 + 13 * 32
    old_journal = bytearray(
        journal[: 26 + 11 * 32]
        + journal[26 + 12 * 32 : new_journal_header_bytes]
        + journal[new_journal_header_bytes:]
    )
    old_journal[10:14] = len(old_journal).to_bytes(4, "big")
    old_output_fixed = bytearray(
        payload[26 : 26 + 11 * 32] + payload[26 + 12 * 32 : new_output_header_bytes]
    )
    old_output_fixed[3 * 32 : 4 * 32] = hashlib.sha256(old_journal).digest()
    old_payload = bytearray(payload[:26] + old_output_fixed + old_journal)
    old_payload[10:14] = len(old_payload).to_bytes(4, "big")
    old_payload[14:18] = len(old_journal).to_bytes(4, "big")
    request = firecracker_protocol.decode_request(request_bytes)
    return firecracker_protocol.build_committed_output(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=bytes(old_payload),
    )


def _hash_bytes(value: str) -> bytes:
    return bytes.fromhex(value[2:])


def _store(tmp_path: Path) -> SQLiteSpotV7AtomicSettlementStoreV1:
    directory = tmp_path / "private"
    directory.mkdir(mode=0o700)
    return SQLiteSpotV7AtomicSettlementStoreV1(
        directory / "spot-v7.sqlite3",
        identity=_identity(),
        genesis_cells=_initial_cells(),
    )


def _reopen(store: SQLiteSpotV7AtomicSettlementStoreV1) -> SQLiteSpotV7AtomicSettlementStoreV1:
    return SQLiteSpotV7AtomicSettlementStoreV1(
        store.path,
        identity=_identity(),
        genesis_cells=_initial_cells(),
    )


def _database_rows(path: Path) -> tuple[tuple[str, tuple[tuple[object, ...], ...]], ...]:
    with sqlite3.connect(path) as connection:
        tables = [
            str(row[0])
            for row in connection.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%' "
                "ORDER BY name"
            )
        ]
        result = []
        for table in tables:
            columns = [str(row[1]) for row in connection.execute(f"PRAGMA table_info({table})")]
            order = ", ".join(columns)
            rows = tuple(connection.execute(f"SELECT * FROM {table} ORDER BY {order}").fetchall())
            result.append((table, rows))
        return tuple(result)


def test_given_raw_verifier_output_when_committing_then_no_authority_entrypoint_exists(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)

    assert not hasattr(store, "commit")
    assert not hasattr(store, "commit_verifier_output")
    assert not hasattr(store, "commit_firecracker_execution")
    assert store.governed_firecracker_binder_available is False
    with pytest.raises(TypeError, match="test-only sealed Spot V7 candidate"):
        store._commit_test_only_sealed_candidate(
            expected_cursor=store.read_cursor(),
            candidate=b"raw SpotSettlementV7VerifierOutputV1 bytes",
        )
    assert store.read_cursor().revision == 0


def test_governed_firecracker_authority_reports_the_exact_fail_closed_frontier() -> None:
    assert SPOT_V7_FIRECRACKER_AUTHORITY_MISSING_CONDITIONS_V1 == (
        SpotV7FirecrackerAuthorityMissingConditionV1.FINAL_V6_CHILD_IMAGE_ID,
        SpotV7FirecrackerAuthorityMissingConditionV1.FINAL_V7_IMAGE_ID,
        SpotV7FirecrackerAuthorityMissingConditionV1.CURRENT_V7_RECEIPT_EVIDENCE,
        SpotV7FirecrackerAuthorityMissingConditionV1.GOVERNED_RELEASE_BINDING,
        SpotV7FirecrackerAuthorityMissingConditionV1.ROOT_OWNED_IMMUTABLE_STAGING,
        SpotV7FirecrackerAuthorityMissingConditionV1.EXACT_RUNTIME_ARTIFACT_SET,
        SpotV7FirecrackerAuthorityMissingConditionV1.EXACT_REQUEST_OUTPUT_BINDING,
        SpotV7FirecrackerAuthorityMissingConditionV1.LIVE_PRIVILEGED_JAILER,
        SpotV7FirecrackerAuthorityMissingConditionV1.LIVE_CGROUP_LIFECYCLE,
        SpotV7FirecrackerAuthorityMissingConditionV1.LIVE_EXCLUSIVE_NETWORK_NAMESPACE,
        SpotV7FirecrackerAuthorityMissingConditionV1.EXACT_EXECUTION_RECORD_BINDING,
        SpotV7FirecrackerAuthorityMissingConditionV1.EXACT_V7_PAYLOAD_BINDING,
        SpotV7FirecrackerAuthorityMissingConditionV1.AUTHORITY_CAPABLE_STORE_SCHEMA,
    )

    with pytest.raises(SpotV7FirecrackerAuthorityUnavailableV1) as captured:
        _require_governed_firecracker_spot_v7_authority_available_v1()

    assert captured.value.code == "SPOT_V7_FIRECRACKER_AUTHORITY_UNAVAILABLE"
    assert captured.value.missing_conditions == (
        SPOT_V7_FIRECRACKER_AUTHORITY_MISSING_CONDITIONS_V1
    )
    assert tuple(item.value for item in captured.value.missing_conditions) == (
        "final_v6_child_image_id_unmaterialized",
        "final_v7_image_id_unmaterialized",
        "current_v7_receipt_and_seal_mutation_evidence_missing",
        "governed_v7_release_manifest_and_revocation_binding_missing",
        "root_owned_immutable_artifact_staging_missing",
        "exact_runtime_artifact_set_validation_missing",
        "exact_request_output_device_binding_missing",
        "live_privileged_jailer_execution_missing",
        "live_cgroup_limits_membership_and_teardown_evidence_missing",
        "live_exclusive_network_namespace_evidence_missing",
        "canonical_execution_record_and_provenance_binding_missing",
        "exact_firecracker_output_and_v7_payload_binding_missing",
        "authority_capable_atomic_store_schema_missing",
    )


def test_unavailable_binder_source_contains_no_production_mint_path() -> None:
    source = inspect.getsource(_bind_governed_firecracker_spot_v7_settlement_v1)

    assert "_require_governed_firecracker_spot_v7_authority_available_v1()" in source
    assert "_GovernedFirecrackerSpotV7SettlementV1(" not in source
    assert "_GOVERNED_BINDER_SEAL_V1" not in source
    assert tuple(inspect.signature(_bind_governed_firecracker_spot_v7_settlement_v1).parameters) == (
        "runtime_execution",
    )


@pytest.mark.parametrize(
    "untrusted_runtime_value",
    (
        b"raw Firecracker output",
        {"firecracker_execution_verified": True},
        {"docker_replay_verified": True},
        True,
        object(),
    ),
)
def test_raw_output_reports_and_booleans_cannot_mint_governed_capability(
    untrusted_runtime_value: object,
) -> None:
    with pytest.raises(TypeError, match="governed jailed Firecracker execution"):
        _bind_governed_firecracker_spot_v7_settlement_v1(
            runtime_execution=untrusted_runtime_value,
        )


def test_committed_output_decoder_matches_outer_protocol_and_exact_v7_payload() -> None:
    bound, request_bytes, output_device = _bound_committed_output()

    decoded = _decode_exact_committed_spot_v7_output_v1(
        request_bytes=request_bytes,
        output_device_bytes=output_device,
    )

    assert decoded == bound.decoded_output
    assert decoded.output_payload_bytes == bound.candidate.exact_firecracker_output_bytes
    assert decoded.journal_bytes == bound.candidate.exact_v7_journal_bytes
    assert decoded.plan_b_bytes == bound.candidate.exact_plan_b_bytes
    assert decoded.output_device_sha256 == hashlib.sha256(output_device).digest()
    assert SPOT_V7_COMMITTED_OUTPUT_UNBOUND_CANDIDATE_FIELDS_V1 == (
        "application_id",
        "chain_or_domain_id",
        "epoch_id",
        "exact_v7_receipt_bytes",
        "exact_firecracker_execution_record_bytes",
    )


def test_python_v7_payload_decoder_accepts_the_rust_golden_vector() -> None:
    vector_path = (
        Path(__file__).resolve().parents[2]
        / "zk/spot_settlement_v7_risc0/verifier/tests/vectors/"
        / "spot_settlement_v7_firecracker_output_v1.hex"
    )
    payload = bytes.fromhex(
        "".join(
            line.split("//", maxsplit=1)[0].strip()
            for line in vector_path.read_text(encoding="utf-8").splitlines()
        )
    )

    fixed, journal, plan, journal_fixed, binding_fixed, host_input_length = (
        _decode_spot_v7_payload_v1(payload)
    )

    assert len(payload) == 3_372
    assert hashlib.sha256(payload).hexdigest() == (
        "979b2e9cb4757de50ec935c55ca827c693ad5cb4e22ee8034bee9e7866de148c"
    )
    assert len(fixed) == 19
    assert len(journal) == 2_738
    assert len(plan) == 1_600
    assert len(journal_fixed) == 13
    assert len(binding_fixed) == 12
    assert host_input_length == 1_024


def test_committed_output_decoder_rejects_recommitted_nested_plan_b_mutation() -> None:
    _, request_bytes, output_device = _bound_committed_output()
    mutated_output = _mutate_nested_v7_plan_and_recommit(request_bytes, output_device)

    with pytest.raises(SpotV7CommittedOutputRejectV1) as captured:
        _decode_exact_committed_spot_v7_output_v1(
            request_bytes=request_bytes,
            output_device_bytes=mutated_output,
        )

    assert captured.value.code == "v7_plan_bytes_sha256"


def test_committed_output_decoder_rejects_prior_width_v1_frame() -> None:
    _, request_bytes, output_device = _bound_committed_output()
    prior_width_output = _encode_prior_width_v7_output_and_recommit(
        request_bytes,
        output_device,
    )

    with pytest.raises(SpotV7CommittedOutputRejectV1) as captured:
        _decode_exact_committed_spot_v7_output_v1(
            request_bytes=request_bytes,
            output_device_bytes=prior_width_output,
        )

    assert captured.value.code == "v7_output_framing"


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        ("request_nonce", "output_binding"),
        ("payload", "output_payload"),
        ("trailing", "output_trailing_bytes"),
        ("commit", "output_commit"),
    ),
)
def test_committed_output_decoder_rejects_outer_binding_mutations(
    mutation: str,
    code: str,
) -> None:
    _, request_bytes, output_device = _bound_committed_output()
    request = bytearray(request_bytes)
    output = bytearray(output_device)
    if mutation == "request_nonce":
        request[16] ^= 1
    elif mutation == "payload":
        output[256] ^= 1
    elif mutation == "trailing":
        payload_length = struct.unpack_from("<I", output, 16)[0]
        output[256 + payload_length] = 1
    else:
        output[-1] ^= 1

    with pytest.raises(SpotV7CommittedOutputRejectV1) as captured:
        _decode_exact_committed_spot_v7_output_v1(
            request_bytes=bytes(request),
            output_device_bytes=bytes(output),
        )

    assert captured.value.code == code


def test_governed_runtime_owns_the_exact_candidate_and_rejects_a_b_rebinding() -> None:
    bound_a, _, _ = _bound_committed_output(seed=100)
    bound_b, _, _ = _bound_committed_output(seed=200)
    runtime = _GovernedJailedFirecrackerExecutionV1(
        bound_a,
        seal=firecracker_authority_module._GOVERNED_RUNTIME_SEAL_V1,
    )
    capability = _GovernedFirecrackerSpotV7SettlementV1(
        runtime_execution=runtime,
        seal=firecracker_authority_module._GOVERNED_BINDER_SEAL_V1,
    )

    assert capability._candidate_for_atomic_store() is bound_a.candidate
    assert capability._candidate_for_atomic_store() is not bound_b.candidate
    with pytest.raises(TypeError, match="unexpected keyword argument 'candidate_input'"):
        _bind_governed_firecracker_spot_v7_settlement_v1(
            runtime_execution=runtime,
            **{"candidate_input": bound_b.candidate},
        )

    with pytest.raises(SpotV7CommittedOutputRejectV1) as captured:
        _bind_decoded_spot_v7_output_to_candidate_v1(
            decoded_output=bound_a.decoded_output,
            candidate=bound_b.candidate,
        )
    assert captured.value.code == "candidate_output_binding"


@pytest.mark.parametrize("mutation", ["action", "asset", "amount"])
def test_committed_output_binding_rejects_asset_effect_semantic_mutation(
    mutation: str,
) -> None:
    bound, _, _ = _bound_committed_output()
    candidate = bound.candidate
    first, second = candidate.asset_effects
    mutated_first = SpotV7AssetEffectV1(
        _hash(91) if mutation == "action" else first.economic_action_id,
        _hash(92) if mutation == "asset" else first.asset_id,
        first.amount_atoms + 1 if mutation == "amount" else first.amount_atoms,
    )
    mutated = replace(candidate, asset_effects=(mutated_first, second))

    with pytest.raises(SpotV7CommittedOutputRejectV1) as captured:
        _bind_decoded_spot_v7_output_to_candidate_v1(
            decoded_output=bound.decoded_output,
            candidate=mutated,
        )

    assert captured.value.code == "candidate_output_binding"


def test_direct_or_object_new_capability_construction_cannot_cross_private_seals() -> None:
    bound, _, _ = _bound_committed_output()

    with pytest.raises(TypeError, match="governed runtime seal"):
        _GovernedJailedFirecrackerExecutionV1(
            bound,
            seal=object(),  # type: ignore[arg-type]
        )
    forged_runtime = object.__new__(_GovernedJailedFirecrackerExecutionV1)
    with pytest.raises(TypeError, match="governed jailed Firecracker execution"):
        _bind_governed_firecracker_spot_v7_settlement_v1(
            runtime_execution=forged_runtime,
        )
    with pytest.raises(TypeError, match="governed binder seal"):
        _GovernedFirecrackerSpotV7SettlementV1(
            runtime_execution=forged_runtime,
            seal=object(),  # type: ignore[arg-type]
        )


def test_unminted_governed_capability_types_still_reject_copy_and_serialization() -> None:
    forged_values = (
        object.__new__(_GovernedJailedFirecrackerExecutionV1),
        object.__new__(_GovernedFirecrackerSpotV7SettlementV1),
    )

    for forged in forged_values:
        for operation in (copy.copy, copy.deepcopy, pickle.dumps):
            with pytest.raises(TypeError):
                operation(forged)


def test_future_capability_defers_retry_and_exact_once_to_atomic_store() -> None:
    source = inspect.getsource(_GovernedFirecrackerSpotV7SettlementV1)

    assert "_OneShotSpotV7CapabilityUseV1" not in source
    assert "_claim_once" not in source
    assert "_consumed" not in source
    assert "_candidate_for_atomic_store" in source


@pytest.mark.parametrize(
    "untrusted_capability",
    (
        b"raw SpotSettlementV7VerifierOutputV1 bytes",
        {"settlement_authority": True},
        {"docker_replay_verified": True},
        True,
        object(),
    ),
)
def test_governed_store_sink_rejects_forgeable_values_without_mutating_state(
    tmp_path: Path,
    untrusted_capability: object,
) -> None:
    store = _store(tmp_path)
    before_cursor = store.read_cursor()
    before_rows = _database_rows(store.path)

    with patch.object(
        SQLiteSpotV7AtomicSettlementStoreV1,
        "_connect",
        side_effect=AssertionError("governed rejection must precede SQLite"),
    ):
        with pytest.raises(TypeError, match="governed Firecracker Spot V7 capability"):
            store._commit_governed_firecracker_capability(
                expected_cursor=before_cursor,
                capability=untrusted_capability,
            )

    assert store.read_cursor() == before_cursor
    assert _database_rows(store.path) == before_rows


def test_decoded_or_bound_unjailed_output_rejects_before_sqlite_mutation(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    before_cursor = store.read_cursor()
    before_rows = _database_rows(store.path)
    bound, _, _ = _bound_committed_output()

    for unjailed_value in (bound.decoded_output, bound):
        with patch.object(
            SQLiteSpotV7AtomicSettlementStoreV1,
            "_connect",
            side_effect=AssertionError("unjailed output must reject before SQLite"),
        ):
            with pytest.raises(
                TypeError,
                match="governed Firecracker Spot V7 capability",
            ):
                store._commit_governed_firecracker_capability(
                    expected_cursor=before_cursor,
                    capability=unjailed_value,
                )

    assert store.read_cursor() == before_cursor
    assert _database_rows(store.path) == before_rows


def test_object_new_forged_exact_capability_rejects_before_sqlite_mutation(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    before_cursor = store.read_cursor()
    before_rows = _database_rows(store.path)
    forged = object.__new__(_GovernedFirecrackerSpotV7SettlementV1)

    with patch.object(
        SQLiteSpotV7AtomicSettlementStoreV1,
        "_connect",
        side_effect=AssertionError("governed rejection must precede SQLite"),
    ):
        with pytest.raises(TypeError, match="module-private governed binder seal"):
            store._commit_governed_firecracker_capability(
                expected_cursor=before_cursor,
                capability=forged,
            )

    assert store.read_cursor() == before_cursor
    assert _database_rows(store.path) == before_rows


def test_exact_sealed_but_unavailable_capability_rejects_before_sqlite_mutation(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    before_cursor = store.read_cursor()
    before_rows = _database_rows(store.path)
    bound, _, _ = _bound_committed_output()
    runtime = _GovernedJailedFirecrackerExecutionV1(
        bound,
        seal=firecracker_authority_module._GOVERNED_RUNTIME_SEAL_V1,
    )
    capability = _GovernedFirecrackerSpotV7SettlementV1(
        runtime_execution=runtime,
        seal=firecracker_authority_module._GOVERNED_BINDER_SEAL_V1,
    )

    with patch.object(
        SQLiteSpotV7AtomicSettlementStoreV1,
        "_connect",
        side_effect=AssertionError("unavailable authority must precede SQLite"),
    ):
        with pytest.raises(SpotV7FirecrackerAuthorityUnavailableV1):
            store._commit_governed_firecracker_capability(
                expected_cursor=before_cursor,
                capability=capability,
            )

    assert store.read_cursor() == before_cursor
    assert _database_rows(store.path) == before_rows


def test_python_cell_hashing_matches_the_reviewed_rust_v7_fixed_vector() -> None:
    """Detect drift against one reviewed Rust effect-binding vector."""

    sender = _subject(0xAA, 48)
    pool = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686"
    input_asset = _subject(0x11, 32)
    output_asset = _subject(0x22, 32)
    rows = (
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, input_asset, 5_000),
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, input_asset, 4_000),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, input_asset, 1_000_000),
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, input_asset, 1_001_000),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, output_asset, 2_000_000),
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, output_asset, 1_998_008),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, output_asset, 100),
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, output_asset, 2_092),
        ),
    )
    ordered = tuple(sorted(rows, key=lambda row: row.cell_key))

    assert spot_v7_cell_transitions_root_v1(ordered) == (
        "0xe7750210d2ebbcad884ec908e5f371405a53c423d5adbf3bc340c74dc709787b"
    )


def test_test_only_capability_cannot_be_copied_pickled_or_claim_authority() -> None:
    candidate = _candidate()

    assert candidate.settlement_authority is False
    assert candidate.production_authority is False
    assert candidate.firecracker_execution_verified is False
    assert candidate.authority_blocked_reason == (
        SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
    )
    for operation in (copy.copy, copy.deepcopy, pickle.dumps):
        with pytest.raises(TypeError):
            operation(candidate)
    with pytest.raises(TypeError, match="cannot be mutated"):
        candidate._input = candidate._input


@pytest.mark.parametrize("direction", ["all_deposits", "all_withdrawals"])
def test_restricted_spot_candidate_requires_opposite_global_leg_directions(
    direction: str,
) -> None:
    base = _candidate(output_atoms=10)
    action = base.economic_action_id
    if direction == "all_deposits":
        rows = (
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_000),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 900),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_100),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 25),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 15),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_010),
            ),
        )
    else:
        rows = (
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 4_900),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_000),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_100),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 7_990),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 25),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 35),
            ),
        )
    transitions = tuple(sorted(rows, key=lambda row: row.cell_key))
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, _INPUT_ASSET, 100),
                SpotV7AssetEffectV1(action, _OUTPUT_ASSET, 10),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    proposal = replace(
        base._input,
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
        asset_effects=effects,
    )

    with pytest.raises(
        ValueError,
        match="restricted Spot V7 requires one input leg and one output leg",
    ):
        _seal_test_only_spot_v7_settlement_v1(proposal)


@pytest.mark.parametrize("method_name", ["read_cursor", "read_cells", "get_receipt"])
def test_read_entrypoints_hold_one_sqlite_snapshot_through_history_validation(
    tmp_path: Path,
    method_name: str,
) -> None:
    store = _store(tmp_path)
    observed: list[bool] = []
    real_validate = store_module._validate_complete_spot_v7_history

    def assert_transaction(connection: sqlite3.Connection) -> None:
        observed.append(connection.in_transaction)
        real_validate(connection)

    with patch.object(
        store_module,
        "_validate_complete_spot_v7_history",
        side_effect=assert_transaction,
    ):
        if method_name == "read_cursor":
            store.read_cursor()
        elif method_name == "read_cells":
            store.read_cells()
        else:
            store.get_receipt(_hash(900))

    assert observed == [True]


def test_given_test_sealed_v7_candidate_when_committed_then_state_and_ids_move_atomically(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert result.committed is True
    assert result.settlement_authority is False
    assert result.production_authority is False
    assert result.head_cursor.revision == 1
    assert result.head_cursor.state_root == candidate.post_state_root
    assert result.receipt is not None
    assert result.receipt.firecracker_execution_verified is False
    assert result.receipt.settlement_authority is False
    assert result.receipt.production_authority is False
    assert result.receipt.receipt_sha256 == candidate.receipt_sha256
    assert result.receipt.firecracker_execution_record_sha256 == (
        candidate.firecracker_execution_record_sha256
    )
    assert result.receipt.economic_action_id == candidate.economic_action_id
    assert result.receipt.authorization_nullifier == candidate.authorization_nullifier
    assert result.receipt.authorization_grant_spend_nullifier == (
        candidate.authorization_grant_spend_nullifier
    )
    cells = {cell.cell_key: cell for cell in store.read_cells()}
    assert cells == {row.post.cell_key: row.post for row in candidate.cell_transitions}


@pytest.mark.parametrize("mode", ["cursor", "pre_state", "cell_pre_state"])
def test_given_stale_or_mismatched_state_when_committing_then_reject_is_no_op(
    tmp_path: Path,
    mode: str,
) -> None:
    store = _store(tmp_path)
    expected = store.read_cursor()
    candidate = _candidate()
    if mode == "cursor":
        expected = replace(expected, state_root=_hash(999))
        expected_reason = SpotV7AtomicSettlementRejectReasonV1.CURSOR_MISMATCH
    elif mode == "pre_state":
        candidate = _candidate(pre_state_root=_hash(998))
        expected_reason = SpotV7AtomicSettlementRejectReasonV1.PRE_STATE_ROOT_MISMATCH
    else:
        candidate = _candidate(values=(999, 5_000, 8_000, 25))
        expected_reason = SpotV7AtomicSettlementRejectReasonV1.CELL_PRE_STATE_MISMATCH
    before = _database_rows(store.path)

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=expected,
        candidate=candidate,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.REJECTED
    assert result.reject_reason is expected_reason
    assert _database_rows(store.path) == before


def test_given_lost_response_when_exact_candidate_retries_then_result_is_idempotent(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    candidate = _candidate()
    committed = store._commit_test_only_sealed_candidate(
        expected_cursor=initial,
        candidate=candidate,
    )

    retried = store._commit_test_only_sealed_candidate(
        expected_cursor=initial,
        candidate=candidate,
    )

    assert committed.committed is True
    assert retried.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY
    assert retried.receipt == committed.receipt
    assert retried.head_cursor == committed.head_cursor


def test_given_two_concurrent_exact_retries_then_exactly_one_transaction_commits(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    cursor = store.read_cursor()
    candidate = _candidate()
    barrier = Barrier(2)

    def submit():
        barrier.wait()
        return store._commit_test_only_sealed_candidate(
            expected_cursor=cursor,
            candidate=candidate,
        )

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = tuple(executor.map(lambda _index: submit(), range(2)))

    assert sum(result.committed for result in results) == 1
    assert sum(result.idempotent_replay for result in results) == 1
    assert store.read_cursor().revision == 1


def test_given_two_concurrent_conflicts_then_exactly_one_transaction_commits(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    cursor = store.read_cursor()
    first = _candidate(seed=100)
    second = _candidate(seed=200, action_id=first.economic_action_id)
    barrier = Barrier(2)

    def submit(candidate):
        barrier.wait()
        return store._commit_test_only_sealed_candidate(
            expected_cursor=cursor,
            candidate=candidate,
        )

    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = (executor.submit(submit, first), executor.submit(submit, second))
        results = tuple(future.result() for future in futures)

    assert sum(result.committed for result in results) == 1
    assert sum(result.disposition is SpotV7AtomicSettlementDispositionV1.REJECTED for result in results) == 1
    assert store.read_cursor().revision == 1


@pytest.mark.parametrize("reused_field", ["action", "authorization", "grant_spend"])
def test_given_reused_economic_identity_when_next_state_commits_then_duplicate_rejects_no_op(
    tmp_path: Path,
    reused_field: str,
) -> None:
    store = _store(tmp_path)
    first = _candidate()
    first_result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=first,
    )
    assert first_result.committed is True
    values = (900, 5_100, 7_940, 85)
    overrides = {
        "action_id": first.economic_action_id if reused_field == "action" else None,
        "authorization_nullifier": (
            first.authorization_nullifier if reused_field == "authorization" else None
        ),
        "grant_spend_nullifier": (
            first.authorization_grant_spend_nullifier if reused_field == "grant_spend" else None
        ),
    }
    second = _candidate(
        seed=200,
        pre_state_root=first.post_state_root,
        values=values,
        input_atoms=50,
        output_atoms=30,
        **overrides,
    )
    before = _database_rows(store.path)

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=second,
    )

    expected = {
        "action": SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_ECONOMIC_ACTION,
        "authorization": SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_NULLIFIER,
        "grant_spend": SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND,
    }[reused_field]
    assert result.reject_reason is expected
    assert _database_rows(store.path) == before


@pytest.mark.parametrize(
    ("field", "reason"),
    [
        ("exact_v7_receipt_bytes", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_RECEIPT),
        ("exact_v7_journal_bytes", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_JOURNAL),
        (
            "exact_firecracker_execution_record_bytes",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FIRECRACKER_EXECUTION,
        ),
        (
            "exact_firecracker_output_bytes",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FIRECRACKER_OUTPUT,
        ),
        (
            "settlement_effect_plan_commitment",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN,
        ),
        ("exact_plan_b_bytes", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN),
        ("source_child_claim_binding", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SOURCE_CHILD),
        ("source_child_journal_sha256", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SOURCE_CHILD),
        ("post_state_root", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_POST_STATE_ROOT),
    ],
)
def test_given_reused_proof_or_execution_identity_then_typed_duplicate_rejects_no_op(
    tmp_path: Path,
    field: str,
    reason: SpotV7AtomicSettlementRejectReasonV1,
) -> None:
    store = _store(tmp_path)
    first = _candidate()
    committed = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=first,
    )
    assert committed.committed is True
    second = _candidate(
        seed=200,
        pre_state_root=first.post_state_root,
        values=(900, 5_100, 7_940, 85),
        input_atoms=50,
        output_atoms=30,
    )
    replacement = getattr(first._input, field)
    proposal = replace(second._input, **{field: replacement})
    candidate = _seal_test_only_spot_v7_settlement_v1(proposal)
    before = _database_rows(store.path)

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )

    assert result.reject_reason is reason
    assert _database_rows(store.path) == before


def test_given_failure_after_cell_updates_when_transaction_aborts_then_all_rows_roll_back(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    before = _database_rows(store.path)
    candidate = _candidate()
    cursor = store.read_cursor()

    with patch(
        "src.integration._zrpf_spot_v7_atomic_settlement_engine._persist_asset_effects",
        side_effect=sqlite3.IntegrityError("injected post-cell failure"),
    ):
        with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED"):
            store._commit_test_only_sealed_candidate(
                expected_cursor=cursor,
                candidate=candidate,
            )

    assert _database_rows(store.path) == before


def test_given_failure_after_metadata_cas_when_transaction_aborts_then_all_rows_roll_back(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    before = _database_rows(store.path)
    candidate = _candidate()
    cursor = store.read_cursor()
    real_validate = store_module._validate_complete_spot_v7_history
    calls = 0

    def fail_second_validation(connection: sqlite3.Connection) -> None:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise ValueError("injected post-CAS failure")
        real_validate(connection)

    with patch.object(
        store_module,
        "_validate_complete_spot_v7_history",
        side_effect=fail_second_validation,
    ):
        with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED"):
            store._commit_test_only_sealed_candidate(
                expected_cursor=cursor,
                candidate=candidate,
            )

    assert _database_rows(store.path) == before


def test_given_committed_history_when_store_reopens_then_exact_state_reconstructs(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()
    committed = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )
    assert committed.receipt is not None

    reopened = _reopen(store)

    assert reopened.read_cursor() == committed.head_cursor
    assert reopened.get_receipt(candidate.settlement_commitment) == committed.receipt
    assert reopened.read_cells() == tuple(row.post for row in candidate.cell_transitions)


def test_given_tampered_persisted_cell_when_store_reopens_then_history_replay_rejects(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()
    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )
    assert result.committed is True
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_cells SET atoms_be = zeroblob(16) WHERE cell_key = ?",
            (bytes.fromhex(candidate.cell_transitions[0].cell_key[2:]),),
        )
        connection.commit()

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        _reopen(store)


@pytest.mark.parametrize("tamper", ["updated_revision", "journal", "authority"])
def test_given_tampered_persisted_metadata_when_store_reopens_then_rejects(
    tmp_path: Path,
    tamper: str,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()
    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )
    assert result.committed is True
    with sqlite3.connect(store.path) as connection:
        if tamper == "updated_revision":
            connection.execute("UPDATE spot_v7_cells SET updated_revision = 0")
        elif tamper == "journal":
            connection.execute(
                "UPDATE spot_v7_settlements SET exact_v7_journal = ?",
                (b"tampered-journal",),
            )
        else:
            with pytest.raises(sqlite3.IntegrityError):
                connection.execute(
                    "UPDATE spot_v7_settlements SET settlement_authority = 1"
                )
            return
        connection.commit()

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        _reopen(store)


def test_given_reopened_store_when_identity_or_genesis_cells_drift_then_open_fails_closed(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=replace(_identity(), verified_program_id=_hash(700)),
            genesis_cells=_initial_cells(),
        )
    changed = list(_initial_cells())
    changed[0] = replace(changed[0], atoms=changed[0].atoms + 1)
    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=_identity(),
            genesis_cells=tuple(changed),
        )
