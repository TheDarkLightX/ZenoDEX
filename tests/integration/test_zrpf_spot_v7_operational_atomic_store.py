"""Atomic authority-false Spot V7 economics, full-blob, and finality evidence."""

from __future__ import annotations

import copy
import hashlib
import pickle
import sqlite3
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from threading import Barrier
from unittest.mock import patch

import pytest

import src.integration._zrpf_spot_v7_firecracker_authority as firecracker_authority
import src.integration._zrpf_spot_v7_operational_capability_v2 as operational_v2
import src.integration.zrpf_spot_v7_atomic_settlement_store as store_module
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _seal_test_only_spot_v7_settlement_v1,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AuthenticatedExactCheckpointFinalityTransitionV2,
    _bind_spot_v7_operational_commit_capability_v2,
    _GovernedExactFullBlobPolicySatisfactionV2,
    _GovernedOperationalPolicyMaterialV2,
    _GovernedOperationalPolicyProvenanceV1,
    _GovernedSpotV7OperationalPolicyV2,
    _SpotV7AtomicEconomicCommitCapabilityV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _AuthenticatedCheckpointFinalityProjectionV2,
    _GovernedFullBlobPolicyProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _build_test_only_checkpoint_finality_artifacts_v2,
    _build_test_only_full_blob_artifacts_v1,
    _encode_checkpoint_finality_certificate_v2,
    _finality_certificate_root_v2,
    _seal_test_only_spot_v7_operational_commit_v1,
    _TestOnlyCheckpointFinalityArtifactsV2,
    _TestOnlyFullBlobArtifactsV1,
    _TestOnlySpotV7OperationalCommitInputV1,
    _TestOnlySpotV7OperationalCommitV1,
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_store import (
    SQLiteSpotV7AtomicSettlementStoreV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AssetEffectV1,
    SpotV7AtomicSettlementCursorV1,
    SpotV7AtomicSettlementDispositionV1,
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7AtomicSettlementResultV1,
    SpotV7AtomicSettlementStoreErrorV1,
    SpotV7AtomicSettlementStoreIdentityV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    spot_v7_cell_transitions_root_v1,
)


def _root(seed: int) -> str:
    return f"0x{seed:064x}"


def _repeat_root(byte: int) -> str:
    return "0x" + (bytes((byte,)) * 32).hex()


def _subject(byte: int, length: int) -> str:
    return "0x" + (bytes((byte,)) * length).hex()


_SENDER = _subject(0x11, 48)
_POOL = _subject(0x22, 32)
_INPUT_ASSET = _root(0x33)
_OUTPUT_ASSET = _root(0x44)
_RECIPIENT = _subject(0x55, 48)


def _opening(
    kind: SpotV7CellKindV1,
    subject_id: str,
    asset_id: str,
    atoms: int,
) -> SpotV7CellOpeningV1:
    return SpotV7CellOpeningV1(kind, subject_id, asset_id, atoms)


def _transitions(
    values: tuple[int, int, int, int],
    *,
    input_atoms: int,
    output_atoms: int,
) -> tuple[SpotV7CellTransitionV1, ...]:
    sender_input, pool_input, pool_output, recipient_output = values
    rows = (
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, sender_input),
            _opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _SENDER,
                _INPUT_ASSET,
                sender_input - input_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, pool_input),
            _opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _INPUT_ASSET,
                pool_input + input_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, pool_output),
            _opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _OUTPUT_ASSET,
                pool_output - output_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            _opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _RECIPIENT,
                _OUTPUT_ASSET,
                recipient_output,
            ),
            _opening(
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
        application_id=_root(1),
        chain_or_domain_id=_root(2),
        verified_program_id=_root(3),
        verified_profile_id=_root(4),
        verified_program_manifest_root=_root(5),
        genesis_state_root=_root(6),
    )


def _initial_cells() -> tuple[SpotV7CellOpeningV1, ...]:
    return tuple(
        sorted(
            (
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_000),
                _opening(
                    SpotV7CellKindV1.ACCOUNT_BALANCE,
                    _RECIPIENT,
                    _OUTPUT_ASSET,
                    25,
                ),
            ),
            key=lambda row: row.cell_key,
        )
    )


def _policy() -> _TestOnlySpotV7OperationalPolicyV1:
    return _TestOnlySpotV7OperationalPolicyV1(
        application_id=_identity().application_id,
        chain_or_domain_id=_identity().chain_or_domain_id,
        data_schema_id=_root(30),
        storage_policy_hash=_root(31),
        minimum_retention_epochs=20,
        minimum_remaining_epochs=5,
        maximum_blob_bytes=1_048_576,
        finality_network_id=_root(32),
        finality_protocol_id=_root(33),
        external_finality_policy_hash=_root(34),
        finality_verifier_set_root=_root(35),
        genesis_application_checkpoint_sequence=40,
        genesis_application_checkpoint_hash=_root(36),
    )


def _packet(
    *,
    seed: int = 100,
    pre_state_root: str | None = None,
    values: tuple[int, int, int, int] = (1_000, 5_000, 8_000, 25),
    input_atoms: int = 100,
    output_atoms: int = 60,
    prior_checkpoint_sequence: int = 40,
    prior_checkpoint_hash: str | None = None,
    blob: bytes | None = None,
    finality_evidence: bytes | None = None,
) -> _TestOnlySpotV7OperationalCommitV1:
    policy = _policy()
    exact_blob = blob or f"canonical-epoch-blob-{seed}".encode()
    da = _build_test_only_full_blob_artifacts_v1(
        policy=policy,
        epoch_id=seed,
        checked_epoch=seed,
        retention_through_epoch=seed + 20,
        exact_blob_bytes=exact_blob,
    )
    action = _root(seed + 1)
    transitions = _transitions(
        values,
        input_atoms=input_atoms,
        output_atoms=output_atoms,
    )
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, _INPUT_ASSET, input_atoms),
                SpotV7AssetEffectV1(action, _OUTPUT_ASSET, output_atoms),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    identity = _identity()
    settlement = _seal_test_only_spot_v7_settlement_v1(
        _SpotV7SettlementCandidateInputV1(
            application_id=identity.application_id,
            chain_or_domain_id=identity.chain_or_domain_id,
            epoch_id=seed,
            verified_program_id=identity.verified_program_id,
            verified_profile_id=identity.verified_profile_id,
            verified_program_manifest_root=identity.verified_program_manifest_root,
            source_child_claim_binding=_root(seed + 2),
            source_child_journal_sha256=_root(seed + 3),
            data_availability_certificate_root=da.certificate_root,
            data_root=da.data_root,
            settlement_effect_plan_commitment=_root(seed + 6),
            pre_state_root=pre_state_root or identity.genesis_state_root,
            post_state_root=_root(seed + 7),
            economic_action_id=action,
            authorization_nullifier=_root(seed + 8),
            authorization_grant_spend_nullifier=_root(seed + 9),
            consumed_object_ids=(_root(seed + 10), _root(seed + 11)),
            cell_transitions=transitions,
            cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
            asset_effects=effects,
            exact_v7_receipt_bytes=f"receipt-{seed}".encode(),
            exact_v7_journal_bytes=f"journal-{seed}".encode(),
            exact_plan_b_bytes=f"plan-b-{seed}".encode(),
            exact_firecracker_execution_record_bytes=f"execution-{seed}".encode(),
            exact_firecracker_output_bytes=f"output-{seed}".encode(),
        )
    )
    finality = _build_test_only_checkpoint_finality_artifacts_v2(
        policy=policy,
        settlement=settlement,
        prior_application_checkpoint_sequence=prior_checkpoint_sequence,
        prior_application_checkpoint_hash=(
            prior_checkpoint_hash or policy.genesis_application_checkpoint_hash
        ),
        next_application_checkpoint_hash=_root(seed + 60),
        exact_finality_evidence_bytes=(finality_evidence or f"finality-evidence-{seed}".encode()),
    )
    return _seal_test_only_spot_v7_operational_commit_v1(
        _TestOnlySpotV7OperationalCommitInputV1(
            settlement=settlement,
            policy=policy,
            data_availability=da,
            finality=finality,
        )
    )


def _store(tmp_path: Path) -> SQLiteSpotV7AtomicSettlementStoreV1:
    directory = tmp_path / "private"
    directory.mkdir(mode=0o700)
    return SQLiteSpotV7AtomicSettlementStoreV1(
        directory / "spot-v7.sqlite3",
        identity=_identity(),
        genesis_cells=_initial_cells(),
        test_only_operational_policy=_policy(),
    )


def _reopen(store: SQLiteSpotV7AtomicSettlementStoreV1) -> SQLiteSpotV7AtomicSettlementStoreV1:
    return SQLiteSpotV7AtomicSettlementStoreV1(
        store.path,
        identity=_identity(),
        genesis_cells=_initial_cells(),
        test_only_operational_policy=_policy(),
    )


def _governed_policy_v2(
    policy: _TestOnlySpotV7OperationalPolicyV1 | None = None,
    *,
    policy_revocation_epoch: int | None = None,
    provenance_bytes: bytes = b'{"schema":"test-only-operational-policy-provenance-v1"}',
) -> _GovernedSpotV7OperationalPolicyV2:
    value = policy or _policy()
    return _GovernedSpotV7OperationalPolicyV2(
        _GovernedOperationalPolicyMaterialV2(
            application_id=value.application_id,
            chain_or_domain_id=value.chain_or_domain_id,
            data_schema_id=value.data_schema_id,
            storage_policy_hash=value.storage_policy_hash,
            minimum_retention_epochs=value.minimum_retention_epochs,
            minimum_remaining_epochs=value.minimum_remaining_epochs,
            maximum_blob_bytes=value.maximum_blob_bytes,
            finality_network_id=value.finality_network_id,
            finality_protocol_id=value.finality_protocol_id,
            external_finality_policy_hash=value.external_finality_policy_hash,
            finality_verifier_set_root=value.finality_verifier_set_root,
            genesis_application_checkpoint_sequence=(value.genesis_application_checkpoint_sequence),
            genesis_application_checkpoint_hash=(value.genesis_application_checkpoint_hash),
        ),
        provenance=_GovernedOperationalPolicyProvenanceV1(
            evidence_root="0x" + hashlib.sha256(provenance_bytes).hexdigest(),
            exact_evidence_bytes=provenance_bytes,
            manifest_sha256=hashlib.sha256(b"test-only-manifest").hexdigest(),
            signer_registry_hash=_root(0x901),
            signature_quorum_report_hash=_root(0x902),
            policy_revision=1,
            policy_activation_epoch=0,
            policy_revocation_epoch=policy_revocation_epoch,
            signer_registry_revision=1,
            signer_registry_activation_epoch=0,
            signer_registry_revocation_epoch=None,
            evaluation_epoch=1,
        ),
        seal=operational_v2._GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )


def _governed_settlement_v2(
    candidate: _SpotV7SettlementCandidateInputV1,
) -> _GovernedFirecrackerSpotV7SettlementV1:
    capability = object.__new__(_GovernedFirecrackerSpotV7SettlementV1)
    object.__setattr__(capability, "_candidate", candidate)
    object.__setattr__(capability, "_runtime_execution", object())
    object.__setattr__(
        capability,
        "_seal",
        firecracker_authority._GOVERNED_BINDER_SEAL_V1,
    )
    return capability


def _governed_v2_components(
    packet: _TestOnlySpotV7OperationalCommitV1 | None = None,
    *,
    policy_revocation_epoch: int | None = None,
) -> tuple[
    _GovernedFirecrackerSpotV7SettlementV1,
    _GovernedSpotV7OperationalPolicyV2,
    _GovernedExactFullBlobPolicySatisfactionV2,
    _AuthenticatedExactCheckpointFinalityTransitionV2,
]:
    value = (packet or _packet())._input
    settlement = _governed_settlement_v2(value.settlement._input)
    policy = _governed_policy_v2(
        value.policy,
        policy_revocation_epoch=policy_revocation_epoch,
    )
    da = value.data_availability
    governed_da = _GovernedExactFullBlobPolicySatisfactionV2(
        _GovernedFullBlobPolicyProjectionV1(
            application_id=value.policy.application_id,
            chain_or_domain_id=value.policy.chain_or_domain_id,
            epoch_id=da.epoch_id,
            certificate_root=da.certificate_root,
            data_root=da.data_root,
            policy_root=da.policy_root,
            exact_blob_sha256=da.blob_sha256,
            checked_epoch=da.checked_epoch,
            retention_through_epoch=da.retention_through_epoch,
        ),
        governed_policy=policy,
        exact_blob_bytes=da.exact_blob_bytes,
        exact_certificate_bytes=da.exact_certificate_bytes,
        seal=operational_v2._GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
    )
    finality = value.finality
    governed_finality = _AuthenticatedExactCheckpointFinalityTransitionV2(
        _AuthenticatedCheckpointFinalityProjectionV2(
            application_id=value.policy.application_id,
            chain_or_domain_id=value.policy.chain_or_domain_id,
            epoch_id=finality.epoch_id,
            proof_journal_hash=finality.proof_journal_hash,
            post_state_root=finality.post_state_root,
            policy_root=finality.policy_root,
            certificate_root=finality.certificate_root,
            finality_evidence_root=finality.finality_evidence_root,
            prior_application_checkpoint_sequence=(finality.prior_application_checkpoint_sequence),
            prior_application_checkpoint_hash=(finality.prior_application_checkpoint_hash),
            next_application_checkpoint_sequence=(finality.next_application_checkpoint_sequence),
            next_application_checkpoint_hash=(finality.next_application_checkpoint_hash),
        ),
        exact_certificate_bytes=finality.exact_certificate_bytes,
        exact_finality_evidence_bytes=finality.exact_finality_evidence_bytes,
        seal=operational_v2._AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2,
    )
    return settlement, policy, governed_da, governed_finality


def _governed_v2_capability(
    packet: _TestOnlySpotV7OperationalCommitV1 | None = None,
    *,
    policy_revocation_epoch: int | None = None,
) -> tuple[
    _SpotV7AtomicEconomicCommitCapabilityV2,
    _GovernedSpotV7OperationalPolicyV2,
]:
    settlement, policy, da, finality = _governed_v2_components(
        packet,
        policy_revocation_epoch=policy_revocation_epoch,
    )
    return (
        _bind_spot_v7_operational_commit_capability_v2(
            settlement=settlement,
            policy=policy,
            data_availability=da,
            finality=finality,
        ),
        policy,
    )


def _governed_store_v2(
    tmp_path: Path,
    policy: _GovernedSpotV7OperationalPolicyV2,
) -> SQLiteSpotV7AtomicSettlementStoreV1:
    directory = tmp_path / "governed-private"
    directory.mkdir(mode=0o700)
    return SQLiteSpotV7AtomicSettlementStoreV1(
        directory / "spot-v7.sqlite3",
        identity=_identity(),
        genesis_cells=_initial_cells(),
        governed_operational_policy=policy,
    )


def _database_rows(path: Path) -> tuple[tuple[str, tuple[tuple[object, ...], ...]], ...]:
    with sqlite3.connect(path) as connection:
        tables = tuple(
            str(row[0])
            for row in connection.execute(
                "SELECT name FROM sqlite_master WHERE type='table' "
                "AND name NOT LIKE 'sqlite_%' ORDER BY name"
            )
        )
        return tuple(
            (
                table,
                tuple(connection.execute(f"SELECT * FROM {table}").fetchall()),
            )
            for table in tables
        )


def _operational_cursor(path: Path) -> tuple[int, str]:
    with sqlite3.connect(path) as connection:
        row = connection.execute(
            "SELECT current_checkpoint_sequence_be, current_checkpoint_hash "
            "FROM spot_v7_operational_policy WHERE singleton = 1"
        ).fetchone()
    assert row is not None
    return int.from_bytes(row[0], "big"), "0x" + bytes(row[1]).hex()


def test_given_exact_sealed_v2_inputs_when_committed_then_every_surface_moves_once(
    tmp_path: Path,
) -> None:
    source_packet = _packet()
    capability, policy = _governed_v2_capability(source_packet)
    store = _governed_store_v2(tmp_path, policy)
    before = store.read_cursor()

    result = store._commit_operational_capability(
        expected_cursor=before,
        capability=capability,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert result.settlement_authority is False
    assert result.production_authority is False
    assert store.settlement_authority is False
    assert store.production_authority is False
    assert store.read_cursor().revision == 1
    with sqlite3.connect(store.path) as connection:
        counts = tuple(
            int(connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0])
            for table in (
                "spot_v7_settlements",
                "spot_v7_operational_da",
                "spot_v7_operational_finality",
            )
        )
        authority = connection.execute(
            "SELECT settlement_authority, production_authority "
            "FROM spot_v7_store_meta WHERE singleton = 1"
        ).fetchone()
        exact_da = connection.execute(
            "SELECT exact_blob, exact_certificate FROM spot_v7_operational_da"
        ).fetchone()
        exact_finality = connection.execute(
            "SELECT exact_certificate, exact_finality_evidence FROM spot_v7_operational_finality"
        ).fetchone()
    assert counts == (1, 1, 1)
    assert authority == (0, 0)
    assert exact_da == (
        source_packet._input.data_availability.exact_blob_bytes,
        source_packet._input.data_availability.exact_certificate_bytes,
    )
    assert exact_finality == (
        source_packet._input.finality.exact_certificate_bytes,
        source_packet._input.finality.exact_finality_evidence_bytes,
    )


def test_atomic_sink_rechecks_policy_lifecycle_before_opening_transaction(
    tmp_path: Path,
) -> None:
    source_packet = _packet()
    epoch_id = source_packet._input.settlement._input.epoch_id
    capability, policy = _governed_v2_capability(
        source_packet,
        policy_revocation_epoch=epoch_id,
    )
    store = _governed_store_v2(tmp_path, policy)
    before = _database_rows(store.path)

    with pytest.raises(ValueError, match="revoked at the checked epoch"):
        store._commit_operational_capability(
            expected_cursor=store.read_cursor(),
            capability=capability,
        )

    assert _database_rows(store.path) == before


def test_governed_store_persists_exact_policy_release_provenance(
    tmp_path: Path,
) -> None:
    policy = _governed_policy_v2()
    provenance = policy._policy_provenance_for_atomic_store()
    store = _governed_store_v2(tmp_path, policy)

    with sqlite3.connect(store.path) as connection:
        connection.row_factory = sqlite3.Row
        assert connection.execute("PRAGMA user_version").fetchone()[0] == 3
        row = connection.execute(
            "SELECT * FROM spot_v7_operational_policy_provenance WHERE singleton = 1"
        ).fetchone()

    assert row is not None
    assert bytes(row["evidence_root"]) == bytes.fromhex(provenance.evidence_root[2:])
    assert bytes(row["manifest_sha256"]) == bytes.fromhex(provenance.manifest_sha256)
    assert bytes(row["signer_registry_hash"]) == bytes.fromhex(
        provenance.signer_registry_hash[2:]
    )
    assert bytes(row["signature_quorum_report_hash"]) == bytes.fromhex(
        provenance.signature_quorum_report_hash[2:]
    )
    assert bytes(row["exact_evidence"]) == provenance.exact_evidence_bytes
    assert tuple(
        int(row[field])
        for field in ("release_authority", "settlement_authority", "production_authority")
    ) == (0, 0, 0)


def test_governed_store_reopen_rejects_policy_provenance_tamper(
    tmp_path: Path,
) -> None:
    policy = _governed_policy_v2()
    store = _governed_store_v2(tmp_path, policy)
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_operational_policy_provenance SET exact_evidence = ? "
            "WHERE singleton = 1",
            (b"tampered-policy-release-provenance",),
        )
        connection.commit()

    with pytest.raises(
        SpotV7AtomicSettlementStoreErrorV1,
        match="stored operational policy provenance root mismatch",
    ):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=_identity(),
            genesis_cells=_initial_cells(),
            governed_operational_policy=policy,
        )


def test_governed_store_reopen_rejects_different_release_for_same_policy_material(
    tmp_path: Path,
) -> None:
    policy = _governed_policy_v2()
    store = _governed_store_v2(tmp_path, policy)
    replacement = _governed_policy_v2(
        provenance_bytes=b'{"schema":"different-test-release-provenance-v1"}'
    )

    with pytest.raises(
        SpotV7AtomicSettlementStoreErrorV1,
        match="stored operational policy provenance",
    ):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=_identity(),
            genesis_cells=_initial_cells(),
            governed_operational_policy=replacement,
        )


def test_atomic_sink_rejects_coherent_policy_provenance_substitution_under_lock(
    tmp_path: Path,
) -> None:
    source_packet = _packet()
    capability, policy = _governed_v2_capability(source_packet)
    store = _governed_store_v2(tmp_path, policy)
    substituted = b'{"schema":"coherently-substituted-policy-provenance-v1"}'
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_operational_policy_provenance "
            "SET evidence_root = ?, exact_evidence = ? WHERE singleton = 1",
            (hashlib.sha256(substituted).digest(), substituted),
        )
        connection.commit()

    with pytest.raises(
        SpotV7AtomicSettlementStoreErrorV1,
        match="stored operational policy provenance evidence mismatch",
    ):
        store._commit_operational_capability(
            expected_cursor=store.read_cursor(),
            capability=capability,
        )

    with sqlite3.connect(store.path) as connection:
        assert connection.execute("SELECT count(*) FROM spot_v7_settlements").fetchone()[0] == 0


@pytest.mark.parametrize(
    "untrusted",
    (
        True,
        {"settlement_authority": True},
        {"external_finality_authenticated": True},
        b"exact-looking-artifact-bytes",
        object(),
    ),
)
def test_given_raw_caller_data_when_binding_v2_then_type_boundary_rejects(
    untrusted: object,
) -> None:
    with pytest.raises(TypeError):
        _bind_spot_v7_operational_commit_capability_v2(
            settlement=untrusted,
            policy=untrusted,
            data_availability=untrusted,
            finality=untrusted,
        )


def test_given_v2_capability_when_copying_or_serializing_then_operation_rejects() -> None:
    capability, _policy_value = _governed_v2_capability()

    assert capability.settlement_authority is False
    assert capability.production_authority is False
    for operation in (copy.copy, copy.deepcopy, pickle.dumps):
        with pytest.raises(TypeError):
            operation(capability)


def test_given_forged_v2_capability_when_committing_then_sqlite_is_never_opened() -> None:
    store = object.__new__(SQLiteSpotV7AtomicSettlementStoreV1)
    forged = object.__new__(_SpotV7AtomicEconomicCommitCapabilityV2)

    with pytest.raises(TypeError, match="module-private seal"):
        store._commit_operational_capability(
            expected_cursor=SpotV7AtomicSettlementCursorV1(
                revision=0,
                state_root=_identity().genesis_state_root,
                settlement_count=0,
                cell_count=4,
                last_epoch_id=None,
            ),
            capability=forged,
        )


@pytest.mark.parametrize(
    "artifact",
    ("blob", "da_certificate", "finality_certificate", "finality_evidence"),
)
def test_given_mutated_exact_v2_artifact_when_binding_then_no_capability_is_minted(
    artifact: str,
) -> None:
    settlement, policy, da, finality = _governed_v2_components()
    with pytest.raises(ValueError, match="canonical|exact bytes|SHA-256|root"):
        if artifact == "blob":
            da = _GovernedExactFullBlobPolicySatisfactionV2(
                da._projection,
                governed_policy=policy,
                exact_blob_bytes=b"X" + da._exact_blob_bytes[1:],
                exact_certificate_bytes=da._exact_certificate_bytes,
                seal=operational_v2._GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
            )
        elif artifact == "da_certificate":
            da = _GovernedExactFullBlobPolicySatisfactionV2(
                da._projection,
                governed_policy=policy,
                exact_blob_bytes=da._exact_blob_bytes,
                exact_certificate_bytes=b"X" + da._exact_certificate_bytes[1:],
                seal=operational_v2._GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
            )
        elif artifact == "finality_certificate":
            finality = _AuthenticatedExactCheckpointFinalityTransitionV2(
                finality._projection,
                exact_certificate_bytes=b"X" + finality._exact_certificate_bytes[1:],
                exact_finality_evidence_bytes=finality._exact_finality_evidence_bytes,
                seal=(operational_v2._AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2),
            )
        else:
            finality = _AuthenticatedExactCheckpointFinalityTransitionV2(
                finality._projection,
                exact_certificate_bytes=finality._exact_certificate_bytes,
                exact_finality_evidence_bytes=(b"X" + finality._exact_finality_evidence_bytes[1:]),
                seal=(operational_v2._AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2),
            )
        _bind_spot_v7_operational_commit_capability_v2(
            settlement=settlement,
            policy=policy,
            data_availability=da,
            finality=finality,
        )


def test_given_v2_precheck_then_in_transaction_recheck_failure_when_committing_then_no_rows_move(
    tmp_path: Path,
) -> None:
    capability, policy = _governed_v2_capability()
    store = _governed_store_v2(tmp_path, policy)
    before = _database_rows(store.path)
    original = capability._packet_for_atomic_store
    calls = 0

    def fail_second_recheck(
        _capability: _SpotV7AtomicEconomicCommitCapabilityV2,
    ) -> _TestOnlySpotV7OperationalCommitV1:
        nonlocal calls
        calls += 1
        if calls == 1:
            return original()
        raise ValueError("injected in-transaction V2 binding drift")

    with patch.object(
        _SpotV7AtomicEconomicCommitCapabilityV2,
        "_packet_for_atomic_store",
        new=fail_second_recheck,
    ):
        with pytest.raises(
            RuntimeError,
            match="SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED",
        ):
            store._commit_operational_capability(
                expected_cursor=store.read_cursor(),
                capability=capability,
            )

    assert calls == 2
    assert _database_rows(store.path) == before
    assert store.read_cursor().revision == 0


def test_given_v2_failure_after_finality_cursor_cas_when_committing_then_every_row_rolls_back(
    tmp_path: Path,
) -> None:
    capability, policy = _governed_v2_capability()
    store = _governed_store_v2(tmp_path, policy)
    before = _database_rows(store.path)

    with patch.object(
        store_module,
        "_cas_spot_v7_meta",
        side_effect=ValueError("injected after V2 finality cursor CAS"),
    ):
        with pytest.raises(
            RuntimeError,
            match="SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED",
        ):
            store._commit_operational_capability(
                expected_cursor=store.read_cursor(),
                capability=capability,
            )

    assert _database_rows(store.path) == before
    assert _operational_cursor(store.path) == (
        _policy().genesis_application_checkpoint_sequence,
        _policy().genesis_application_checkpoint_hash,
    )


def test_given_two_concurrent_v2_retries_when_committing_then_one_complete_row_set_exists(
    tmp_path: Path,
) -> None:
    capability, policy = _governed_v2_capability()
    store = _governed_store_v2(tmp_path, policy)
    cursor = store.read_cursor()
    barrier = Barrier(2)

    def submit() -> SpotV7AtomicSettlementResultV1:
        barrier.wait()
        return store._commit_operational_capability(
            expected_cursor=cursor,
            capability=capability,
        )

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = tuple(executor.map(lambda _index: submit(), range(2)))

    dispositions = tuple(result.disposition for result in results)
    assert dispositions.count(SpotV7AtomicSettlementDispositionV1.COMMITTED) == 1
    assert dispositions.count(SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY) == 1
    assert all(result.settlement_authority is False for result in results)
    assert all(result.production_authority is False for result in results)
    with sqlite3.connect(store.path) as connection:
        counts = tuple(
            int(connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0])
            for table in (
                "spot_v7_settlements",
                "spot_v7_operational_da",
                "spot_v7_operational_finality",
            )
        )
    assert counts == (1, 1, 1)


def test_given_stale_v2_finality_cursor_when_committing_then_rejection_is_no_op(
    tmp_path: Path,
) -> None:
    first_packet = _packet()
    first_capability, policy = _governed_v2_capability(first_packet)
    store = _governed_store_v2(tmp_path, policy)
    first_result = store._commit_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=first_capability,
    )
    assert first_result.committed is True
    second_packet = _packet(
        seed=200,
        pre_state_root=first_packet._input.settlement.post_state_root,
        values=(900, 5_100, 7_940, 85),
        input_atoms=50,
        output_atoms=30,
    )
    second_capability, _same_policy = _governed_v2_capability(second_packet)
    before = _database_rows(store.path)

    rejected = store._commit_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=second_capability,
    )

    assert rejected.reject_reason is SpotV7AtomicSettlementRejectReasonV1.FINALITY_CURSOR_MISMATCH
    assert _database_rows(store.path) == before


def test_given_committed_v2_store_when_reopened_then_exact_governed_policy_is_required(
    tmp_path: Path,
) -> None:
    capability, policy = _governed_v2_capability()
    store = _governed_store_v2(tmp_path, policy)
    committed = store._commit_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=capability,
    )
    assert committed.committed is True

    reopened = SQLiteSpotV7AtomicSettlementStoreV1(
        store.path,
        identity=_identity(),
        genesis_cells=_initial_cells(),
        governed_operational_policy=policy,
    )

    assert reopened.read_cursor() == committed.head_cursor
    assert reopened.authority_false_v2_operational_sink_available is True
    assert reopened.operational_commit_gate_available is False
    assert reopened.settlement_authority is False
    assert reopened.production_authority is False
    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=_identity(),
            genesis_cells=_initial_cells(),
        )


def test_combined_transaction_persists_economics_blob_certificate_and_finality(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    packet = _packet()
    value = packet._input

    result = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=packet,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert result.settlement_authority is False
    assert result.production_authority is False
    assert result.head_cursor.state_root == value.settlement.post_state_root
    assert _operational_cursor(store.path) == (
        value.finality.next_application_checkpoint_sequence,
        value.finality.next_application_checkpoint_hash,
    )
    cells = {cell.cell_key: cell for cell in store.read_cells()}
    assert cells == {row.post.cell_key: row.post for row in value.settlement.cell_transitions}
    with sqlite3.connect(store.path) as connection:
        da = connection.execute("SELECT * FROM spot_v7_operational_da").fetchone()
        finality = connection.execute("SELECT * FROM spot_v7_operational_finality").fetchone()
        assert da is not None and finality is not None
        assert bytes(da[8]) == value.data_availability.exact_blob_bytes
        assert bytes(da[9]) == value.data_availability.exact_certificate_bytes
        assert bytes(finality[12]) == value.finality.exact_certificate_bytes
        assert bytes(finality[13]) == value.finality.exact_finality_evidence_bytes
        assert tuple(da[10:13]) == (0, 0, 0)
        assert tuple(finality[14:17]) == (0, 0, 0)


def test_operational_store_rejects_bare_candidate_and_unconfigured_packet(
    tmp_path: Path,
) -> None:
    operational = _store(tmp_path)
    packet = _packet()
    before = _database_rows(operational.path)

    bare = operational._commit_test_only_sealed_candidate(
        expected_cursor=operational.read_cursor(),
        candidate=packet._candidate_for_store(),
    )

    assert bare.reject_reason is SpotV7AtomicSettlementRejectReasonV1.OPERATIONAL_POLICY_REQUIRED
    assert _database_rows(operational.path) == before

    plain_directory = tmp_path / "plain"
    plain_directory.mkdir(mode=0o700)
    plain = SQLiteSpotV7AtomicSettlementStoreV1(
        plain_directory / "spot-v7.sqlite3",
        identity=_identity(),
        genesis_cells=_initial_cells(),
    )
    unconfigured = plain._commit_test_only_operational_capability(
        expected_cursor=plain.read_cursor(),
        capability=packet,
    )
    assert unconfigured.reject_reason is (
        SpotV7AtomicSettlementRejectReasonV1.OPERATIONAL_POLICY_NOT_CONFIGURED
    )
    assert plain.read_cursor().revision == 0


def test_failure_after_operational_cursor_cas_rolls_back_every_surface(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    packet = _packet()
    before = _database_rows(store.path)

    with patch.object(
        store_module,
        "_cas_spot_v7_meta",
        side_effect=ValueError("injected after operational cursor CAS"),
    ):
        with pytest.raises(
            RuntimeError,
            match="SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED",
        ):
            store._commit_test_only_operational_capability(
                expected_cursor=store.read_cursor(),
                capability=packet,
            )

    assert _database_rows(store.path) == before
    assert _operational_cursor(store.path) == (
        _policy().genesis_application_checkpoint_sequence,
        _policy().genesis_application_checkpoint_hash,
    )
    assert _reopen(store).read_cursor().revision == 0


def test_stale_finality_cursor_is_a_typed_no_op_rejection(tmp_path: Path) -> None:
    store = _store(tmp_path)
    first = _packet()
    committed = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=first,
    )
    assert committed.committed is True
    second = _packet(
        seed=200,
        pre_state_root=first._input.settlement.post_state_root,
        values=(900, 5_100, 7_940, 85),
        input_atoms=50,
        output_atoms=30,
    )
    before = _database_rows(store.path)

    rejected = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=second,
    )

    assert rejected.reject_reason is SpotV7AtomicSettlementRejectReasonV1.FINALITY_CURSOR_MISMATCH
    assert _database_rows(store.path) == before


def test_exact_operational_retry_is_idempotent(tmp_path: Path) -> None:
    store = _store(tmp_path)
    packet = _packet()
    initial = store.read_cursor()
    committed = store._commit_test_only_operational_capability(
        expected_cursor=initial,
        capability=packet,
    )

    retried = store._commit_test_only_operational_capability(
        expected_cursor=initial,
        capability=packet,
    )

    assert committed.committed is True
    assert retried.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY
    assert retried.receipt == committed.receipt
    assert store.read_cursor().revision == 1


def test_concurrent_operational_retry_commits_one_complete_row_set(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    packet = _packet()
    cursor = store.read_cursor()
    barrier = Barrier(2)

    def submit() -> SpotV7AtomicSettlementResultV1:
        barrier.wait()
        return store._commit_test_only_operational_capability(
            expected_cursor=cursor,
            capability=packet,
        )

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = tuple(executor.map(lambda _index: submit(), range(2)))

    dispositions = tuple(result.disposition for result in results)
    assert dispositions.count(SpotV7AtomicSettlementDispositionV1.COMMITTED) == 1
    assert dispositions.count(SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY) == 1
    with sqlite3.connect(store.path) as connection:
        counts = tuple(
            int(connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0])
            for table in (
                "spot_v7_settlements",
                "spot_v7_operational_da",
                "spot_v7_operational_finality",
            )
        )
    assert counts == (1, 1, 1)
    assert store.read_cursor().revision == 1


@pytest.mark.parametrize(
    ("duplicate", "reason"),
    (
        (
            "blob",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_DA_CERTIFICATE,
        ),
        (
            "finality_evidence",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FINALITY_CERTIFICATE,
        ),
    ),
)
def test_reused_operational_identity_rejects_without_partial_rows(
    tmp_path: Path,
    duplicate: str,
    reason: SpotV7AtomicSettlementRejectReasonV1,
) -> None:
    store = _store(tmp_path)
    first = _packet()
    first_result = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=first,
    )
    assert first_result.committed is True
    first_value = first._input
    second = _packet(
        seed=200,
        pre_state_root=first_value.settlement.post_state_root,
        values=(900, 5_100, 7_940, 85),
        input_atoms=50,
        output_atoms=30,
        prior_checkpoint_sequence=first_value.finality.next_application_checkpoint_sequence,
        prior_checkpoint_hash=first_value.finality.next_application_checkpoint_hash,
        blob=(first_value.data_availability.exact_blob_bytes if duplicate == "blob" else None),
        finality_evidence=(
            first_value.finality.exact_finality_evidence_bytes
            if duplicate == "finality_evidence"
            else None
        ),
    )
    before = _database_rows(store.path)

    rejected = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=second,
    )

    assert rejected.reject_reason is reason
    assert _database_rows(store.path) == before


@pytest.mark.parametrize(
    "mutation",
    ("blob", "da_certificate", "finality_certificate"),
)
def test_exact_blob_or_certificate_mutation_cannot_reseal(
    mutation: str,
) -> None:
    packet = _packet()
    value = packet._input
    da: _TestOnlyFullBlobArtifactsV1 = value.data_availability
    finality: _TestOnlyCheckpointFinalityArtifactsV2 = value.finality
    if mutation == "blob":
        changed_da = replace(da, exact_blob_bytes=b"X" + da.exact_blob_bytes[1:])
        changed_finality = finality
    elif mutation == "da_certificate":
        changed_da = replace(
            da,
            exact_certificate_bytes=b"X" + da.exact_certificate_bytes[1:],
        )
        changed_finality = finality
    else:
        changed_da = da
        changed_finality = replace(
            finality,
            exact_certificate_bytes=b"X" + finality.exact_certificate_bytes[1:],
        )

    with pytest.raises(ValueError, match="canonical|match exact bytes"):
        _seal_test_only_spot_v7_operational_commit_v1(
            replace(
                value,
                data_availability=changed_da,
                finality=changed_finality,
            )
        )


def test_committed_operational_history_reopens_with_exact_policy(tmp_path: Path) -> None:
    store = _store(tmp_path)
    packet = _packet()
    committed = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=packet,
    )
    assert committed.committed is True

    reopened = _reopen(store)

    assert reopened.read_cursor() == committed.head_cursor
    assert _operational_cursor(reopened.path) == (
        packet._input.finality.next_application_checkpoint_sequence,
        packet._input.finality.next_application_checkpoint_hash,
    )
    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=_identity(),
            genesis_cells=_initial_cells(),
        )
    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=_identity(),
            genesis_cells=_initial_cells(),
            test_only_operational_policy=replace(
                _policy(),
                storage_policy_hash=_root(999),
            ),
        )


def test_schema_revision_one_cannot_silently_reopen_as_revision_two(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    with sqlite3.connect(store.path) as connection:
        connection.execute("PRAGMA user_version = 1")

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        _reopen(store)


@pytest.mark.parametrize("tamper", ("blob", "finality_evidence", "cursor"))
def test_reopen_rejects_operational_history_tampering(
    tmp_path: Path,
    tamper: str,
) -> None:
    store = _store(tmp_path)
    packet = _packet()
    result = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=packet,
    )
    assert result.committed is True
    with sqlite3.connect(store.path) as connection:
        if tamper == "blob":
            connection.execute(
                "UPDATE spot_v7_operational_da SET exact_blob = ?",
                (b"X" + packet._input.data_availability.exact_blob_bytes[1:],),
            )
        elif tamper == "finality_evidence":
            connection.execute(
                "UPDATE spot_v7_operational_finality SET exact_finality_evidence = ?",
                (b"X" + packet._input.finality.exact_finality_evidence_bytes[1:],),
            )
        else:
            connection.execute(
                "UPDATE spot_v7_operational_policy SET current_checkpoint_hash = ?",
                (bytes.fromhex(_root(999)[2:]),),
            )
        connection.commit()

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        _reopen(store)


def test_operational_exact_artifact_hashes_are_persisted(tmp_path: Path) -> None:
    store = _store(tmp_path)
    packet = _packet()
    value = packet._input
    result = store._commit_test_only_operational_capability(
        expected_cursor=store.read_cursor(),
        capability=packet,
    )
    assert result.committed is True
    with sqlite3.connect(store.path) as connection:
        da_hashes = connection.execute(
            "SELECT blob_sha256, certificate_sha256 FROM spot_v7_operational_da"
        ).fetchone()
        finality_hashes = connection.execute(
            "SELECT certificate_sha256, evidence_sha256 FROM spot_v7_operational_finality"
        ).fetchone()
    assert da_hashes is not None and finality_hashes is not None
    assert bytes(da_hashes[0]) == hashlib.sha256(value.data_availability.exact_blob_bytes).digest()
    assert (
        bytes(da_hashes[1])
        == hashlib.sha256(value.data_availability.exact_certificate_bytes).digest()
    )
    assert (
        bytes(finality_hashes[0]) == hashlib.sha256(value.finality.exact_certificate_bytes).digest()
    )
    assert (
        bytes(finality_hashes[1])
        == hashlib.sha256(value.finality.exact_finality_evidence_bytes).digest()
    )


def test_python_operational_hashes_and_postcard_match_exact_rust_vector() -> None:
    """Bind the Python mirror to a vector emitted by the current Rust protocol."""

    policy = _TestOnlySpotV7OperationalPolicyV1(
        application_id=_repeat_root(1),
        chain_or_domain_id=_repeat_root(2),
        data_schema_id=_repeat_root(3),
        storage_policy_hash=_repeat_root(4),
        minimum_retention_epochs=20,
        minimum_remaining_epochs=5,
        maximum_blob_bytes=1_024,
        finality_network_id=_repeat_root(6),
        finality_protocol_id=_repeat_root(7),
        external_finality_policy_hash=_repeat_root(8),
        finality_verifier_set_root=_repeat_root(9),
        genesis_application_checkpoint_sequence=41,
        genesis_application_checkpoint_hash=_repeat_root(5),
    )
    full_blob = _build_test_only_full_blob_artifacts_v1(
        policy=policy,
        epoch_id=7,
        checked_epoch=20,
        retention_through_epoch=30,
        exact_blob_bytes=b"locally present governed replay blob",
    )
    assert policy.full_blob_policy_root == (
        "0x9f75936af923bef8ddb6b217756bc11f30220cd70f99595b8c3d9302800df825"
    )
    assert full_blob.data_root == (
        "0x43f126a24dde3f2d200094c9c8805005f40eafe5b10f575c044be27a11f8468d"
    )
    assert full_blob.chunk_count == 1
    assert full_blob.chunk_root == (
        "0xa2cca633f2ade5c3350416c3ad0ff3c62a94702f2ec3ff960d90f0de82f580e5"
    )
    assert full_blob.certificate_root == (
        "0x6eda12e380d4c9a72b0f85e35bf1542622356ecccd6c273679b65b63db2594d3"
    )
    assert len(full_blob.exact_certificate_bytes) == 232
    assert hashlib.sha256(full_blob.exact_certificate_bytes).hexdigest() == (
        "fde4fa33a2afc80c8812b84de10c6cc7258b3da27b05562709d40933ef215161"
    )

    assert policy.checkpoint_finality_policy_root == (
        "0x8b03b76cc795636960966b84872beb7e83f179450608f75ae9653e332163a9a6"
    )
    finality_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=11,
        proof_journal_hash=_repeat_root(3),
        post_state_root=_repeat_root(4),
        sequence=42,
        checkpoint_hash=_repeat_root(11),
        parent_hash=_repeat_root(5),
        evidence_root=_repeat_root(10),
        policy_root=policy.checkpoint_finality_policy_root,
    )
    finality_bytes = _encode_checkpoint_finality_certificate_v2(
        policy=policy,
        epoch_id=11,
        proof_journal_hash=_repeat_root(3),
        post_state_root=_repeat_root(4),
        sequence=42,
        checkpoint_hash=_repeat_root(11),
        parent_hash=_repeat_root(5),
        evidence_root=_repeat_root(10),
        policy_root=policy.checkpoint_finality_policy_root,
        certificate_root=finality_root,
    )
    assert finality_root == ("0x1b6d5c7962859d467abe1cda70fdf4328f9c23959caf30a1866b148956d49e51")
    assert len(finality_bytes) == 419
    assert hashlib.sha256(finality_bytes).hexdigest() == (
        "a3812dbfdecfa716f73ec70eb0b8986e693851d9fa268b9c998540a2743a81fa"
    )


def test_rust_parity_vector_source_closure_is_exact() -> None:
    root = Path(__file__).resolve().parents[2]
    expected = {
        "zk/zrpf_protocol/protocol/src/full_blob_da_v1/hash.rs": (
            "848a8ac9ce34b3889e4202c73432c011c6c86a006820cb4c12c3a80bc831c534"
        ),
        "zk/zrpf_protocol/protocol/src/full_blob_da_v1/policy.rs": (
            "e2ac430291e566a33c078f6531953992a8b81b5d21a8d30f37af90f922b5f03b"
        ),
        "zk/zrpf_protocol/protocol/src/full_blob_da_v1/certificate.rs": (
            "b0a8e331ac3375e4a5feb543b7e4543561328a0945785b5f30c4c0a6af0ea769"
        ),
        "zk/zrpf_protocol/protocol/src/full_blob_da_v1/codec.rs": (
            "5400f441bcfa6f712025bec67ee7eb9ca9c38272d27f9ac977d20d9486080e91"
        ),
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/hash.rs": (
            "bdd8ebb2b634f83821aa6b54df3526b84976e3f800f4162344651caae2bd885c"
        ),
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/policy.rs": (
            "7f0d20a7eeaa55b0d0ca7c5ef2134afb5cfb00910bdffb279b07f89a6ff26e35"
        ),
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/certificate.rs": (
            "44ea322a7f4850c17e6839b727adb8d2be55732465f699cebdd2ce42d73078ee"
        ),
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/codec.rs": (
            "3b4a5f8617325be0abe0a0091ff4e7e87318f8c6cc53dba9931d37b8c11ef9b0"
        ),
        "zk/zrpf_protocol/Cargo.lock": (
            "2253f54c3046aa6dee3b1f3cd56e2b92de9731486b1abc56c360a38a8c8b37cf"
        ),
    }

    observed = {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in expected}

    assert observed == expected

    closure_paths = sorted(
        tuple((root / "zk/zrpf_protocol/protocol/src").rglob("*.rs"))
        + (
            root / "zk/zrpf_protocol/protocol/Cargo.toml",
            root / "zk/zrpf_protocol/Cargo.lock",
        ),
        key=lambda path: path.relative_to(root).as_posix(),
    )
    domain = b"zenodex.zrpf.operational_parity_source_closure.v1"
    closure = hashlib.sha256()
    closure.update(len(domain).to_bytes(2, "big"))
    closure.update(domain)
    closure.update(len(closure_paths).to_bytes(4, "big"))
    for path in closure_paths:
        relative = path.relative_to(root).as_posix().encode()
        content = path.read_bytes()
        closure.update(len(relative).to_bytes(4, "big"))
        closure.update(relative)
        closure.update(len(content).to_bytes(8, "big"))
        closure.update(content)

    assert len(closure_paths) == 123
    assert closure.hexdigest() == (
        "05e1573dab34095fffbf8470b3d3fd661578da76a00aad2cc79e7c9993adf6c2"
    )
