"""Exact V4 operational rows for authority-neutral Spot V7 commits."""

from __future__ import annotations

import sqlite3

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
)
from src.integration._zrpf_spot_v7_operational_capability_v3 import (
    _SpotV7OperationalCommitPacketV3,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementRejectReasonV1,
    _hash_bytes,
    _root_bytes_allow_zero,
)


def _operational_v4_reject_reason_locked(
    connection: sqlite3.Connection,
    packet: _SpotV7OperationalCommitPacketV3,
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    finality = packet.finality
    policy_row = connection.execute(
        "SELECT current_checkpoint_sequence_be, current_checkpoint_hash "
        "FROM spot_v7_operational_policy_v4 WHERE singleton = 1"
    ).fetchone()
    if policy_row is None:
        return SpotV7AtomicSettlementRejectReasonV1.OPERATIONAL_POLICY_NOT_CONFIGURED
    if int.from_bytes(
        bytes(policy_row["current_checkpoint_sequence_be"]), "big"
    ) != finality.prior_application_checkpoint_sequence or bytes(
        policy_row["current_checkpoint_hash"]
    ) != _root_bytes_allow_zero(
        finality.prior_application_checkpoint_hash,
        name="V4 prior checkpoint hash",
    ):
        return SpotV7AtomicSettlementRejectReasonV1.FINALITY_CURSOR_MISMATCH
    duplicate_checks = (
        (
            "SELECT 1 FROM spot_v7_operational_da_v4 WHERE certificate_root = ?",
            packet.data_availability.base.certificate_root,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_DA_CERTIFICATE,
        ),
        (
            "SELECT 1 FROM spot_v7_operational_finality_v4 WHERE certificate_root = ?",
            finality.certificate_root,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FINALITY_CERTIFICATE,
        ),
        (
            "SELECT 1 FROM spot_v7_operational_finality_v4 WHERE next_checkpoint_hash = ?",
            finality.next_application_checkpoint_hash,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_APPLICATION_CHECKPOINT,
        ),
    )
    for statement, value, reason in duplicate_checks:
        if (
            connection.execute(
                statement,
                (_hash_bytes(value, name="V4 duplicate identity"),),
            ).fetchone()
            is not None
        ):
            return reason
    return None


def _persist_operational_packet_v4(
    connection: sqlite3.Connection,
    packet: _SpotV7OperationalCommitPacketV3,
) -> None:
    commitment = _hash_bytes(
        _derive_capability_commitment(packet.candidate),
        name="V4 settlement commitment",
    )
    _insert_da_row(connection, commitment, packet)
    _insert_finality_row(connection, commitment, packet)
    _insert_replay_row(connection, commitment, packet)


def _insert_da_row(
    connection: sqlite3.Connection,
    commitment: bytes,
    packet: _SpotV7OperationalCommitPacketV3,
) -> None:
    value = packet.data_availability
    base = value.base
    connection.execute(
        """
        INSERT INTO spot_v7_operational_da_v4 (
            settlement_commitment, certificate_root, data_root, chunk_root,
            full_blob_policy_root, sampled_policy_root, checked_epoch_be,
            retention_through_epoch_be, exact_blob_sha256,
            sampled_evidence_sha256, accepted_provider_set_root,
            beacon_commitment, source_network_id, source_protocol_id,
            source_epoch_lag_be, source_checkpoint_sequence_be,
            source_checkpoint_hash, source_finality_certificate_root,
            source_finality_policy_root, source_finality_evidence_root,
            exact_full_blob, exact_full_blob_certificate,
            exact_sampled_evidence, exact_source_finality_certificate,
            exact_source_finality_evidence, exact_content_verified,
            sampled_policy_governance_verified,
            governed_beacon_provenance_verified,
            public_future_availability_verified, settlement_authority,
            production_authority
        ) VALUES (
            ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
            ?, ?, ?, ?, ?, 1, 1, 1, 0, 0, 0
        )
        """,
        (
            commitment,
            _hash_bytes(base.certificate_root, name="V4 DA certificate root"),
            _hash_bytes(base.data_root, name="V4 DA data root"),
            _hash_bytes(base.chunk_root, name="V4 DA chunk root"),
            _hash_bytes(base.full_blob_policy_root, name="V4 full-blob policy"),
            _hash_bytes(base.sampled_policy_root, name="V4 sampled policy"),
            base.checked_epoch.to_bytes(8, "big"),
            base.retention_through_epoch.to_bytes(8, "big"),
            _hash_bytes(base.exact_blob_sha256, name="V4 exact blob SHA-256"),
            bytes.fromhex(base.sampled_evidence_sha256),
            _root_bytes_allow_zero(
                base.accepted_provider_set_root,
                name="V4 accepted provider set",
            ),
            _hash_bytes(base.beacon_commitment, name="V4 beacon commitment"),
            _hash_bytes(value.source_network_id, name="V4 source network"),
            _hash_bytes(value.source_protocol_id, name="V4 source protocol"),
            value.source_epoch_lag.to_bytes(8, "big"),
            value.source_checkpoint_sequence.to_bytes(8, "big"),
            _hash_bytes(value.source_checkpoint_hash, name="V4 source checkpoint"),
            _hash_bytes(
                value.source_finality_certificate_root,
                name="V4 source finality certificate",
            ),
            _hash_bytes(
                value.source_finality_policy_root,
                name="V4 source finality policy",
            ),
            _hash_bytes(
                value.source_finality_evidence_root,
                name="V4 source finality evidence",
            ),
            packet.exact_full_blob_bytes,
            packet.exact_full_blob_certificate_bytes,
            packet.exact_sampled_evidence_bytes,
            packet.exact_source_finality_certificate_bytes,
            packet.exact_source_finality_evidence_bytes,
        ),
    )


def _insert_finality_row(
    connection: sqlite3.Connection,
    commitment: bytes,
    packet: _SpotV7OperationalCommitPacketV3,
) -> None:
    value = packet.finality
    connection.execute(
        """
        INSERT INTO spot_v7_operational_finality_v4 (
            settlement_commitment, certificate_root, policy_root,
            proof_journal_hash, post_state_root, finality_evidence_root,
            prior_checkpoint_sequence_be, prior_checkpoint_hash,
            next_checkpoint_sequence_be, next_checkpoint_hash,
            exact_certificate, exact_finality_evidence,
            cryptographic_checkpoint_quorum_authenticated,
            proof_receipt_authentication_established,
            settlement_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 0, 0, 0)
        """,
        (
            commitment,
            _hash_bytes(value.certificate_root, name="V4 finality certificate"),
            _hash_bytes(value.policy_root, name="V4 finality policy"),
            _hash_bytes(value.proof_journal_hash, name="V4 finality journal"),
            _hash_bytes(value.post_state_root, name="V4 finality post-state"),
            _hash_bytes(value.finality_evidence_root, name="V4 finality evidence"),
            value.prior_application_checkpoint_sequence.to_bytes(8, "big"),
            _root_bytes_allow_zero(
                value.prior_application_checkpoint_hash,
                name="V4 prior checkpoint",
            ),
            value.next_application_checkpoint_sequence.to_bytes(8, "big"),
            _hash_bytes(
                value.next_application_checkpoint_hash,
                name="V4 next checkpoint",
            ),
            packet.exact_finality_certificate_bytes,
            packet.exact_finality_evidence_bytes,
        ),
    )


def _insert_replay_row(
    connection: sqlite3.Connection,
    commitment: bytes,
    packet: _SpotV7OperationalCommitPacketV3,
) -> None:
    projection = packet.durable_replay_packet._projection_for_history_reverification()
    value = packet.persisted_replay_inputs
    connection.execute(
        """
        INSERT INTO spot_v7_settlement_replay_v4 (
            settlement_commitment, replay_material_root, exact_projection,
            exact_header, exact_body, exact_envelope, exact_receipt,
            exact_evidence, exact_config_document, exact_pre_state_snapshot,
            exact_parent_header, replay_reverified_before_commit,
            proof_receipt_authentication_established, release_authority,
            settlement_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 0, 0, 0, 0)
        """,
        (
            commitment,
            _hash_bytes(projection.replay_material_root, name="V4 replay material"),
            value.exact_projection_bytes,
            value.exact_header_bytes,
            value.exact_body_bytes,
            value.exact_envelope_bytes,
            value.exact_receipt_bytes,
            value.exact_evidence_bytes,
            value.exact_config_document_bytes,
            value.exact_pre_state_snapshot_bytes,
            packet.exact_parent_header_bytes,
        ),
    )


def _cas_operational_cursor_v4(
    connection: sqlite3.Connection,
    packet: _SpotV7OperationalCommitPacketV3,
) -> None:
    value = packet.finality
    result = connection.execute(
        """
        UPDATE spot_v7_operational_policy_v4
        SET current_checkpoint_sequence_be = ?, current_checkpoint_hash = ?
        WHERE singleton = 1
          AND current_checkpoint_sequence_be = ?
          AND current_checkpoint_hash = ?
        """,
        (
            value.next_application_checkpoint_sequence.to_bytes(8, "big"),
            _hash_bytes(value.next_application_checkpoint_hash, name="V4 next checkpoint"),
            value.prior_application_checkpoint_sequence.to_bytes(8, "big"),
            _root_bytes_allow_zero(
                value.prior_application_checkpoint_hash,
                name="V4 prior checkpoint",
            ),
        ),
    )
    if result.rowcount != 1:
        raise ValueError("Spot V7 V4 operational cursor compare-and-swap failed")


def _stored_operational_packet_matches_v4(
    connection: sqlite3.Connection,
    packet: _SpotV7OperationalCommitPacketV3,
) -> bool:
    commitment = _hash_bytes(
        _derive_capability_commitment(packet.candidate),
        name="V4 stored settlement commitment",
    )
    rows = (
        connection.execute(
            "SELECT * FROM spot_v7_operational_da_v4 WHERE settlement_commitment = ?",
            (commitment,),
        ).fetchone(),
        connection.execute(
            "SELECT * FROM spot_v7_operational_finality_v4 WHERE settlement_commitment = ?",
            (commitment,),
        ).fetchone(),
        connection.execute(
            "SELECT * FROM spot_v7_settlement_replay_v4 WHERE settlement_commitment = ?",
            (commitment,),
        ).fetchone(),
    )
    da_row, finality_row, replay_row = rows
    if da_row is None or finality_row is None or replay_row is None:
        return False
    base = packet.data_availability.base
    finality = packet.finality
    replay = packet.persisted_replay_inputs
    replay_projection = packet.durable_replay_packet._projection_for_history_reverification()
    return all(
        (
            bytes(da_row["exact_full_blob"]) == packet.exact_full_blob_bytes,
            bytes(da_row["exact_full_blob_certificate"])
            == packet.exact_full_blob_certificate_bytes,
            bytes(da_row["exact_sampled_evidence"]) == packet.exact_sampled_evidence_bytes,
            bytes(da_row["exact_source_finality_certificate"])
            == packet.exact_source_finality_certificate_bytes,
            bytes(da_row["exact_source_finality_evidence"])
            == packet.exact_source_finality_evidence_bytes,
            bytes(da_row["certificate_root"])
            == _hash_bytes(base.certificate_root, name="V4 DA certificate"),
            bytes(finality_row["exact_certificate"]) == packet.exact_finality_certificate_bytes,
            bytes(finality_row["exact_finality_evidence"]) == packet.exact_finality_evidence_bytes,
            bytes(finality_row["certificate_root"])
            == _hash_bytes(finality.certificate_root, name="V4 finality certificate"),
            bytes(replay_row["replay_material_root"])
            == _hash_bytes(replay_projection.replay_material_root, name="V4 replay root"),
            bytes(replay_row["exact_projection"]) == replay.exact_projection_bytes,
            bytes(replay_row["exact_header"]) == replay.exact_header_bytes,
            bytes(replay_row["exact_body"]) == replay.exact_body_bytes,
            bytes(replay_row["exact_envelope"]) == replay.exact_envelope_bytes,
            bytes(replay_row["exact_receipt"]) == replay.exact_receipt_bytes,
            bytes(replay_row["exact_evidence"]) == replay.exact_evidence_bytes,
            bytes(replay_row["exact_config_document"]) == replay.exact_config_document_bytes,
            bytes(replay_row["exact_pre_state_snapshot"]) == replay.exact_pre_state_snapshot_bytes,
            (
                None
                if replay_row["exact_parent_header"] is None
                else bytes(replay_row["exact_parent_header"])
            )
            == packet.exact_parent_header_bytes,
        )
    )


__all__ = ()
