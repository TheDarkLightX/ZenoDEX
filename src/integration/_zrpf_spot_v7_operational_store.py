"""Combined authority-false DA/finality persistence for Spot V7 mechanics."""

from __future__ import annotations

import hashlib
import sqlite3

from src.integration._zrpf_spot_v7_operational_mechanics import (
    _derive_test_only_full_blob_artifacts_v1,
    _encode_checkpoint_finality_certificate_v2,
    _finality_certificate_root_v2,
    _TestOnlySpotV7OperationalCommitInputV1,
    _TestOnlySpotV7OperationalCommitV1,
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7AtomicSettlementStoreIdentityV1,
    _hash_bytes,
    _hex_hash,
)


def _initialize_or_validate_test_only_operational_policy(
    connection: sqlite3.Connection,
    *,
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    policy: _TestOnlySpotV7OperationalPolicyV1 | None,
) -> None:
    if not connection.in_transaction:
        raise ValueError("operational policy initialization requires a transaction")
    row = _read_policy_row(connection)
    if row is None:
        if policy is not None:
            _require_policy_scope(identity, policy)
            _insert_policy(connection, policy)
        return
    if policy is None:
        raise ValueError("operational store reopen requires its exact test-only policy")
    _require_policy_scope(identity, policy)
    if _policy_from_row(row) != policy:
        raise ValueError("operational store policy mismatch")


def _test_only_operational_policy_is_configured(connection: sqlite3.Connection) -> bool:
    return _read_policy_row(connection) is not None


def _test_only_operational_reject_reason_locked(
    connection: sqlite3.Connection,
    capability: _TestOnlySpotV7OperationalCommitV1,
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    if not _test_only_operational_policy_is_configured(connection):
        return SpotV7AtomicSettlementRejectReasonV1.OPERATIONAL_POLICY_NOT_CONFIGURED
    value = capability._input
    row = _read_policy_row(connection)
    if row is None or _policy_from_row(row) != value.policy:
        return SpotV7AtomicSettlementRejectReasonV1.OPERATIONAL_POLICY_NOT_CONFIGURED
    finality = value.finality
    prior_sequence = int.from_bytes(bytes(row["current_checkpoint_sequence_be"]), "big")
    prior_hash = _hex_hash(bytes(row["current_checkpoint_hash"]))
    if (
        finality.prior_application_checkpoint_sequence != prior_sequence
        or finality.prior_application_checkpoint_hash != prior_hash
    ):
        return SpotV7AtomicSettlementRejectReasonV1.FINALITY_CURSOR_MISMATCH
    duplicate_checks = (
        (
            "SELECT 1 FROM spot_v7_operational_da WHERE certificate_root = ?",
            value.data_availability.certificate_root,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_DA_CERTIFICATE,
        ),
        (
            "SELECT 1 FROM spot_v7_operational_da WHERE blob_sha256 = ?",
            value.data_availability.blob_sha256,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_DA_CERTIFICATE,
        ),
        (
            "SELECT 1 FROM spot_v7_operational_finality WHERE certificate_root = ?",
            finality.certificate_root,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FINALITY_CERTIFICATE,
        ),
        (
            "SELECT 1 FROM spot_v7_operational_finality WHERE finality_evidence_root = ?",
            finality.finality_evidence_root,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FINALITY_CERTIFICATE,
        ),
        (
            "SELECT 1 FROM spot_v7_operational_finality WHERE next_checkpoint_hash = ?",
            finality.next_application_checkpoint_hash,
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_APPLICATION_CHECKPOINT,
        ),
    )
    for statement, value_hash, reason in duplicate_checks:
        encoded = _hash_bytes(value_hash, name="operational duplicate identity")
        if connection.execute(statement, (encoded,)).fetchone() is not None:
            return reason
    return None


def _persist_test_only_operational_rows(
    connection: sqlite3.Connection,
    capability: _TestOnlySpotV7OperationalCommitV1,
) -> None:
    value = capability._input
    candidate = value.settlement
    commitment = _hash_bytes(candidate.settlement_commitment, name="settlement commitment")
    da = value.data_availability
    connection.execute(
        """
        INSERT INTO spot_v7_operational_da (
            settlement_commitment, certificate_root, data_root, policy_root,
            checked_epoch_be, retention_through_epoch_be, blob_sha256,
            certificate_sha256, exact_blob, exact_certificate,
            provider_retrievability_verified, settlement_authority,
            production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0)
        """,
        (
            commitment,
            _hash_bytes(da.certificate_root, name="DA certificate root"),
            _hash_bytes(da.data_root, name="DA data root"),
            _hash_bytes(da.policy_root, name="DA policy root"),
            da.checked_epoch.to_bytes(8, "big"),
            da.retention_through_epoch.to_bytes(8, "big"),
            _hash_bytes(da.blob_sha256, name="DA blob SHA-256"),
            _hash_bytes(da.certificate_sha256, name="DA certificate SHA-256"),
            da.exact_blob_bytes,
            da.exact_certificate_bytes,
        ),
    )
    finality = value.finality
    connection.execute(
        """
        INSERT INTO spot_v7_operational_finality (
            settlement_commitment, certificate_root, policy_root,
            proof_journal_hash, post_state_root, finality_evidence_root,
            prior_checkpoint_sequence_be, prior_checkpoint_hash,
            next_checkpoint_sequence_be, next_checkpoint_hash,
            certificate_sha256, evidence_sha256, exact_certificate,
            exact_finality_evidence, external_finality_authenticated,
            settlement_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0)
        """,
        (
            commitment,
            _hash_bytes(finality.certificate_root, name="finality certificate root"),
            _hash_bytes(finality.policy_root, name="finality policy root"),
            _hash_bytes(finality.proof_journal_hash, name="finality journal hash"),
            _hash_bytes(finality.post_state_root, name="finality post state"),
            _hash_bytes(finality.finality_evidence_root, name="finality evidence root"),
            finality.prior_application_checkpoint_sequence.to_bytes(8, "big"),
            _hash_bytes(finality.prior_application_checkpoint_hash, name="prior checkpoint"),
            finality.next_application_checkpoint_sequence.to_bytes(8, "big"),
            _hash_bytes(finality.next_application_checkpoint_hash, name="next checkpoint"),
            _hash_bytes(finality.certificate_sha256, name="finality certificate SHA-256"),
            _hash_bytes(finality.evidence_sha256, name="finality evidence SHA-256"),
            finality.exact_certificate_bytes,
            finality.exact_finality_evidence_bytes,
        ),
    )


def _cas_test_only_operational_cursor(
    connection: sqlite3.Connection,
    capability: _TestOnlySpotV7OperationalCommitV1,
) -> None:
    finality = capability._input.finality
    result = connection.execute(
        """
        UPDATE spot_v7_operational_policy
        SET current_checkpoint_sequence_be = ?, current_checkpoint_hash = ?
        WHERE singleton = 1
          AND current_checkpoint_sequence_be = ?
          AND current_checkpoint_hash = ?
        """,
        (
            finality.next_application_checkpoint_sequence.to_bytes(8, "big"),
            _hash_bytes(finality.next_application_checkpoint_hash, name="next checkpoint"),
            finality.prior_application_checkpoint_sequence.to_bytes(8, "big"),
            _hash_bytes(finality.prior_application_checkpoint_hash, name="prior checkpoint"),
        ),
    )
    if result.rowcount != 1:
        raise ValueError("test-only checkpoint-finality cursor compare-and-swap failed")


def _stored_test_only_operational_packet_matches(
    connection: sqlite3.Connection,
    capability: _TestOnlySpotV7OperationalCommitV1,
) -> bool:
    commitment = _hash_bytes(
        capability._input.settlement.settlement_commitment,
        name="settlement commitment",
    )
    da = connection.execute(
        "SELECT * FROM spot_v7_operational_da WHERE settlement_commitment = ?",
        (commitment,),
    ).fetchone()
    finality = connection.execute(
        "SELECT * FROM spot_v7_operational_finality WHERE settlement_commitment = ?",
        (commitment,),
    ).fetchone()
    if da is None or finality is None:
        return False
    value = capability._input
    return _da_row_matches(da, value) and _finality_row_matches(finality, value)


def _validate_complete_test_only_operational_history(
    connection: sqlite3.Connection,
) -> None:
    policy_row = _read_policy_row(connection)
    revision = int(
        connection.execute(
            "SELECT revision FROM spot_v7_store_meta WHERE singleton = 1"
        ).fetchone()[0]
    )
    da_count = int(connection.execute("SELECT count(*) FROM spot_v7_operational_da").fetchone()[0])
    finality_count = int(
        connection.execute("SELECT count(*) FROM spot_v7_operational_finality").fetchone()[0]
    )
    if policy_row is None:
        if da_count != 0 or finality_count != 0:
            raise ValueError("operational rows exist without configured policy")
        return
    if da_count != revision or finality_count != revision:
        raise ValueError("operational row counts do not match settlement revision")
    policy = _policy_from_row(policy_row)
    _validate_policy_row_roots(policy_row, policy)
    sequence = policy.genesis_application_checkpoint_sequence
    checkpoint_hash = policy.genesis_application_checkpoint_hash
    settlements = connection.execute(
        "SELECT * FROM spot_v7_settlements ORDER BY revision"
    ).fetchall()
    for settlement in settlements:
        commitment = bytes(settlement["settlement_commitment"])
        da = connection.execute(
            "SELECT * FROM spot_v7_operational_da WHERE settlement_commitment = ?",
            (commitment,),
        ).fetchone()
        finality = connection.execute(
            "SELECT * FROM spot_v7_operational_finality WHERE settlement_commitment = ?",
            (commitment,),
        ).fetchone()
        if da is None or finality is None:
            raise ValueError("operational settlement rows are incomplete")
        _validate_operational_row(
            settlement,
            da,
            finality,
            policy,
            sequence,
            checkpoint_hash,
        )
        sequence = int.from_bytes(bytes(finality["next_checkpoint_sequence_be"]), "big")
        checkpoint_hash = _hex_hash(bytes(finality["next_checkpoint_hash"]))
    if sequence != int.from_bytes(bytes(policy_row["current_checkpoint_sequence_be"]), "big"):
        raise ValueError("operational checkpoint sequence disagrees with history")
    if checkpoint_hash != _hex_hash(bytes(policy_row["current_checkpoint_hash"])):
        raise ValueError("operational checkpoint hash disagrees with history")


def _validate_operational_row(
    settlement: sqlite3.Row,
    da_row: sqlite3.Row,
    finality_row: sqlite3.Row,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    prior_sequence: int,
    prior_hash: str,
) -> None:
    epoch = int.from_bytes(bytes(settlement["epoch_id_be"]), "big")
    da = _derive_test_only_full_blob_artifacts_v1(
        policy=policy,
        epoch_id=epoch,
        checked_epoch=int.from_bytes(bytes(da_row["checked_epoch_be"]), "big"),
        retention_through_epoch=int.from_bytes(
            bytes(da_row["retention_through_epoch_be"]), "big"
        ),
        exact_blob_bytes=bytes(da_row["exact_blob"]),
        exact_certificate_bytes=bytes(da_row["exact_certificate"]),
    )
    if da.certificate_root != _hex_hash(bytes(da_row["certificate_root"])):
        raise ValueError("stored operational DA certificate root mismatch")
    if da.data_root != _hex_hash(bytes(da_row["data_root"])):
        raise ValueError("stored operational DA data root mismatch")
    if da.policy_root != _hex_hash(bytes(da_row["policy_root"])):
        raise ValueError("stored operational DA policy root mismatch")
    if da.certificate_root != _hex_hash(bytes(settlement["data_availability_certificate_root"])):
        raise ValueError("stored operational DA settlement certificate mismatch")
    if da.data_root != _hex_hash(bytes(settlement["data_root"])):
        raise ValueError("stored operational DA settlement data root mismatch")
    _require_zero_authority(da_row, ("provider_retrievability_verified",))
    if bytes(da_row["blob_sha256"]) != hashlib.sha256(bytes(da_row["exact_blob"])).digest():
        raise ValueError("stored operational blob SHA-256 mismatch")
    if bytes(da_row["certificate_sha256"]) != hashlib.sha256(
        bytes(da_row["exact_certificate"])
    ).digest():
        raise ValueError("stored operational DA certificate SHA-256 mismatch")
    _validate_finality_row(
        settlement,
        finality_row,
        policy,
        epoch,
        prior_sequence,
        prior_hash,
    )


def _validate_finality_row(
    settlement: sqlite3.Row,
    row: sqlite3.Row,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch: int,
    prior_sequence: int,
    prior_hash: str,
) -> None:
    observed_prior = int.from_bytes(bytes(row["prior_checkpoint_sequence_be"]), "big")
    observed_prior_hash = _hex_hash(bytes(row["prior_checkpoint_hash"]))
    next_sequence = int.from_bytes(bytes(row["next_checkpoint_sequence_be"]), "big")
    if observed_prior != prior_sequence or observed_prior_hash != prior_hash:
        raise ValueError("stored operational finality cursor continuity mismatch")
    if next_sequence != prior_sequence + 1:
        raise ValueError("stored operational finality sequence is not an exact successor")
    journal_hash = _hex_hash(bytes(row["proof_journal_hash"]))
    post_state_root = _hex_hash(bytes(row["post_state_root"]))
    if journal_hash != _hex_hash(bytes(settlement["journal_sha256"])):
        raise ValueError("stored operational finality journal mismatch")
    if post_state_root != _hex_hash(bytes(settlement["result_state_root"])):
        raise ValueError("stored operational finality post-state mismatch")
    evidence = bytes(row["exact_finality_evidence"])
    evidence_root = _hex_hash(bytes(row["finality_evidence_root"]))
    if _hex_hash(hashlib.sha256(evidence).digest()) != evidence_root:
        raise ValueError("stored operational finality evidence root mismatch")
    expected_certificate_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=epoch,
        proof_journal_hash=journal_hash,
        post_state_root=post_state_root,
        sequence=next_sequence,
        checkpoint_hash=_hex_hash(bytes(row["next_checkpoint_hash"])),
        parent_hash=prior_hash,
        evidence_root=evidence_root,
        policy_root=policy.checkpoint_finality_policy_root,
    )
    if expected_certificate_root != _hex_hash(bytes(row["certificate_root"])):
        raise ValueError("stored operational finality certificate root mismatch")
    if _hex_hash(bytes(row["policy_root"])) != policy.checkpoint_finality_policy_root:
        raise ValueError("stored operational finality policy root mismatch")
    if bytes(row["certificate_sha256"]) != hashlib.sha256(
        bytes(row["exact_certificate"])
    ).digest():
        raise ValueError("stored operational finality certificate SHA-256 mismatch")
    expected_certificate = _encode_checkpoint_finality_certificate_v2(
        policy=policy,
        epoch_id=epoch,
        proof_journal_hash=journal_hash,
        post_state_root=post_state_root,
        sequence=next_sequence,
        checkpoint_hash=_hex_hash(bytes(row["next_checkpoint_hash"])),
        parent_hash=prior_hash,
        evidence_root=evidence_root,
        policy_root=policy.checkpoint_finality_policy_root,
        certificate_root=expected_certificate_root,
    )
    if bytes(row["exact_certificate"]) != expected_certificate:
        raise ValueError("stored operational finality certificate is not canonical")
    if bytes(row["evidence_sha256"]) != hashlib.sha256(evidence).digest():
        raise ValueError("stored operational finality evidence SHA-256 mismatch")
    _require_zero_authority(row, ("external_finality_authenticated",))


def _insert_policy(
    connection: sqlite3.Connection,
    policy: _TestOnlySpotV7OperationalPolicyV1,
) -> None:
    connection.execute(
        """
        INSERT INTO spot_v7_operational_policy (
            singleton, application_id, chain_or_domain_id, data_schema_id,
            storage_policy_hash, minimum_retention_epochs_be,
            minimum_remaining_epochs_be, maximum_blob_bytes,
            full_blob_policy_root, finality_network_id, finality_protocol_id,
            external_finality_policy_hash, finality_verifier_set_root,
            checkpoint_finality_policy_root, genesis_checkpoint_sequence_be,
            genesis_checkpoint_hash, current_checkpoint_sequence_be,
            current_checkpoint_hash, settlement_authority, production_authority
        ) VALUES (1, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0)
        """,
        _policy_storage_values(policy),
    )


def _policy_storage_values(policy: _TestOnlySpotV7OperationalPolicyV1) -> tuple[object, ...]:
    return (
        _hash_bytes(policy.application_id, name="policy application"),
        _hash_bytes(policy.chain_or_domain_id, name="policy domain"),
        _hash_bytes(policy.data_schema_id, name="policy data schema"),
        _hash_bytes(policy.storage_policy_hash, name="policy storage hash"),
        policy.minimum_retention_epochs.to_bytes(8, "big"),
        policy.minimum_remaining_epochs.to_bytes(8, "big"),
        policy.maximum_blob_bytes,
        _hash_bytes(policy.full_blob_policy_root, name="full-blob policy root"),
        _hash_bytes(policy.finality_network_id, name="finality network"),
        _hash_bytes(policy.finality_protocol_id, name="finality protocol"),
        _hash_bytes(policy.external_finality_policy_hash, name="external policy"),
        _hash_bytes(policy.finality_verifier_set_root, name="verifier set"),
        _hash_bytes(
            policy.checkpoint_finality_policy_root,
            name="checkpoint finality policy root",
        ),
        policy.genesis_application_checkpoint_sequence.to_bytes(8, "big"),
        _hash_bytes(policy.genesis_application_checkpoint_hash, name="genesis checkpoint"),
        policy.genesis_application_checkpoint_sequence.to_bytes(8, "big"),
        _hash_bytes(policy.genesis_application_checkpoint_hash, name="current checkpoint"),
    )


def _policy_from_row(row: sqlite3.Row) -> _TestOnlySpotV7OperationalPolicyV1:
    return _TestOnlySpotV7OperationalPolicyV1(
        application_id=_hex_hash(bytes(row["application_id"])),
        chain_or_domain_id=_hex_hash(bytes(row["chain_or_domain_id"])),
        data_schema_id=_hex_hash(bytes(row["data_schema_id"])),
        storage_policy_hash=_hex_hash(bytes(row["storage_policy_hash"])),
        minimum_retention_epochs=int.from_bytes(
            bytes(row["minimum_retention_epochs_be"]), "big"
        ),
        minimum_remaining_epochs=int.from_bytes(
            bytes(row["minimum_remaining_epochs_be"]), "big"
        ),
        maximum_blob_bytes=int(row["maximum_blob_bytes"]),
        finality_network_id=_hex_hash(bytes(row["finality_network_id"])),
        finality_protocol_id=_hex_hash(bytes(row["finality_protocol_id"])),
        external_finality_policy_hash=_hex_hash(
            bytes(row["external_finality_policy_hash"])
        ),
        finality_verifier_set_root=_hex_hash(bytes(row["finality_verifier_set_root"])),
        genesis_application_checkpoint_sequence=int.from_bytes(
            bytes(row["genesis_checkpoint_sequence_be"]), "big"
        ),
        genesis_application_checkpoint_hash=_hex_hash(bytes(row["genesis_checkpoint_hash"])),
    )


def _read_policy_row(connection: sqlite3.Connection) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM spot_v7_operational_policy WHERE singleton = 1"
    ).fetchone()


def _require_policy_scope(
    identity: SpotV7AtomicSettlementStoreIdentityV1,
    policy: _TestOnlySpotV7OperationalPolicyV1,
) -> None:
    if (
        policy.application_id != identity.application_id
        or policy.chain_or_domain_id != identity.chain_or_domain_id
    ):
        raise ValueError("test-only operational policy does not match store scope")


def _validate_policy_row_roots(
    row: sqlite3.Row,
    policy: _TestOnlySpotV7OperationalPolicyV1,
) -> None:
    if _hex_hash(bytes(row["full_blob_policy_root"])) != policy.full_blob_policy_root:
        raise ValueError("stored full-blob policy root mismatch")
    if (
        _hex_hash(bytes(row["checkpoint_finality_policy_root"]))
        != policy.checkpoint_finality_policy_root
    ):
        raise ValueError("stored checkpoint-finality policy root mismatch")
    _require_zero_authority(row)


def _require_zero_authority(
    row: sqlite3.Row,
    extra_fields: tuple[str, ...] = (),
) -> None:
    fields = ("settlement_authority", "production_authority", *extra_fields)
    if any(int(row[field]) != 0 for field in fields):
        raise ValueError("operational authority non-claim mismatch")


def _da_row_matches(
    row: sqlite3.Row,
    value: _TestOnlySpotV7OperationalCommitInputV1,
) -> bool:
    da = value.data_availability
    return all(
        (
            _hex_hash(bytes(row["certificate_root"])) == da.certificate_root,
            _hex_hash(bytes(row["data_root"])) == da.data_root,
            _hex_hash(bytes(row["policy_root"])) == da.policy_root,
            int.from_bytes(bytes(row["checked_epoch_be"]), "big") == da.checked_epoch,
            int.from_bytes(bytes(row["retention_through_epoch_be"]), "big")
            == da.retention_through_epoch,
            _hex_hash(bytes(row["blob_sha256"])) == da.blob_sha256,
            _hex_hash(bytes(row["certificate_sha256"])) == da.certificate_sha256,
            bytes(row["exact_blob"]) == da.exact_blob_bytes,
            bytes(row["exact_certificate"]) == da.exact_certificate_bytes,
        )
    )


def _finality_row_matches(
    row: sqlite3.Row,
    value: _TestOnlySpotV7OperationalCommitInputV1,
) -> bool:
    finality = value.finality
    return all(
        (
            _hex_hash(bytes(row["certificate_root"])) == finality.certificate_root,
            _hex_hash(bytes(row["policy_root"])) == finality.policy_root,
            _hex_hash(bytes(row["finality_evidence_root"]))
            == finality.finality_evidence_root,
            _hex_hash(bytes(row["proof_journal_hash"]))
            == finality.proof_journal_hash,
            _hex_hash(bytes(row["post_state_root"])) == finality.post_state_root,
            int.from_bytes(bytes(row["prior_checkpoint_sequence_be"]), "big")
            == finality.prior_application_checkpoint_sequence,
            _hex_hash(bytes(row["prior_checkpoint_hash"]))
            == finality.prior_application_checkpoint_hash,
            int.from_bytes(bytes(row["next_checkpoint_sequence_be"]), "big")
            == finality.next_application_checkpoint_sequence,
            _hex_hash(bytes(row["next_checkpoint_hash"]))
            == finality.next_application_checkpoint_hash,
            _hex_hash(bytes(row["certificate_sha256"]))
            == finality.certificate_sha256,
            _hex_hash(bytes(row["evidence_sha256"])) == finality.evidence_sha256,
            bytes(row["exact_certificate"]) == finality.exact_certificate_bytes,
            bytes(row["exact_finality_evidence"])
            == finality.exact_finality_evidence_bytes,
        )
    )


__all__: list[str] = []
