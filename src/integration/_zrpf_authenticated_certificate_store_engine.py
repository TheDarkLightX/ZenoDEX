"""Row mechanics for authenticated settlement certificates."""

from __future__ import annotations

import hashlib
import sqlite3

from src.core._zrpf_settlement_certificate_authority import (
    SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,
    _AuthenticatedSettlementCertificateV1,
)
from src.integration.recursive_stark_admission_store_types import _hash_bytes, _hex_hash
from src.integration.zrpf_atomic_settlement_store_types import (
    DurableAuthenticatedSettlementCertificateReceiptV1,
    DurableZrpfSettlementCursorV1,
    ZrpfAtomicSettlementRejectReasonV1,
    ZrpfAtomicSettlementStoreErrorV1,
)

_ACTION_LIST_DOMAIN = b"zenodex.zrpf.persisted_action_nullifier_list.v1"
_CONSUMED_LIST_DOMAIN = b"zenodex.zrpf.persisted_consumed_object_list.v1"
_GRANT_LIST_DOMAIN = b"zenodex.zrpf.persisted_grant_spend_list.v1"

_CERTIFICATE_INSERT_SQL = """
    INSERT INTO zrpf_settlement_certificates (
        certificate_journal_hash, semantic_root_journal_hash, plan_commitment,
        settlement_revision, certificate_version, epoch_id_be,
        settlement_receipt_id, semantic_claim_hash, settlement_claim_hash,
        settlement_image_id, settlement_profile_id, settlement_manifest_sha256,
        application_id, chain_or_domain_id, public_policy_hash,
        pre_state_root, post_state_root, economic_action_ids_root,
        ledger_cell_writes_root, asset_effects_root,
        action_authorization_bindings_root, action_nullifier_list_sha256,
        authorization_grant_spend_nullifiers_root,
        authorization_grant_spend_list_sha256, consumed_object_ids_root,
        consumed_object_id_list_sha256, message_effects_root,
        carry_effects_root, reward_effects_root, effect_plan_commitment,
        canonical_certificate_sha256, canonical_certificate,
        exact_effect_plan_sha256, exact_effect_plan,
        authority_manifest_sha256, admission_policy_binding_sha256,
        verifier_executable_sha256, verification_request_sha256,
        settlement_authority, authority_blocked_reason
    ) VALUES (
        ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
        ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, ?
    )
"""


def _read_certificate_row_by_semantic_root(
    connection: sqlite3.Connection,
    *,
    semantic_root_journal_hash: str,
) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM zrpf_settlement_certificates WHERE semantic_root_journal_hash = ?",
        (_hash_bytes(semantic_root_journal_hash, name="semantic root journal hash"),),
    ).fetchone()


def _authenticated_certificate_idempotent_match(
    connection: sqlite3.Connection,
    authenticated: _AuthenticatedSettlementCertificateV1,
) -> bool:
    row = _read_certificate_row_by_semantic_root(
        connection,
        semantic_root_journal_hash=(
            authenticated.certificate.semantic_root_journal_hash
        ),
    )
    if row is None:
        return False
    certificate = authenticated.certificate
    provenance = authenticated.provenance
    expected_hashes = {
        "certificate_journal_hash": certificate.certificate_journal_hash,
        "semantic_root_journal_hash": certificate.semantic_root_journal_hash,
        "plan_commitment": authenticated.plan.commitment,
        "settlement_receipt_id": certificate.settlement_receipt_id,
        "semantic_claim_hash": certificate.semantic_claim_hash,
        "settlement_claim_hash": certificate.settlement_claim_hash,
        "settlement_image_id": certificate.settlement_image_id,
        "application_id": certificate.application_id,
        "chain_or_domain_id": certificate.chain_or_domain_id,
        "public_policy_hash": certificate.public_policy_hash,
        "pre_state_root": certificate.pre_state_root,
        "post_state_root": certificate.post_state_root,
        "economic_action_ids_root": certificate.economic_action_ids_root,
        "ledger_cell_writes_root": certificate.ledger_cell_writes_root,
        "asset_effects_root": certificate.asset_effects_root,
        "action_authorization_bindings_root": (
            certificate.action_authorization_bindings_root
        ),
        "authorization_grant_spend_nullifiers_root": (
            certificate.authorization_grant_spend_nullifiers_root
        ),
        "consumed_object_ids_root": certificate.consumed_object_ids_root,
        "message_effects_root": certificate.message_effects_root,
        "carry_effects_root": certificate.carry_effects_root,
        "reward_effects_root": certificate.reward_effects_root,
        "effect_plan_commitment": certificate.effect_plan_commitment,
    }
    for column, value in expected_hashes.items():
        if bytes(row[column]) != _hash_bytes(value, name=f"certificate {column}"):
            return False
    expected_bare_hashes = {
        "settlement_manifest_sha256": certificate.settlement_manifest_sha256,
        "canonical_certificate_sha256": certificate.canonical_certificate_sha256,
        "exact_effect_plan_sha256": certificate.exact_effect_plan_sha256,
        "authority_manifest_sha256": provenance.authority_manifest_sha256,
        "admission_policy_binding_sha256": provenance.admission_policy_binding_sha256,
        "verifier_executable_sha256": provenance.verifier_executable_sha256,
        "verification_request_sha256": provenance.verification_request_sha256,
    }
    for column, value in expected_bare_hashes.items():
        if bytes(row[column]) != bytes.fromhex(value):
            return False
    if (
        int(row["certificate_version"]) != certificate.certificate_version
        or bytes(row["epoch_id_be"]) != certificate.epoch_id.to_bytes(8, "big")
        or str(row["settlement_profile_id"]) != certificate.settlement_profile_id
        or bytes(row["canonical_certificate"]) != certificate.canonical_certificate
        or bytes(row["exact_effect_plan"]) != certificate.exact_effect_plan
        or int(row["settlement_authority"]) != 0
        or str(row["authority_blocked_reason"])
        != SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1
    ):
        return False
    return (
        _read_identifier_sequence(
            connection,
            table="zrpf_settlement_action_nullifiers",
            column="action_nullifier",
            certificate_journal_hash=certificate.certificate_journal_hash,
        )
        == certificate.action_nullifiers
        and _read_identifier_sequence(
            connection,
            table="zrpf_settlement_consumed_objects",
            column="consumed_object_id",
            certificate_journal_hash=certificate.certificate_journal_hash,
        )
        == certificate.consumed_object_ids
    )


def _certificate_reject_reason_locked(
    connection: sqlite3.Connection,
    authenticated: _AuthenticatedSettlementCertificateV1,
) -> ZrpfAtomicSettlementRejectReasonV1 | None:
    certificate = authenticated.certificate
    previous = connection.execute(
        "SELECT epoch_id_be FROM zrpf_settlement_plans ORDER BY settlement_revision DESC LIMIT 1"
    ).fetchone()
    if previous is not None and certificate.epoch_id <= int.from_bytes(
        bytes(previous["epoch_id_be"]),
        "big",
    ):
        return ZrpfAtomicSettlementRejectReasonV1.EPOCH_NOT_MONOTONIC
    _stage_incoming_certificate_ids(connection, authenticated)
    overlap_specs = (
        (
            1,
            "zrpf_settlement_action_nullifiers",
            "action_nullifier",
            ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_ACTION_NULLIFIER,
        ),
        (
            2,
            "zrpf_settlement_consumed_objects",
            "consumed_object_id",
            ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_CONSUMED_OBJECT,
        ),
    )
    for kind, table, column, reason in overlap_specs:
        found = connection.execute(
            f"""
            SELECT 1 FROM temp.zrpf_settlement_incoming_certificate_ids AS incoming
            JOIN {table} AS stored ON stored.{column} = incoming.identifier
            WHERE incoming.kind = ? LIMIT 1
            """,
            (kind,),
        ).fetchone()
        if found is not None:
            return reason
    return None


def _stage_incoming_certificate_ids(
    connection: sqlite3.Connection,
    authenticated: _AuthenticatedSettlementCertificateV1,
) -> None:
    connection.execute(
        "CREATE TEMP TABLE IF NOT EXISTS zrpf_settlement_incoming_certificate_ids "
        "(kind INTEGER NOT NULL, identifier BLOB NOT NULL, PRIMARY KEY (kind, identifier)) "
        "WITHOUT ROWID"
    )
    connection.execute("DELETE FROM temp.zrpf_settlement_incoming_certificate_ids")
    certificate = authenticated.certificate
    rows = [
        *(
            (1, _hash_bytes(value, name="action nullifier"))
            for value in certificate.action_nullifiers
        ),
        *(
            (2, _hash_bytes(value, name="consumed object ID"))
            for value in certificate.consumed_object_ids
        ),
    ]
    connection.executemany(
        "INSERT INTO temp.zrpf_settlement_incoming_certificate_ids "
        "(kind, identifier) VALUES (?, ?)",
        rows,
    )


def _persist_authenticated_certificate(
    connection: sqlite3.Connection,
    authenticated: _AuthenticatedSettlementCertificateV1,
    next_cursor: DurableZrpfSettlementCursorV1,
) -> None:
    certificate = authenticated.certificate
    provenance = authenticated.provenance
    connection.execute(
        _CERTIFICATE_INSERT_SQL,
        (
            _hash_bytes(certificate.certificate_journal_hash, name="certificate journal"),
            _hash_bytes(certificate.semantic_root_journal_hash, name="semantic root"),
            _hash_bytes(authenticated.plan.commitment, name="normalized plan commitment"),
            next_cursor.revision,
            certificate.certificate_version,
            certificate.epoch_id.to_bytes(8, "big"),
            _hash_bytes(certificate.settlement_receipt_id, name="settlement receipt ID"),
            _hash_bytes(certificate.semantic_claim_hash, name="semantic claim"),
            _hash_bytes(certificate.settlement_claim_hash, name="settlement claim"),
            _hash_bytes(certificate.settlement_image_id, name="settlement image ID"),
            certificate.settlement_profile_id,
            bytes.fromhex(certificate.settlement_manifest_sha256),
            _hash_bytes(certificate.application_id, name="application ID"),
            _hash_bytes(certificate.chain_or_domain_id, name="chain or domain ID"),
            _hash_bytes(certificate.public_policy_hash, name="public policy"),
            _hash_bytes(certificate.pre_state_root, name="pre-state root"),
            _hash_bytes(certificate.post_state_root, name="post-state root"),
            _hash_bytes(certificate.economic_action_ids_root, name="action IDs root"),
            _hash_bytes(certificate.ledger_cell_writes_root, name="cell writes root"),
            _hash_bytes(certificate.asset_effects_root, name="asset effects root"),
            _hash_bytes(
                certificate.action_authorization_bindings_root,
                name="action authorization bindings root",
            ),
            _identifier_list_digest(_ACTION_LIST_DOMAIN, certificate.action_nullifiers),
            _hash_bytes(
                certificate.authorization_grant_spend_nullifiers_root,
                name="grant spend root",
            ),
            _identifier_list_digest(
                _GRANT_LIST_DOMAIN,
                certificate.authorization_grant_spend_nullifiers,
            ),
            _hash_bytes(certificate.consumed_object_ids_root, name="consumed IDs root"),
            _identifier_list_digest(_CONSUMED_LIST_DOMAIN, certificate.consumed_object_ids),
            _hash_bytes(certificate.message_effects_root, name="message effects root"),
            _hash_bytes(certificate.carry_effects_root, name="carry effects root"),
            _hash_bytes(certificate.reward_effects_root, name="reward effects root"),
            _hash_bytes(certificate.effect_plan_commitment, name="effect plan commitment"),
            bytes.fromhex(certificate.canonical_certificate_sha256),
            certificate.canonical_certificate,
            bytes.fromhex(certificate.exact_effect_plan_sha256),
            certificate.exact_effect_plan,
            bytes.fromhex(provenance.authority_manifest_sha256),
            bytes.fromhex(provenance.admission_policy_binding_sha256),
            bytes.fromhex(provenance.verifier_executable_sha256),
            bytes.fromhex(provenance.verification_request_sha256),
            SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,
        ),
    )
    journal = _hash_bytes(certificate.certificate_journal_hash, name="certificate journal")
    connection.executemany(
        "INSERT INTO zrpf_settlement_action_nullifiers "
        "(action_nullifier, certificate_journal_hash, ordinal) VALUES (?, ?, ?)",
        (
            (_hash_bytes(value, name="action nullifier"), journal, ordinal)
            for ordinal, value in enumerate(certificate.action_nullifiers)
        ),
    )
    connection.executemany(
        "INSERT INTO zrpf_settlement_consumed_objects "
        "(consumed_object_id, certificate_journal_hash, ordinal) VALUES (?, ?, ?)",
        (
            (_hash_bytes(value, name="consumed object ID"), journal, ordinal)
            for ordinal, value in enumerate(certificate.consumed_object_ids)
        ),
    )


def _cas_authenticated_certificate_meta(
    connection: sqlite3.Connection,
    authenticated: _AuthenticatedSettlementCertificateV1,
    next_cursor: DurableZrpfSettlementCursorV1,
) -> None:
    previous = connection.execute(
        "SELECT certificate_count, last_settlement_revision "
        "FROM zrpf_settlement_certificate_meta WHERE singleton = 1"
    ).fetchone()
    if previous is None:
        raise ValueError("authenticated certificate metadata row is missing")
    previous_count = int(previous["certificate_count"])
    previous_revision = previous["last_settlement_revision"]
    certificate = authenticated.certificate
    cursor = connection.execute(
        """
        UPDATE zrpf_settlement_certificate_meta
        SET certificate_count = ?, last_settlement_revision = ?,
            last_epoch_id_be = ?, last_certificate_journal_hash = ?
        WHERE singleton = 1 AND certificate_count = ?
          AND last_settlement_revision IS ?
          AND settlement_authority = 0 AND authority_blocked_reason = ?
        """,
        (
            previous_count + 1,
            next_cursor.revision,
            certificate.epoch_id.to_bytes(8, "big"),
            _hash_bytes(certificate.certificate_journal_hash, name="certificate journal"),
            previous_count,
            previous_revision,
            SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,
        ),
    )
    if cursor.rowcount != 1:
        raise ZrpfAtomicSettlementStoreErrorV1(
            "AUTHENTICATED_SETTLEMENT_CERTIFICATE_INTERNAL_CAS_FAILED",
            "serialized certificate metadata compare-and-swap changed no row",
        )


def _certificate_receipt_from_row(
    row: sqlite3.Row,
) -> DurableAuthenticatedSettlementCertificateReceiptV1:
    return DurableAuthenticatedSettlementCertificateReceiptV1(
        certificate_journal_hash=_hex_hash(bytes(row["certificate_journal_hash"])),
        semantic_root_journal_hash=_hex_hash(bytes(row["semantic_root_journal_hash"])),
        normalized_plan_commitment=_hex_hash(bytes(row["plan_commitment"])),
        effect_plan_commitment=_hex_hash(bytes(row["effect_plan_commitment"])),
        settlement_receipt_id=_hex_hash(bytes(row["settlement_receipt_id"])),
        settlement_claim_hash=_hex_hash(bytes(row["settlement_claim_hash"])),
        settlement_image_id=_hex_hash(bytes(row["settlement_image_id"])),
        settlement_profile_id=str(row["settlement_profile_id"]),
        settlement_revision=int(row["settlement_revision"]),
        epoch_id=int.from_bytes(bytes(row["epoch_id_be"]), "big"),
        previous_state_root=_hex_hash(bytes(row["pre_state_root"])),
        result_state_root=_hex_hash(bytes(row["post_state_root"])),
        settlement_authority=bool(row["settlement_authority"]),
        authority_blocked_reason=str(row["authority_blocked_reason"]),
    )


def _read_identifier_sequence(
    connection: sqlite3.Connection,
    *,
    table: str,
    column: str,
    certificate_journal_hash: str,
) -> tuple[str, ...]:
    allowed = {
        ("zrpf_settlement_action_nullifiers", "action_nullifier"),
        ("zrpf_settlement_consumed_objects", "consumed_object_id"),
    }
    if (table, column) not in allowed:
        raise ValueError("unsupported certificate identifier table")
    rows = connection.execute(
        f"SELECT ordinal, {column} FROM {table} "
        "WHERE certificate_journal_hash = ? ORDER BY ordinal",
        (_hash_bytes(certificate_journal_hash, name="certificate journal"),),
    ).fetchall()
    if [int(row["ordinal"]) for row in rows] != list(range(len(rows))):
        raise ValueError(f"stored {column} ordinals must be dense")
    return tuple(_hex_hash(bytes(row[column])) for row in rows)


def _identifier_list_digest(domain: bytes, identifiers: tuple[str, ...]) -> bytes:
    digest = hashlib.sha256()
    digest.update(len(domain).to_bytes(2, "big"))
    digest.update(domain)
    digest.update(len(identifiers).to_bytes(4, "big"))
    for identifier in identifiers:
        digest.update(_hash_bytes(identifier, name="persisted identifier"))
    return digest.digest()
