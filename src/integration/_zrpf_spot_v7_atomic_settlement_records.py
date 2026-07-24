"""Exact stored-identity and durable-receipt decoding for Spot V7 mechanics."""

from __future__ import annotations

import sqlite3

from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    DurableSpotV7AtomicSettlementReceiptV1,
    _hash_bytes,
    _hex_hash,
)


def _single_identifier(
    connection: sqlite3.Connection,
    table: str,
    column: str,
    settlement_commitment: bytes,
) -> str:
    statements = {
        ("spot_v7_economic_actions", "economic_action_id"): (
            "SELECT economic_action_id FROM spot_v7_economic_actions "
            "WHERE settlement_commitment = ?"
        ),
        ("spot_v7_authorization_nullifiers", "authorization_nullifier"): (
            "SELECT authorization_nullifier FROM spot_v7_authorization_nullifiers "
            "WHERE settlement_commitment = ?"
        ),
        (
            "spot_v7_authorization_grant_spends",
            "authorization_grant_spend_nullifier",
        ): (
            "SELECT authorization_grant_spend_nullifier "
            "FROM spot_v7_authorization_grant_spends WHERE settlement_commitment = ?"
        ),
    }
    try:
        statement = statements[(table, column)]
    except KeyError as exc:
        raise ValueError("unsupported Spot V7 identifier table") from exc
    rows = connection.execute(statement, (settlement_commitment,)).fetchall()
    if len(rows) != 1:
        raise ValueError(f"Spot V7 stored identifier count mismatch: {column}")
    return _hex_hash(bytes(rows[0][0]))


def _receipt_for_commitment(
    connection: sqlite3.Connection,
    settlement_commitment: str,
) -> DurableSpotV7AtomicSettlementReceiptV1 | None:
    commitment = _hash_bytes(settlement_commitment, name="settlement commitment")
    row = connection.execute(
        "SELECT * FROM spot_v7_settlements WHERE settlement_commitment = ?",
        (commitment,),
    ).fetchone()
    if row is None:
        return None
    return _receipt_from_row(connection, commitment, row)


def _receipt_from_row(
    connection: sqlite3.Connection,
    commitment: bytes,
    row: sqlite3.Row,
) -> DurableSpotV7AtomicSettlementReceiptV1:
    action = _single_identifier(
        connection, "spot_v7_economic_actions", "economic_action_id", commitment
    )
    authorization = _single_identifier(
        connection,
        "spot_v7_authorization_nullifiers",
        "authorization_nullifier",
        commitment,
    )
    grant = _single_identifier(
        connection,
        "spot_v7_authorization_grant_spends",
        "authorization_grant_spend_nullifier",
        commitment,
    )
    return DurableSpotV7AtomicSettlementReceiptV1(
        settlement_commitment=_hex_hash(bytes(row["settlement_commitment"])),
        settlement_revision=int(row["revision"]),
        epoch_id=int.from_bytes(bytes(row["epoch_id_be"]), "big"),
        previous_state_root=_hex_hash(bytes(row["previous_state_root"])),
        result_state_root=_hex_hash(bytes(row["result_state_root"])),
        receipt_sha256=_hex_hash(bytes(row["receipt_sha256"])),
        journal_sha256=_hex_hash(bytes(row["journal_sha256"])),
        firecracker_execution_record_sha256=_hex_hash(
            bytes(row["firecracker_execution_record_sha256"])
        ),
        firecracker_output_sha256=_hex_hash(bytes(row["firecracker_output_sha256"])),
        settlement_effect_plan_commitment=_hex_hash(
            bytes(row["settlement_effect_plan_commitment"])
        ),
        economic_action_id=action,
        authorization_nullifier=authorization,
        authorization_grant_spend_nullifier=grant,
        settlement_authority=False,
        production_authority=False,
        firecracker_execution_verified=False,
        authority_blocked_reason=str(row["authority_blocked_reason"]),
    )
