"""Combined replay-admission and settlement-plan SQLite schema."""

from __future__ import annotations

import sqlite3

from src.core._zrpf_settlement_commit_authority import (
    SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
)
from src.integration._recursive_stark_admission_store_schema import (
    _SCHEMA_STATEMENTS as _ADMISSION_SCHEMA_STATEMENTS,
)
from src.integration._recursive_stark_admission_store_schema import (
    GENESIS_STATE_ROOT,
)
from src.integration._recursive_stark_admission_store_schema import (
    _validate_database_content as _validate_admission_content,
)

ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1 = 0x5A525053
ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1 = 1

_BLOCKED_REASON_SQL = SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1

_SETTLEMENT_SCHEMA_STATEMENTS = (
    f"""
    CREATE TABLE zrpf_settlement_meta (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 1),
        revision INTEGER NOT NULL CHECK (revision BETWEEN 0 AND 1048576),
        plan_count INTEGER NOT NULL CHECK (plan_count BETWEEN 0 AND 1048576),
        genesis_state_root BLOB NOT NULL
            CHECK (typeof(genesis_state_root) = 'blob' AND length(genesis_state_root) = 32),
        state_root BLOB NOT NULL
            CHECK (typeof(state_root) = 'blob' AND length(state_root) = 32),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        authority_blocked_reason TEXT NOT NULL
            CHECK (authority_blocked_reason = '{_BLOCKED_REASON_SQL}'),
        CHECK (revision = plan_count)
    ) STRICT, WITHOUT ROWID
    """,
    f"""
    CREATE TABLE zrpf_settlement_plans (
        plan_commitment BLOB NOT NULL PRIMARY KEY CHECK (length(plan_commitment) = 32),
        root_journal_hash BLOB NOT NULL UNIQUE
            REFERENCES zrpf_admissions(root_journal_hash) ON DELETE RESTRICT,
        admission_revision INTEGER NOT NULL
            REFERENCES zrpf_admissions(revision) ON DELETE RESTRICT,
        settlement_revision INTEGER NOT NULL UNIQUE
            CHECK (settlement_revision BETWEEN 1 AND 1048576),
        application_id BLOB NOT NULL CHECK (length(application_id) = 32),
        chain_or_domain_id BLOB NOT NULL CHECK (length(chain_or_domain_id) = 32),
        epoch_id_be BLOB NOT NULL CHECK (length(epoch_id_be) = 8),
        public_policy_hash BLOB NOT NULL CHECK (length(public_policy_hash) = 32),
        previous_state_root BLOB NOT NULL CHECK (length(previous_state_root) = 32),
        result_state_root BLOB NOT NULL CHECK (length(result_state_root) = 32),
        economic_action_ids_root BLOB NOT NULL CHECK (length(economic_action_ids_root) = 32),
        ledger_cell_writes_root BLOB NOT NULL CHECK (length(ledger_cell_writes_root) = 32),
        asset_effects_root BLOB NOT NULL CHECK (length(asset_effects_root) = 32),
        authorization_consumptions_root BLOB NOT NULL
            CHECK (length(authorization_consumptions_root) = 32),
        authorization_nullifiers_root BLOB NOT NULL
            CHECK (length(authorization_nullifiers_root) = 32),
        authorization_grant_spend_nullifiers_root BLOB NOT NULL
            CHECK (length(authorization_grant_spend_nullifiers_root) = 32),
        message_effects_root BLOB NOT NULL CHECK (length(message_effects_root) = 32),
        carry_effects_root BLOB NOT NULL CHECK (length(carry_effects_root) = 32),
        reward_effects_root BLOB NOT NULL CHECK (length(reward_effects_root) = 32),
        canonical_plan BLOB NOT NULL
            CHECK (typeof(canonical_plan) = 'blob' AND length(canonical_plan) BETWEEN 2 AND 134217728),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        authority_blocked_reason TEXT NOT NULL
            CHECK (authority_blocked_reason = '{_BLOCKED_REASON_SQL}'),
        CHECK (admission_revision = settlement_revision)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_economic_actions (
        economic_action_id BLOB NOT NULL PRIMARY KEY CHECK (length(economic_action_id) = 32),
        plan_commitment BLOB NOT NULL
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        UNIQUE (plan_commitment, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_cell_writes (
        plan_commitment BLOB NOT NULL
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        economic_action_id BLOB NOT NULL CHECK (length(economic_action_id) = 32),
        cell_key BLOB NOT NULL CHECK (length(cell_key) = 32),
        canonical_record BLOB NOT NULL
            CHECK (typeof(canonical_record) = 'blob' AND length(canonical_record) BETWEEN 2 AND 16384),
        PRIMARY KEY (plan_commitment, ordinal),
        UNIQUE (plan_commitment, cell_key)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_asset_effects (
        effect_id BLOB NOT NULL PRIMARY KEY CHECK (length(effect_id) = 32),
        plan_commitment BLOB NOT NULL
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        economic_action_id BLOB NOT NULL CHECK (length(economic_action_id) = 32),
        canonical_record BLOB NOT NULL
            CHECK (typeof(canonical_record) = 'blob' AND length(canonical_record) BETWEEN 2 AND 16384),
        UNIQUE (plan_commitment, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_authorization_consumptions (
        authorization_nullifier BLOB NOT NULL PRIMARY KEY
            CHECK (length(authorization_nullifier) = 32),
        authorization_grant_spend_nullifier BLOB NOT NULL UNIQUE
            CHECK (length(authorization_grant_spend_nullifier) = 32),
        plan_commitment BLOB NOT NULL
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        economic_action_id BLOB NOT NULL CHECK (length(economic_action_id) = 32),
        canonical_record BLOB NOT NULL
            CHECK (typeof(canonical_record) = 'blob' AND length(canonical_record) BETWEEN 2 AND 16384),
        UNIQUE (plan_commitment, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_message_effects (
        message_id BLOB NOT NULL PRIMARY KEY CHECK (length(message_id) = 32),
        plan_commitment BLOB NOT NULL
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        economic_action_id BLOB NOT NULL CHECK (length(economic_action_id) = 32),
        canonical_record BLOB NOT NULL
            CHECK (typeof(canonical_record) = 'blob' AND length(canonical_record) BETWEEN 2 AND 16384),
        UNIQUE (plan_commitment, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_carry_effects (
        carry_id BLOB NOT NULL PRIMARY KEY CHECK (length(carry_id) = 32),
        plan_commitment BLOB NOT NULL
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        economic_action_id BLOB NOT NULL CHECK (length(economic_action_id) = 32),
        canonical_record BLOB NOT NULL
            CHECK (typeof(canonical_record) = 'blob' AND length(canonical_record) BETWEEN 2 AND 16384),
        UNIQUE (plan_commitment, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_reward_effects (
        reward_id BLOB NOT NULL PRIMARY KEY CHECK (length(reward_id) = 32),
        plan_commitment BLOB NOT NULL
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        economic_action_id BLOB NOT NULL CHECK (length(economic_action_id) = 32),
        canonical_record BLOB NOT NULL
            CHECK (typeof(canonical_record) = 'blob' AND length(canonical_record) BETWEEN 2 AND 16384),
        UNIQUE (plan_commitment, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
)

_ALL_SCHEMA_STATEMENTS = _ADMISSION_SCHEMA_STATEMENTS + _SETTLEMENT_SCHEMA_STATEMENTS
_ADMISSION_TABLE_NAMES = (
    "zrpf_store_meta",
    "zrpf_admissions",
    "zrpf_child_claims",
    "zrpf_accepted_receipts",
    "zrpf_cross_shard_messages",
)
_SETTLEMENT_TABLE_NAMES = (
    "zrpf_settlement_meta",
    "zrpf_settlement_plans",
    "zrpf_settlement_economic_actions",
    "zrpf_settlement_cell_writes",
    "zrpf_settlement_asset_effects",
    "zrpf_settlement_authorization_consumptions",
    "zrpf_settlement_message_effects",
    "zrpf_settlement_carry_effects",
    "zrpf_settlement_reward_effects",
)
_EXPECTED_SCHEMA_SQL = dict(
    zip(
        _ADMISSION_TABLE_NAMES + _SETTLEMENT_TABLE_NAMES,
        _ALL_SCHEMA_STATEMENTS,
        strict=True,
    )
)


def _initialize_or_validate_atomic_settlement_store(
    connection: sqlite3.Connection,
    *,
    genesis_settlement_state_root: bytes,
) -> None:
    if not connection.in_transaction:
        raise ValueError("atomic settlement initialization requires an existing transaction")
    existing_objects = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing_objects:
        if connection.execute("PRAGMA application_id").fetchone()[0] != 0:
            raise ValueError("empty atomic settlement database has an application_id")
        if connection.execute("PRAGMA user_version").fetchone()[0] != 0:
            raise ValueError("empty atomic settlement database has a user_version")
        connection.execute(f"PRAGMA application_id = {ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1}")
        connection.execute(f"PRAGMA user_version = {ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1}")
        for statement in _ALL_SCHEMA_STATEMENTS:
            connection.execute(statement)
        connection.execute(
            """
            INSERT INTO zrpf_store_meta (
                singleton, schema_version, revision, chain_id, state_root,
                root_count, slot_count, child_claim_count, receipt_count,
                message_count
            ) VALUES (1, 1, 0, NULL, ?, 0, 0, 0, 0, 0)
            """,
            (GENESIS_STATE_ROOT,),
        )
        connection.execute(
            """
            INSERT INTO zrpf_settlement_meta (
                singleton, schema_version, revision, plan_count,
                genesis_state_root, state_root, settlement_authority,
                authority_blocked_reason
            ) VALUES (1, 1, 0, 0, ?, ?, 0, ?)
            """,
            (
                genesis_settlement_state_root,
                genesis_settlement_state_root,
                SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
            ),
        )
    _validate_atomic_settlement_schema(connection)
    _validate_admission_content(connection)
    _validate_settlement_meta(connection, genesis_settlement_state_root)


def _validate_atomic_settlement_schema(connection: sqlite3.Connection) -> None:
    if (
        connection.execute("PRAGMA application_id").fetchone()[0]
        != ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1
    ):
        raise ValueError("atomic settlement application_id mismatch")
    if (
        connection.execute("PRAGMA user_version").fetchone()[0]
        != ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1
    ):
        raise ValueError("atomic settlement user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _EXPECTED_SCHEMA_SQL}
    if observed != expected:
        raise ValueError("atomic settlement schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_EXPECTED_SCHEMA_SQL[name]):
            raise ValueError(f"atomic settlement schema SQL mismatch for {name}")


def _validate_settlement_meta(
    connection: sqlite3.Connection,
    expected_genesis_state_root: bytes,
) -> None:
    row = connection.execute("SELECT * FROM zrpf_settlement_meta WHERE singleton = 1").fetchone()
    if row is None:
        raise ValueError("atomic settlement metadata row is missing")
    if bytes(row["genesis_state_root"]) != expected_genesis_state_root:
        raise ValueError("atomic settlement governed genesis root mismatch")
    revision = int(row["revision"])
    plan_count = connection.execute("SELECT count(*) FROM zrpf_settlement_plans").fetchone()[0]
    if revision != plan_count or int(row["plan_count"]) != plan_count:
        raise ValueError("atomic settlement metadata count mismatch")
    if int(row["settlement_authority"]) != 0:
        raise ValueError("atomic settlement authority must remain false")
    if str(row["authority_blocked_reason"]) != SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1:
        raise ValueError("atomic settlement blocked reason mismatch")
    if revision == 0 and bytes(row["state_root"]) != expected_genesis_state_root:
        raise ValueError("atomic settlement empty state root mismatch")


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())
