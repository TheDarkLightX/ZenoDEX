"""Combined replay-admission and settlement-plan SQLite schema."""

from __future__ import annotations

import sqlite3

from src.core._zrpf_settlement_certificate_authority import (
    SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,
)
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
ATOMIC_SETTLEMENT_STORE_LEGACY_SCHEMA_VERSION_V1 = 1
ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V2 = 2
# Compatibility export: the V1 store class now opens the minimally extended
# physical schema so its existing atomic engine can host certificate rows.
ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1 = ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V2

_BLOCKED_REASON_SQL = SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
_CERTIFICATE_BLOCKED_REASON_SQL = SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1

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

_CERTIFICATE_SCHEMA_STATEMENTS = (
    f"""
    CREATE TABLE zrpf_settlement_certificate_meta (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 1),
        certificate_count INTEGER NOT NULL
            CHECK (certificate_count BETWEEN 0 AND 1048576),
        last_settlement_revision INTEGER
            CHECK (last_settlement_revision BETWEEN 1 AND 1048576),
        last_epoch_id_be BLOB CHECK (last_epoch_id_be IS NULL OR length(last_epoch_id_be) = 8),
        last_certificate_journal_hash BLOB
            CHECK (last_certificate_journal_hash IS NULL
                OR length(last_certificate_journal_hash) = 32),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        authority_blocked_reason TEXT NOT NULL
            CHECK (authority_blocked_reason = '{_CERTIFICATE_BLOCKED_REASON_SQL}'),
        CHECK (
            (certificate_count = 0 AND last_settlement_revision IS NULL
                AND last_epoch_id_be IS NULL AND last_certificate_journal_hash IS NULL)
            OR
            (certificate_count > 0 AND last_settlement_revision IS NOT NULL
                AND last_epoch_id_be IS NOT NULL AND last_certificate_journal_hash IS NOT NULL)
        )
    ) STRICT, WITHOUT ROWID
    """,
    f"""
    CREATE TABLE zrpf_settlement_certificates (
        certificate_journal_hash BLOB NOT NULL PRIMARY KEY
            CHECK (length(certificate_journal_hash) = 32),
        semantic_root_journal_hash BLOB NOT NULL UNIQUE
            REFERENCES zrpf_admissions(root_journal_hash) ON DELETE RESTRICT,
        plan_commitment BLOB NOT NULL UNIQUE
            REFERENCES zrpf_settlement_plans(plan_commitment) ON DELETE RESTRICT,
        settlement_revision INTEGER NOT NULL UNIQUE
            REFERENCES zrpf_settlement_plans(settlement_revision) ON DELETE RESTRICT,
        certificate_version INTEGER NOT NULL CHECK (certificate_version IN (1, 2)),
        epoch_id_be BLOB NOT NULL CHECK (length(epoch_id_be) = 8),
        settlement_receipt_id BLOB NOT NULL UNIQUE CHECK (length(settlement_receipt_id) = 32),
        semantic_claim_hash BLOB NOT NULL CHECK (length(semantic_claim_hash) = 32),
        settlement_claim_hash BLOB NOT NULL CHECK (length(settlement_claim_hash) = 32),
        settlement_image_id BLOB NOT NULL CHECK (length(settlement_image_id) = 32),
        settlement_profile_id TEXT NOT NULL
            CHECK (length(settlement_profile_id) BETWEEN 1 AND 128),
        settlement_manifest_sha256 BLOB NOT NULL CHECK (length(settlement_manifest_sha256) = 32),
        application_id BLOB NOT NULL CHECK (length(application_id) = 32),
        chain_or_domain_id BLOB NOT NULL CHECK (length(chain_or_domain_id) = 32),
        public_policy_hash BLOB NOT NULL CHECK (length(public_policy_hash) = 32),
        pre_state_root BLOB NOT NULL CHECK (length(pre_state_root) = 32),
        post_state_root BLOB NOT NULL CHECK (length(post_state_root) = 32),
        economic_action_ids_root BLOB NOT NULL CHECK (length(economic_action_ids_root) = 32),
        ledger_cell_writes_root BLOB NOT NULL CHECK (length(ledger_cell_writes_root) = 32),
        asset_effects_root BLOB NOT NULL CHECK (length(asset_effects_root) = 32),
        action_authorization_bindings_root BLOB NOT NULL
            CHECK (length(action_authorization_bindings_root) = 32),
        action_nullifier_list_sha256 BLOB NOT NULL
            CHECK (length(action_nullifier_list_sha256) = 32),
        authorization_grant_spend_nullifiers_root BLOB NOT NULL
            CHECK (length(authorization_grant_spend_nullifiers_root) = 32),
        authorization_grant_spend_list_sha256 BLOB NOT NULL
            CHECK (length(authorization_grant_spend_list_sha256) = 32),
        consumed_object_ids_root BLOB NOT NULL CHECK (length(consumed_object_ids_root) = 32),
        consumed_object_id_list_sha256 BLOB NOT NULL
            CHECK (length(consumed_object_id_list_sha256) = 32),
        message_effects_root BLOB NOT NULL CHECK (length(message_effects_root) = 32),
        carry_effects_root BLOB NOT NULL CHECK (length(carry_effects_root) = 32),
        reward_effects_root BLOB NOT NULL CHECK (length(reward_effects_root) = 32),
        effect_plan_commitment BLOB NOT NULL CHECK (length(effect_plan_commitment) = 32),
        canonical_certificate_sha256 BLOB NOT NULL
            CHECK (length(canonical_certificate_sha256) = 32),
        canonical_certificate BLOB NOT NULL
            CHECK (typeof(canonical_certificate) = 'blob'
                AND length(canonical_certificate) BETWEEN 1 AND 1048576),
        exact_effect_plan_sha256 BLOB NOT NULL CHECK (length(exact_effect_plan_sha256) = 32),
        exact_effect_plan BLOB NOT NULL
            CHECK (typeof(exact_effect_plan) = 'blob'
                AND length(exact_effect_plan) BETWEEN 1 AND 134217728),
        authority_manifest_sha256 BLOB NOT NULL CHECK (length(authority_manifest_sha256) = 32),
        admission_policy_binding_sha256 BLOB NOT NULL
            CHECK (length(admission_policy_binding_sha256) = 32),
        verifier_executable_sha256 BLOB NOT NULL CHECK (length(verifier_executable_sha256) = 32),
        verification_request_sha256 BLOB NOT NULL CHECK (length(verification_request_sha256) = 32),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        authority_blocked_reason TEXT NOT NULL
            CHECK (authority_blocked_reason = '{_CERTIFICATE_BLOCKED_REASON_SQL}')
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_action_nullifiers (
        action_nullifier BLOB NOT NULL PRIMARY KEY CHECK (length(action_nullifier) = 32),
        certificate_journal_hash BLOB NOT NULL
            REFERENCES zrpf_settlement_certificates(certificate_journal_hash) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        UNIQUE (certificate_journal_hash, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_settlement_consumed_objects (
        consumed_object_id BLOB NOT NULL PRIMARY KEY CHECK (length(consumed_object_id) = 32),
        certificate_journal_hash BLOB NOT NULL
            REFERENCES zrpf_settlement_certificates(certificate_journal_hash) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 8191),
        UNIQUE (certificate_journal_hash, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
)

_LEGACY_SCHEMA_STATEMENTS = _ADMISSION_SCHEMA_STATEMENTS + _SETTLEMENT_SCHEMA_STATEMENTS
_ALL_SCHEMA_STATEMENTS = _LEGACY_SCHEMA_STATEMENTS + _CERTIFICATE_SCHEMA_STATEMENTS
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
_CERTIFICATE_TABLE_NAMES = (
    "zrpf_settlement_certificate_meta",
    "zrpf_settlement_certificates",
    "zrpf_settlement_action_nullifiers",
    "zrpf_settlement_consumed_objects",
)
_LEGACY_EXPECTED_SCHEMA_SQL = dict(
    zip(
        _ADMISSION_TABLE_NAMES + _SETTLEMENT_TABLE_NAMES,
        _LEGACY_SCHEMA_STATEMENTS,
        strict=True,
    )
)
_EXPECTED_SCHEMA_SQL = dict(
    zip(
        _ADMISSION_TABLE_NAMES + _SETTLEMENT_TABLE_NAMES + _CERTIFICATE_TABLE_NAMES,
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
        connection.execute(f"PRAGMA user_version = {ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V2}")
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
        connection.execute(
            """
            INSERT INTO zrpf_settlement_certificate_meta (
                singleton, schema_version, certificate_count,
                last_settlement_revision, last_epoch_id_be,
                last_certificate_journal_hash, settlement_authority,
                authority_blocked_reason
            ) VALUES (1, 1, 0, NULL, NULL, NULL, 0, ?)
            """,
            (SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,),
        )
    elif (
        connection.execute("PRAGMA application_id").fetchone()[0]
        == ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1
        and connection.execute("PRAGMA user_version").fetchone()[0]
        == ATOMIC_SETTLEMENT_STORE_LEGACY_SCHEMA_VERSION_V1
    ):
        _validate_schema_objects(connection, _LEGACY_EXPECTED_SCHEMA_SQL)
        _validate_admission_content(connection)
        _validate_settlement_meta(connection, genesis_settlement_state_root)
        for statement in _CERTIFICATE_SCHEMA_STATEMENTS:
            connection.execute(statement)
        connection.execute(
            """
            INSERT INTO zrpf_settlement_certificate_meta (
                singleton, schema_version, certificate_count,
                last_settlement_revision, last_epoch_id_be,
                last_certificate_journal_hash, settlement_authority,
                authority_blocked_reason
            ) VALUES (1, 1, 0, NULL, NULL, NULL, 0, ?)
            """,
            (SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,),
        )
        connection.execute(f"PRAGMA user_version = {ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V2}")
    _validate_atomic_settlement_schema(connection)
    _validate_admission_content(connection)
    _validate_settlement_meta(connection, genesis_settlement_state_root)
    _validate_certificate_meta(connection)


def _validate_atomic_settlement_schema(connection: sqlite3.Connection) -> None:
    if (
        connection.execute("PRAGMA application_id").fetchone()[0]
        != ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1
    ):
        raise ValueError("atomic settlement application_id mismatch")
    if (
        connection.execute("PRAGMA user_version").fetchone()[0]
        != ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V2
    ):
        raise ValueError("atomic settlement user_version mismatch")
    _validate_schema_objects(connection, _EXPECTED_SCHEMA_SQL)


def _validate_schema_objects(
    connection: sqlite3.Connection,
    expected_sql: dict[str, str],
) -> None:
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in expected_sql}
    if observed != expected:
        raise ValueError("atomic settlement schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(expected_sql[name]):
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


def _validate_certificate_meta(connection: sqlite3.Connection) -> None:
    row = connection.execute(
        "SELECT * FROM zrpf_settlement_certificate_meta WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise ValueError("authenticated certificate metadata row is missing")
    count = int(
        connection.execute("SELECT count(*) FROM zrpf_settlement_certificates").fetchone()[0]
    )
    if int(row["certificate_count"]) != count:
        raise ValueError("authenticated certificate metadata count mismatch")
    if int(row["settlement_authority"]) != 0:
        raise ValueError("authenticated certificate metadata authority must remain false")
    if (
        str(row["authority_blocked_reason"])
        != SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1
    ):
        raise ValueError("authenticated certificate metadata blocked reason mismatch")
    if count == 0:
        if any(
            row[name] is not None
            for name in (
                "last_settlement_revision",
                "last_epoch_id_be",
                "last_certificate_journal_hash",
            )
        ):
            raise ValueError("empty authenticated certificate metadata has a head")
        return
    latest = connection.execute(
        "SELECT settlement_revision, epoch_id_be, certificate_journal_hash "
        "FROM zrpf_settlement_certificates ORDER BY settlement_revision DESC LIMIT 1"
    ).fetchone()
    if latest is None:
        raise ValueError("authenticated certificate metadata latest row is missing")
    if (
        int(row["last_settlement_revision"]) != int(latest["settlement_revision"])
        or bytes(row["last_epoch_id_be"]) != bytes(latest["epoch_id_be"])
        or bytes(row["last_certificate_journal_hash"])
        != bytes(latest["certificate_journal_hash"])
    ):
        raise ValueError("authenticated certificate metadata head mismatch")


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())
