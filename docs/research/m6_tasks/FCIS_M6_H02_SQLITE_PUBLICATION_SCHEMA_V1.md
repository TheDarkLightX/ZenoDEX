# FCIS M6 H02 SQLite publication schema v1

Status: isolated research schema; unmounted.

This document records the exact logical tables declared by
experiments/fcis_m6_h02_sqlite_publication.py. The schema is a deterministic
replay fixture for the H01 matrix and the durable-retraction model.

## Root relations

The DRA snapshot root covers the canonical authority, atom, evidence,
nullifier, outbox, acknowledgment, deployment, and verifier rows reconstructed
by the durable-retraction model.

H02 adds the ANF relation:

    anf_set_root = H(sorted commit_id, atom_root, anf_root, anf_version)
    publication_root = H(snapshot_root, anf_set_root)

Rows are ordered by commit identity before hashing. The cached roots in
snapshot_meta must equal fresh recomputation. A selected state root without the
complete ANF relation is rejected.

## Table inventory

### snapshot_meta

One singleton row with:

    singleton
    genesis_state_root
    current_state_root
    snapshot_root
    deployment_config_root
    verifier_profile_root
    authority_head_epoch
    authority_head_root
    anf_set_root
    publication_root

The singleton key is exactly 1. Authority-head, ANF-set, and publication roots
are caches with checked rederivation obligations.

### authority_epochs

One row per authority epoch:

    epoch_index
    phase
    legacy_profile_root
    target_profile_root
    active_profile_root
    transport_root
    transition_root

Phase is closed to LEGACY, SHADOW_REPLAY, DUAL_CHECK, QUIESCED,
AUTHORITY_SWITCH, POST_SWITCH_VALIDATION, and LEGACY_DISABLED. Epoch indexes
are u32 values and form the canonical history order.

### authority_allowed_writers

The parallel writer relation:

    epoch_index
    writer_profile_root

The pair is unique and the epoch must exist.

### publication_atoms

One row per committed transition:

    sequence
    commit_id
    command_root
    expected_pre_root
    post_state_root
    writer_profile_root
    authority_epoch_index
    authority_state_root
    nullifier_root
    response_root
    receipt_root
    decision_root
    bundle_root
    replay_root
    deployment_config_root
    verifier_profile_root

Sequence is bounded and unique. Commit and nullifier identities are unique.
The authority epoch is a foreign key.

### publication_evidence

The complete evidence relation:

    commit_id
    kind
    value_root

Kind is closed to command, response, receipt, decision, bundle, replay, and
authority. The pair commit_id/kind is unique and commit_id is a foreign key.

### publication_nullifiers

The consumed authorization relation:

    nullifier_root
    commit_id
    fingerprint

The nullifier root is the primary key and commit_id references the atom.

### publication_outbox

The committed effect relation:

    effect_id
    commit_id
    ordinal
    destination
    payload_root
    adapter_profile_root

The effect identity is the primary key. Commit/ordinal pairs are unique, the
commit is a foreign key, and ordinal is bounded by the reviewed model.

### anf_publications

The proof-context relation introduced by H02:

    commit_id
    atom_root
    anf_root
    anf_version

Commit_id is the primary key and a foreign key to publication_atoms. The atom
root must equal the exact referenced atom root. The ANF version is pinned to
ANF_VERSION_V1.

### delivery_acks

The future acknowledgment relation:

    effect_id
    destination
    payload_root
    destination_receipt_root
    adapter_profile_root
    idempotency_root
    response_root

Effect identity is the primary key. H02 reopens this table as part of the
complete DRA layout, while worker delivery and acknowledgment admission remain
outside this task.

## Boundary rules

- Every root is exactly 64 lowercase hexadecimal characters.
- ANF roots enter through the 0x-prefixed D08 acceptance and are stored in the
  normalized 64-character form.
- Text values are nonempty and bounded by MAX_TEXT_BYTES.
- Numeric indexes use the declared u32 or model-specific bounded domains.
- Foreign keys are enabled on every created connection.
- Enum values and evidence kinds fail closed through SQL CHECK constraints.
- Canonical readers sort each collection by its specified key and reject
  duplicate, missing, surplus, crossed, or orphan rows.

## Publication and recovery boundary

The current implementation performs one BEGIN IMMEDIATE transaction, checks
all expected roots and the authority head, inserts the logical rows, performs
complete POST reopening before COMMIT, and rolls back on failure.

The SQLite trigger test demonstrates rollback after a partial insert in this
reference adapter. H03 and H04 still have to provide deterministic
process-crash injection and exact PRE/POST recovery evidence.

## Nonclaims

The schema is not a production datastore mount. It does not establish
durability under power loss, WAL/fsync correctness, concurrent linearization,
runtime caller coverage, destination idempotency, migration switching,
no-bypass evidence, or whole-system zUSD safety.
