PRAGMA foreign_keys = ON;

CREATE TABLE IF NOT EXISTS e03_publication_commits (
    sequence INTEGER PRIMARY KEY CHECK(sequence BETWEEN 1 AND 128),
    commit_id TEXT NOT NULL UNIQUE CHECK(
        length(commit_id) = 64
        AND commit_id NOT GLOB '*[^0-9a-f]*'
    ),
    fingerprint TEXT NOT NULL CHECK(
        length(fingerprint) = 64
        AND fingerprint NOT GLOB '*[^0-9a-f]*'
    ),
    nullifier_root TEXT NOT NULL UNIQUE CHECK(
        length(nullifier_root) = 64
        AND nullifier_root NOT GLOB '*[^0-9a-f]*'
    ),
    request_identity_root TEXT NOT NULL CHECK(
        length(request_identity_root) = 64
        AND request_identity_root NOT GLOB '*[^0-9a-f]*'
    ),
    UNIQUE(commit_id, nullifier_root, fingerprint)
);

CREATE TABLE IF NOT EXISTS e03_publication_nullifiers (
    nullifier_root TEXT PRIMARY KEY CHECK(
        length(nullifier_root) = 64
        AND nullifier_root NOT GLOB '*[^0-9a-f]*'
    ),
    commit_id TEXT NOT NULL,
    fingerprint TEXT NOT NULL CHECK(
        length(fingerprint) = 64
        AND fingerprint NOT GLOB '*[^0-9a-f]*'
    ),
    UNIQUE(commit_id),
    FOREIGN KEY(commit_id, nullifier_root, fingerprint)
        REFERENCES e03_publication_commits(commit_id, nullifier_root, fingerprint)
);

CREATE TABLE IF NOT EXISTS e03_publication_effects (
    effect_id TEXT PRIMARY KEY CHECK(
        length(effect_id) = 64
        AND effect_id NOT GLOB '*[^0-9a-f]*'
    ),
    commit_id TEXT NOT NULL REFERENCES e03_publication_commits(commit_id),
    ordinal INTEGER NOT NULL CHECK(ordinal BETWEEN 0 AND 63),
    destination TEXT NOT NULL CHECK(
        length(CAST(destination AS BLOB)) BETWEEN 1 AND 256
    ),
    payload_root TEXT NOT NULL CHECK(
        length(payload_root) = 64
        AND payload_root NOT GLOB '*[^0-9a-f]*'
    ),
    writer_profile_root TEXT NOT NULL CHECK(
        length(writer_profile_root) = 64
        AND writer_profile_root NOT GLOB '*[^0-9a-f]*'
    ),
    adapter_profile_root TEXT NOT NULL CHECK(
        length(adapter_profile_root) = 64
        AND adapter_profile_root NOT GLOB '*[^0-9a-f]*'
    ),
    UNIQUE(commit_id, ordinal)
);
