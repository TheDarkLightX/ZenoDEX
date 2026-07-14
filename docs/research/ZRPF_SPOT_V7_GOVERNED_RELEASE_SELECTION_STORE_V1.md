# ZRPF Spot V7 Governed Release Selection Store V1

Date: 2026-07-14

Status: authority-false local lineage and revocation store implemented

Authority: none

## Claim scope

V1 records an externally governed Spot V7 release-selection lineage through a
single local SQLite transaction boundary:

```text
authority-neutral candidate object
  -> reparse exact canonical candidate bytes
  -> independently expected candidate ID from selector input
  -> fixed-width governed SELECT or REVOKE input
  -> exact current-head and database-revision CAS
  -> append-only event plus metadata update in BEGIN IMMEDIATE
  -> authority-false recovery cursor
```

The store does not trust the nominal Python candidate object. It reparses
`candidate.canonical_bytes`, checks the candidate against the independently
supplied target candidate ID, recomputes the canonical SHA-256, and compares
the nominal candidate ID, revision, parent, and bytes with those derived
values before opening the write transaction.

The governed selector input is still externally proposed data. V1 checks its
canonical representation and durable-state relationship. It does not verify a
signature, validator quorum, hardware attestation, consensus decision, or
governance execution receipt.

## Exact wire objects

`GovernedReleaseSelectorInputV1` is exactly 320 bytes in big-endian order. It
binds:

- one fixed SELECT or REVOKE operation tag;
- exact format flags and zero reserved fields;
- expected database revision;
- evaluation epoch;
- target release revision;
- expected current candidate and selection-input identities;
- target candidate ID and exact candidate-byte SHA-256;
- the candidate-bound rollback-policy root and an external
  revocation-registry root;
- an absent or exact revocation-record ID according to the operation;
- one nonzero selector nonce.

`SpotV7RevocationRecordV1` is exactly 216 bytes in big-endian order. It binds
the candidate, candidate-governed revocation-policy root, external revocation
registry root, effective epoch, record revision, reason code, issuer-set root,
and record nonce.

Both objects use domain-separated SHA-256 identities with explicit domain and
payload lengths. Their parsers require independently supplied expected
identities. A self-consistent hash embedded by an untrusted caller is not an
acceptance input.

The fixed position-distinct fixtures are:

```text
SELECT bytes:        320
SELECT SHA-256:      4eca7799c12b71bd1da20c85b37d46717d0dfad330a85ef41989dfbaddc989a0
SELECT input ID:     e45975bc8639b7781a066b2e45fde185821a688635546ffaa337cd2d49ad6d09

REVOKE bytes:        320
REVOKE SHA-256:      7e2cbeaef02f03ed46414564586254110d5936f325af39e7c46d7c49fddbde50
REVOKE input ID:     53a19332cbce4f2eb83c8bd79047eb4f0c9fa521778cd64e3f4a69c35eab0c47

revocation bytes:    216
revocation SHA-256:  5ac6ef420430e06c587b2a6a41410290e52b5f769fc9767821e0f4cc19d8251c
revocation ID:       863d4cd5ddcdfc70cbee2431d5ffe4cdd18d33127ff3f7f99fa15cc7e168fd43
```

## Selection transition

Genesis selection requires release revision one and no parent. Every later
selection requires:

```text
target.release_revision = current.release_revision + 1
target.parent_candidate_id = current.candidate_id
target.release_scope_id = current.release_scope_id
evaluation_epoch >= proposed_activation_epoch
evaluation_epoch < proposed_expiration_epoch, when present
evaluation_epoch >= prior accepted evaluation_epoch, after genesis
```

The release scope contains application, chain, domain, and release-profile
identity. Proof and receipt-security profiles remain candidate-specific and
may change in a later candidate.

Lower revisions and decreasing evaluation epochs reject as rollback. Equal but
different candidates reject as a fork. Revision gaps reject. Expected database
revision, current candidate, and current SELECT-input ID are independent CAS
fields and all must match.

An exact previously committed input with the exact same candidate and optional
revocation bytes is idempotent, even after a later event. A different input for
the same release or revocation is a conflict.

## Revocation transition

REVOKE requires the exact current candidate and a canonical revocation record.
The record must bind:

```text
record.candidate_id = current_candidate_id
record.revocation_policy_root = candidate.revocation_policy_root
record.revocation_registry_root = selector.revocation_registry_root
record.record_id = selector.revocation_record_id
record.effective_epoch <= selector.evaluation_epoch
```

Scheduled future revocation rejects because V1 has no trusted clock or pending
event scheduler. Once committed, revocation cannot be cleared. All later
selection and all different second revocations reject. Recovery or successor
activation after a revocation is deliberately left for a separately governed
future protocol.

## Atomic persistence and recovery

The database uses:

- a private owner-only regular file;
- rollback-journal mode;
- `synchronous=EXTRA`;
- `trusted_schema=OFF`;
- one exact schema and application ID;
- strict tables and fixed-width integer blobs;
- `BEGIN IMMEDIATE` for each transition;
- append-only event insertion and metadata CAS in one transaction;
- full deterministic history replay on open and read;
- `quick_check`, schema SQL, event continuity, state-root chain, candidate,
  selector, revocation, and authority-false column validation.

A failure after event insertion and before metadata CAS rolls back the complete
transaction. Two competing candidates from the same head serialize, and only
one can commit.

## Active distinguishing witnesses

The deterministic mutation corpus separates identity binding from semantic
interpretation. It establishes that:

- every byte position in both 320-byte selector fixtures rejects under the
  unchanged independently expected input identity;
- every byte position in the 216-byte revocation record rejects under the
  unchanged independently expected record identity;
- all format-flag and reserved bits reject when flipped;
- big-endian integer reversals change identity;
- policy, registry, candidate, and SHA field swaps remain distinguishable;
- re-bound release revision, candidate identity, candidate-byte SHA-256, and
  rollback-policy mutations reach distinct semantic reject boundaries;
- SELECT and REVOKE tags cannot cross public method boundaries;
- database-revision, current-candidate, and current-selection CAS fields are
  independently load-bearing;
- fork, release rollback, evaluation-epoch rollback, gap, activation, expiry,
  future revocation, conflicting revocation, restart corruption, schema
  corruption, and transaction-failure branches have pinned negative tests.

This mutation corpus is offline bug-finding and regression evidence. It is not
a proof of codec, SQLite, filesystem, or governance correctness.

## Evidence

```bash
python3 -m pytest -q \
  tests/test_zrpf_spot_v7_governed_release_selection_store_v1.py

python3 -m mypy --follow-imports=skip \
  tools/zrpf_spot_v7_governed_release_selector_input_v1.py \
  tools/zrpf_spot_v7_governed_release_selection_store_v1.py \
  tests/test_zrpf_spot_v7_governed_release_selection_store_v1.py
```

The required `zrpf-assurance` workflow inventories both modules and the test in
Ruff, mypy, and pytest.

## Non-claims

V1 does not establish:

- authenticity or quorum authority for selector or revocation inputs;
- storage rollback resistance against database replacement;
- resistance to hostile same-UID code or path replacement races;
- distributed consensus, fork choice, finality, or current-head publication;
- artifact opening, source-to-binary provenance, proof validity, or runtime
  execution;
- release activation, revocation execution outside this local record,
  settlement, privacy, or production readiness.

Every result and cursor property for selection, current status, revocation,
release, runtime, settlement, and production authority remains `false`.
