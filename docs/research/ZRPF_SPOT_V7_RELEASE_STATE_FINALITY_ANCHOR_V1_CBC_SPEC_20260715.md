# Spot V7 Release-State Finality Anchor V1 CBC Specification

Status: authority-neutral codec and Store-derived projection implemented;
external monotonic observation and finality authority remain production
blockers.

## 1. Purpose

The authenticated release-state store can detect local tampering by replaying
its complete signed history. It cannot detect restoration of an older, fully
valid database snapshot. V1 closes that rollback class only when external
infrastructure remembers both the latest finalized checkpoint and the highest
authenticated release event observed before finality.

A locally written counter, local signature, copied checkpoint file, or Boolean
report is not an external monotonic anchor.

## 2. Canonical release-state checkpoint

`SpotV7ReleaseStateCheckpointV1` contains exactly:

```text
schema
application_id
chain_id
domain_id
release_profile
store_identity_hash
database_revision
last_evaluation_epoch
release_state_root
current_candidate_id
current_candidate_sha256
current_release_revision
current_select_input_id
current_revocation_record_id
parent_release_checkpoint_hash
release_checkpoint_sequence
release_checkpoint_hash
```

The checkpoint hash is exactly:

```text
SHA256(
  domain_sep("zrpf_spot_v7_release_state_checkpoint", version=1)
  || encode_bytes(canonical_json(checkpoint_without_checkpoint_hash))
)
```

The public codec accepts and returns untrusted canonical checkpoint documents.
Canonical bytes and a valid self-hash establish no Store provenance. The
separate `_StoreDerivedReleaseStateCheckpointV1` type is privately constructed
only by directly replaying Store V3 and validating the exact derived parent
chain. A protocol-specific finality adapter must consume that private type, not
the raw codec document.

A genesis checkpoint fixes checkpoint sequence zero, database revision zero,
evaluation epoch zero, the Store V3 genesis state root, and a zero parent hash.
Every successor has checkpoint sequence `parent.sequence + 1`, database
revision `parent.database_revision + 1`, and commits to the exact parent
checkpoint hash. Evaluation epoch is monotonic. Scope and store identity are
immutable across the chain. V1 emits exactly one checkpoint per authenticated
release-state event, so every standalone checkpoint also requires
`release_checkpoint_sequence == database_revision`.

The checkpoint represents an empty genesis state, an unrevoked candidate, or
terminal revocation. Cross-field validity is exact:

```text
empty genesis:
  release_checkpoint_sequence == 0
  current_candidate_id is absent
  current_candidate_sha256 is absent
  current_release_revision is absent
  current_select_input_id is absent
  current_revocation_record_id is absent

unrevoked:
  release_checkpoint_sequence > 0
  current_candidate_id is present
  current_candidate_sha256 is present
  current_release_revision is present
  current_select_input_id is present
  current_revocation_record_id is absent

revoked:
  release_checkpoint_sequence > 0
  prior candidate and SELECT identities remain present
  current_revocation_record_id is present
```

The first selected release has release revision one. Each later SELECT advances
the release revision exactly once and consumes a new candidate identity and
SELECT input identity. A REVOKE preserves the exact selected candidate ID,
candidate byte digest, release revision, and SELECT input identity. Revocation
is terminal in V1. Every successor commits a different release-state root.

## 3. External finality certificate

The checkpoint becomes externally anchored only through one protocol-specific
`AuthenticatedReleaseStateFinalityV1`. Its constructor must verify:

```text
exact checkpoint bytes
exact external consensus certificate bytes
exact signer or validator set
governed verifier-set root and lifecycle
distinct signer identities
quorum threshold and signature validity
external height, block hash, and parent relation
fork-choice/finality rule
checkpoint inclusion or exact payload commitment
finality policy root
```

The proof-neutral release-state layer may consume the authenticated projection.
It may not parse caller-provided `finalized=true`, `quorum_verified=true`, or
equivalent fields as authority.

## 4. Rollback and fork decision table

Let `L` be the replayed local Store V3 head, `F` the latest authenticated
external finalized release-state checkpoint, and `W` the externally monotonic
highest-observed authenticated event watermark. The watermark is recorded
before the event can influence operational eligibility.

| Relation | Required result |
| --- | --- |
| `F.revision > L.revision` | Reject as local rollback or incomplete recovery. |
| `W.revision > L.revision` | Reject as local rollback, even when `L == F`. |
| `W.revision > F.revision` | A previously observed event is pending finality; pause operation. |
| equal revision, different state root | Reject as fork, corruption, or wrong store identity. |
| `L == F == W` with equal state and event roots | The local head is externally anchored. |
| `L.revision > F.revision` | Local head is pending and cannot authorize operation. |
| different Store V3 identity or scope | Reject before comparing revisions. |
| external finality unavailable, stale, ambiguous, or conflicting | Reject authority; retain local history only as authority-neutral state. |

An observed pending revocation prevents the earlier candidate from authorizing
new operation after local rollback. The pause remains until that revocation is
finalized or a separately governed recovery transition resolves the watermark.
An externally finalized terminal revocation permanently prevents the earlier
candidate from authorizing new operation.

## 5. Two-phase release transition

External consensus cannot participate in the local SQLite commit. Release
state therefore advances in two explicit phases:

```text
Phase A: authenticated SELECT or REVOKE event
  -> atomic local Store V3 commit
  -> pending release-state checkpoint
  -> no operational authority

Phase B: protocol-specific finality
  -> authenticate exact checkpoint commitment
  -> atomically persist exact finality evidence
  -> compare local head with finalized checkpoint
  -> anchored release-state prerequisite
```

The final authority-bearing economic transaction must consume the exact
anchored checkpoint identity and revalidate that the local release state has not
advanced or been revoked. A pending newer release event triggers a fail-closed
pause until its disposition is finalized.

## 6. Liveness and revocation latency

The policy must bound:

```text
maximum_external_finality_lag
maximum_pending_release_epochs
maximum_checkpoint_publication_retries
emergency_pause_on_finality_unavailability
```

Failing a bound pauses new authority. It never reuses an older finalized
candidate as a fallback after a locally authenticated revocation is pending.

## 7. Durable evidence

The release-state store must retain:

```text
exact release checkpoint bytes
exact external finality certificate bytes
exact protocol evidence bytes
finality policy bytes or governed identity
verifier-set identity and lifecycle
checker/verifier invocation evidence
external height and block identity
authenticated projection bytes
```

Every open, read, replay, and commit boundary revalidates canonical bytes,
cryptographic evidence, checkpoint linkage, local history equality, and all
false authority fields. Schema extension, missing rows, surplus rows, and
unreferenced evidence reject.

## 8. Required negative evidence

Tests must cover:

1. valid older database restored after a newer finalized checkpoint;
2. equal revision with a different state root;
3. different store identity or scope;
4. locally newer unfinalized SELECT;
5. locally newer unfinalized REVOKE;
6. conflicting finalized checkpoints at one sequence;
7. signer duplication, stale registry, insufficient quorum, and wrong payload;
8. external parent or height mismatch;
9. finality report Boolean substitution;
10. exact certificate, evidence, projection, and invocation-byte mutations;
11. crash before and after local event commit;
12. crash before and after finality evidence commit;
13. delayed finality beyond the governed lag bound;
14. authority-field promotion.
15. finalized selection `F1`, observed local revocation `R2`, restoration of
    local `L1`, and continued fail-closed pause due to watermark `W2`.

## 9. Explicit nonclaims

Until a concrete external protocol adapter, durable evidence store, and final
atomic consumer are implemented and independently replayed, V1 establishes no:

- externally governed trust-root authority;
- rollback protection;
- current-release authority;
- runtime or proof authority;
- settlement authority;
- production authority.

Hardware side-channel resistance, same-UID local path-substitution resistance,
and public data availability are separate obligations.
