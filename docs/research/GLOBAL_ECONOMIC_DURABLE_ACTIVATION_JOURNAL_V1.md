# Global Economic Durable Activation Journal V1

Status: `IMPLEMENTED`, `TESTED_DISCOVERY`, `UNMOUNTED`

Production authority: `NONE`

## Purpose

This bounded slice persists one complete global-economic genesis or migration
candidate bundle behind a SQLite compare-and-swap head. It addresses a narrow
durability prerequisite: after a deterministic failure around the transaction
boundary, reopening exposes one exact complete phase, `PRE` or `POST`.

It does not mount migration publication, verify a receipt cryptographically,
publish ordinary economic epochs, establish consensus finality, or retire any
legacy writer.

## ShapeForge world model

The refinement tuple for this slice is:

```text
Phi := <
  domain: global-economic-durability-v1,
  object: complete migration-activation bundle,
  states: PRE | POST,
  transition: initialize | CAS-activate | reopen | exact-retry,
  concurrency input: journal-minted CAS head token,
  hard guards: exact source activation, generation, profile, state,
               writer epoch, height, chain and deployment,
  observations: reopened head, complete bundle bytes, retry status,
  evidence class: tested discovery,
  excluded authority: receipt verification, epoch publication,
                      consensus finality, production mounting
>
```

The selected ShapeForge refinement tactic is
`refine_economic_evidence_into_publication_authority`. This implementation
stops before publication authority. It supplies a deterministic durable object
for a future verifier-owned publisher to consume.

## Preflight

Invariant owner:

```text
current_head = tip(complete_contiguous_activation_history)
```

For each successor `a[i]`:

```text
a[i].generation = a[i - 1].generation + 1
a[i].source_activation_id = a[i - 1].activation_id
a[i].source_profile_root = a[i - 1].profile_root
a[i].source_state_root = a[i - 1].state_root
a[i].source_writer_epoch = a[i - 1].writer_epoch
a[i].source_height = a[i - 1].height
```

Authority boundary: the token records one process-local CAS head snapshot. It
does not authenticate or authorize a writer. The journal retains an immutable
private copy of the token binding, so caller-visible fields cannot change the
expected head.

Evidence boundary: the designated preparation function runs structural
initial-state validation before bundle construction. The public decoded bundle
type independently rederives all head/body roots, so declared roots cannot
contradict retained bytes. The journal cannot prove that a caller used the
designated preparation function. It does not select a verifier or establish
that retained receipt bytes are valid.

External effects: SQLite configuration, transaction, commit and reopen belong
to the integration shell. Bundle preparation, hashing, framing and decoding are
deterministic core functions.

## Complete bundle

One activation ID commits a fixed-order tuple containing:

1. full profile envelope, including lane, coordinator and route registries;
2. economic policy registry;
3. complete global economic state;
4. complete predecessor state or canonical `null` for genesis;
5. initial-state source manifest;
6. initial-state certificate;
7. exact receipt bytes.

Each component is length-delimited and domain-separated under SHA-256. The
record contains every component root and byte count. The binary frame has one
magic value, one bounded canonical record, seven components in a closed order,
and no extension or trailing-byte channel. The total bundle is bounded to 16
MiB. The journal bounds history to 256 activations and total retained bundle
bytes to 256 MiB.

Bundle validation derives and compares the full registry roots, profile ID,
policy-registry root, target state root, predecessor state root and coordinates,
source-manifest coverage root, certificate root, receipt digest, and canonical
journal byte count. These checks establish internal byte/body consistency.
They do not establish economic validity or cryptographic receipt acceptance.

## Transaction behavior

Creation stores genesis, history and the singleton head in one transaction.
Migration activation uses `BEGIN IMMEDIATE` and performs these operations:

1. validate the complete existing history and current head in one SQLite snapshot;
2. classify any byte-identical historical target as `ALREADY_COMMITTED`;
3. compare the retained CAS token binding and all source coordinates;
4. reject projected row or byte capacity before insertion;
5. insert the complete immutable target bundle;
6. update the singleton head with an exact source-activation CAS;
7. commit under SQLite `synchronous=FULL` and `journal_mode=DELETE`.

A distinct proposal from a stale source returns `STALE_HEAD` without a row or
head change. A byte-identical retry after a lost acknowledgement returns
`ALREADY_COMMITTED`. The outcome separately reports the historical committed
activation and the current journal head.

Every public multi-query read runs inside one deferred SQLite read transaction.
Schema validation compares exact table DDL and checks `STRICT`, primary and
unique indexes, foreign-key integrity, `trusted_schema=OFF`, and SQLite's
integrity result.

## Disaster-state evidence

| Disaster state | Closure layer | Evidence |
|---|---|---|
| crash after transaction begin | SQLite rollback | reopen is exact `PRE` |
| crash after successor insert | SQLite rollback | no successor row remains |
| crash after head update before commit | SQLite rollback | head and history return to `PRE` |
| response loss after commit | exact content identity | reopen is `POST`; retry is `ALREADY_COMMITTED` |
| two writers share one source | source CAS plus retained token binding | one distinct successor wins; loser is no-effect |
| foreign or forged CAS token | process-local ownership registry | reject before transaction |
| stale head-pointer rollback | history-tip invariant | reopen fails closed |
| truncated or extended bundle | exact framing and component commitments | reopen fails closed |
| declared roots contradict component bodies | body-root rederivation | bundle construction and reopen reject |
| historical exact retry after later commits | immutable activation identity | `ALREADY_COMMITTED` plus distinct current head |
| row or byte capacity overflow | projected bound check in write transaction | typed no-effect capacity outcome |
| commit interleaves a multi-query read | deferred read transaction | reader observes coherent `PRE` or `POST` |
| added schema surface | closed SQLite object set | reopen fails closed |
| weakened `STRICT`, `CHECK`, or `UNIQUE` schema | exact DDL and pragma checks | reopen fails closed |
| generation overflow | u64 boundary check | successor construction rejects |

Tests use direct SQLite reads as an independent observable for row count, head
ID and exact stored bytes. The crash table is a fixed oracle: all injected
points before `COMMIT` must reopen `PRE`; the point after `COMMIT` must reopen
`POST`. The table runs once through exception rollback and once in child
processes that terminate with `os._exit` before Python can unwind or execute the
explicit rollback handler.

## Promotion boundary

This slice supports the following claim:

> A complete internally body-bound activation candidate can be checkpointed with
> deterministic SQLite PRE-or-POST recovery, exact retry classification, and
> process-local stale-head rejection in the tested environment. The designated
> preparation path additionally requires structural initial-state admission.

It does not support any of these claims:

- production publication authority;
- cryptographic validity of retained receipt bytes;
- proof that a caller used the designated structurally admitted preparation path;
- release-selected verifier or migration-image authority;
- durable ordinary epoch, effect, nullifier, receipt-history or outbox commit;
- objective consensus finality;
- hostile filesystem replacement resistance or hardware power-loss guarantees;
- complete source-to-target migration semantics;
- mounted writer rotation or retirement of legacy writers;
- safety of all ZenoDEX value movement.

VM-10 therefore remains open. This slice replaces one absent implementation
with bounded code and executable evidence; durable publication closure still
requires verifier-owned mounting and one transaction that includes ordinary
epoch state, history, nullifiers, receipts, release observations and outbox
rows.

## Reproduction

```bash
python3 -m ruff check \
  src/core/global_economic_durable_activation_v1.py \
  src/integration/global_economic_migration_journal_v1.py \
  tests/integration/test_global_economic_migration_journal_v1.py

TMPDIR=/dev/shm python3 -m pytest -q \
  tests/integration/test_global_economic_migration_journal_v1.py
```
