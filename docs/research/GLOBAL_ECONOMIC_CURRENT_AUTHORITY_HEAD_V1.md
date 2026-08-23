# Global Economic Current Authority Head V1

Status: `IMPLEMENTED_TESTED_DISCOVERY`

Production authority: `NONE`

This bounded slice adds one directory-scoped durable authority file whose
current head names exactly one epoch-store file for
`VerifiedDurableEconomicPublisherV1`. Its purpose is to make two bounded
disaster histories observable at the publication linearization point:

1. a retained old-profile store attempts to reopen after authority rotation or
   revocation;
2. an old-authority receipt verification begins before revocation and returns
   after revocation.

Both histories fail without adding an economic epoch when the explicit
authority update and publication use the same unchanged authority file and the
verifier-owned durable publisher path. Actual migration, backup rollback,
authority-file replacement, and copied deployment histories remain open.

## Authority value

`GlobalEconomicAuthorityHeadV1` commits:

- monotone authority generation;
- activation ID, chain ID, deployment root, and directory-local epoch-store
  root;
- profile root and writer epoch;
- verifier registry root, release ID, and measured binding root;
- root image ID; and
- exact `ACTIVE` or `REVOKED` status.

The authority root is content-derived from canonical, closed-field JSON.
Decoding rejects duplicate fields, unknown fields, noncanonical JSON, Boolean
integer aliases, unknown status values, malformed roots, and non-u64 epochs or
generations.

ABI V1 admits two adjacent transitions:

```text
ACTIVE -> REVOKED
ACTIVE -> ACTIVE with a new activation, profile, and next writer epoch
```

The second transition is a profile migration and may carry structurally
declared verifier coordinates for that new profile. This journal does not
authenticate that relationship. Verifier-only rotation is invalid. The
epoch-store root remains fixed. Revocation preserves every coordinate except
generation and status. Revoked is terminal in this bounded model.

## Durable publication protocol

All epoch database paths in one directory derive the same authority database
path:

```text
<deployment-directory>/.global-economic-authority-v1.sqlite
```

The verifier-owned publisher constructs the expected generation-zero authority
from the verified activation, active profile, bound verifier capability, and a
migration-stable root of the epoch file name. Create recovers only an exact
current authority. First installation builds and validates a private
same-directory SQLite candidate, fsyncs it, links it to the final name with
atomic no-replace semantics, fsyncs the directory, and removes the candidate.
A cooperating concurrent installer receives a typed bootstrap-busy exception.
An occupied final name without the exact reserved recovery pair is never
adopted. An exact current-UID `0600` two-name hardlink pair with the complete
expected sequence-zero store is recoverable regardless of its install
provenance; exclusive directory ownership is outside this shared-UID model.
Recovery requires Linux `O_PATH` and usable `/proc/self/fd`, otherwise it returns
a typed unsupported-platform rejection. Final stores require current-process
ownership, mode `0600`, and one filesystem link. A differently named second
epoch file derives a different epoch-store root and fails before its database
is created. Open checks the exact activation bundle and current authority.

The epoch journal attaches the authority database to the same SQLite connection.
Its CAS token snapshots both the economic publication head and authority
generation. `BEGIN IMMEDIATE` starts the publication transaction across the
main epoch database and attached authority database. Inside that transaction,
publication rereads and validates the complete authority history and requires:

```text
current.status = ACTIVE
current = publisher_expected_authority
current.authority_root = cas_authority_root
current.generation = cas_authority_generation
```

Failure returns `AUTHORITY_STALE`. Epoch history, current epoch head, receipts,
replay data, and outbox-containing bundle bytes remain unchanged. The attached
transaction serializes concurrent authority updates before or after epoch
publication; no authority update can linearize between the inner authority
check and epoch commit.

## Refactoring preflight and pattern record

- Authority owner: the shared authority journal owns current publication
  coordinates. The receipt verifier still owns proof acceptance. The epoch
  journal owns atomic economic publication.
- Construction: the publisher derives its expected authority from verified
  typed inputs. The journal snapshots canonical bytes before persistence.
- Commit point: SQLite `COMMIT` after authority validation, source-head CAS,
  complete epoch-bundle insert, and current-head update.
- CAS key: economic publication ID and sequence plus authority root and
  generation.
- Crash semantics: SQLite DELETE journal mode and FULL synchronization retain
  PRE or POST. A nonblocking advisory directory lock serializes cooperating
  installers, and the final pathname is installed without replacement. A
  candidate with no final link rejects without mutation. When final and
  candidate names are the same private inode, descriptor-bound validation of
  the complete expected sequence-zero store precedes candidate unlink and
  directory fsync. Lookalike inodes and semantic mismatches remain untouched.
  Hardware power-loss and noncooperating same-UID race matrices remain open.
- Retry: an exact epoch already present in validated durable history returns
  `ALREADY_COMMITTED` without mutation even after authority revocation. An
  unpublished epoch under stale or revoked authority returns
  `AUTHORITY_STALE`. An authority successor retry reports
  `ALREADY_COMMITTED` only when that successor is still current; older
  generations report `STALE_HEAD`.
- Representation: frozen typed authority values, canonical bytes, strict SQLite
  tables, exact schemas, closed transition classes, bounded history, and
  content-derived roots.
- Python enforcement: process-local privacy and file ownership only. Same-
  process code can still reach underscore-prefixed structural writers.
- Rust enforcement: absent for this slice.
- Migration implication: a production migration publisher must atomically
  commit its verified activation and the matching authority successor. That
  publisher is not implemented here.
- Compatibility implication: these constructors are fresh-install-only. A
  single-link current-UID store using the parent implementation's possible
  `0644` mode receives a typed migration-required rejection without `chmod` or
  content mutation. A future migration must validate a held descriptor before
  changing permissions; service-UID changes remain an operator migration.
- Emergency stop: each accepted active successor reserves one history row and
  sufficient byte capacity for its coordinate-preserving revocation.

The authority journal remains one cohesive commit adapter because schema,
history validation, locking, and CAS order form one crash/concurrency protocol.
Validation is split into schema, history, and current-pointer phases to keep
individual functions reviewable.

## Evidence obligations exercised

- canonical round trip and exact authority root;
- coordinate-preserving terminal revocation;
- rejection of mixed revocation, verifier-only rotation, and epoch-store
  switching;
- durable commit, reopen, and exact retry;
- deterministic concurrent authority, epoch, and verified-publisher creation,
  with one complete install plus typed bootstrap-busy rejection;
- no-replace rejection of occupied final names without an exact valid reserved
  recovery pair, including empty, valid-empty-SQLite, malformed, hardlinked,
  directory, and FIFO entries, without mutation;
- exact owner, `0600` mode, and single-link enforcement on reopen;
- typed non-mutating rejection of legacy `0644` authority and epoch stores;
- crash-left unlinked bootstrap-candidate rejection without deletion or adoption;
- descriptor-bound recovery after the install link, first directory fsync,
  candidate unlink, and second directory fsync boundaries;
- rejection without mutation of byte-identical separate inodes, wrong authority
  heads, and wrong activation bundles during linked-name recovery;
- prompt nonblocking rejection of paired FIFO recovery names;
- typed non-mutating rejection when Linux `O_PATH`, proc-descriptor reopen, or
  SQLite-through-procfs recovery is unavailable;
- explicit evidence that an exact current-UID prebuilt hardlink pair is
  recoverable at the cooperative research ceiling;
- stale historical-authority retry;
- one-row emergency-revocation reserve at the capacity boundary;
- pre-decode byte bounds;
- bounded, single-use process-local authority CAS tokens;
- competing authority successor CAS;
- unknown SQLite sidecar-table rejection;
- attached-database transaction serialization;
- rejection of a second named epoch store under one authority file;
- retained old-store reopen rejection after revocation;
- revocation during receipt verification returning `AUTHORITY_STALE`;
- exact committed-epoch retry after revocation returning historical success
  without changing epoch bytes;
- aggregate epoch-history byte rejection before bundle BLOB rows are fetched;
- unchanged epoch head and absent published record on rejection;
- existing epoch crash, retry, CAS, capacity, schema, and private-writer
  counterexamples.

The old-store and in-flight tests are requirement-linked negative regressions.
Removing the shared authority comparison or moving it outside the attached CAS
transaction causes these tests to expose an unauthorized epoch. Mutation
tooling was not run for this slice.

Four passing tests intentionally preserve open disaster states as executable
release blockers:

- restoring pre-revocation authority-file bytes reopens and publishes through
  the old writer;
- restoring only the epoch database to sequence zero under the unchanged active
  authority permits the same epoch publication to commit again;
- replacing the authority pathname with a revoked database leaves an already-
  open publisher attached to the detached active inode and able to publish; and
- committing the current separate migration journal leaves the old publisher
  able to publish.

Their passing result records reproducibility. It supplies no safety claim.

## Nonclaims and remaining gaps

- The authority journal does not authenticate governance or migration. Its
  successor hook is underscore-prefixed, unmounted, and remains reachable by
  same-process Python code.
- Migration activation and authority advance are not yet one atomic commit.
- A completed migration can coexist with an old publisher that still commits
  through an unchanged old authority file. No constructible successor publisher
  mounts the migrated generation.
- Copying or restoring both databases, restoring old authority bytes, or
  replacing an authority inode for an already-open process is not prevented by
  this reference design.
- Same-process private writer access remains a demonstrated release blocker.
- No OS-isolated sole writer, executable attestation, objective finality, real
  RISC0 replay, Rust parity, or production mount is established.
- Hardware power-loss install recovery, hostile same-UID namespace races,
  directory ownership and durability, legacy permission migration,
  backup/restore, and disaster recovery remain deployment obligations. The
  tested cooperating same-path race and process-level post-link crash points
  are bounded by advisory directory locking, descriptor-bound candidate
  validation, and atomic no-replace install.
- Descriptor-bound linked recovery is Linux/procfs-specific. A shared-UID peer
  can prebuild an exact accepted pair because no authenticated install-intent
  marker exists; production requires exclusive OS-level directory ownership or
  an authenticated intent mechanism.
- The tests are bounded evidence. They are not a proof of whole-economy value
  movement safety.

VM-08, VM-09, VM-10, VM-11, and VM-12 remain incomplete. Production readiness
and production authority remain closed.
