# ZenoLacuna project workflow contract

This implements the first-release completion plan alongside the compatible v1
prototype. The project API is a local developer and agent workflow. Its effect
is an accepted, replayable project revision. It has no settlement authority.

The acceptance boundary is a public key pinned by the operator outside agent
proposal data. Ed25519 signatures bind the project, parent revision, action and
canonical payload. The owner signs initialization, revisions, cancellation and
resumption. Owner-issued delegates may answer, propose a candidate and request
verification for exactly the delegated scope. Signature verification establishes
key authorization under this host premise; it does not establish human intent.
Private keys and the independently distributed public-key pin must be protected
from proposal agents. A same-UID process with key access is outside that premise.

A revision explicitly replaces the full task. It binds the previous scope and
lists every retired or changed protected requirement. Changing the input or
observation interpretation conservatively retires the old protected clauses.
These are owner-approved contract changes, never evidence of preserving the old
contract. All old answers, candidates and completion results become historical.
The signed history and archived source bytes remain replayable.

Every source is an owned relative path and content digest. Supported adapters
are a closed registry: finite relations, restricted integer pipelines, and the
fixed signal migration machine. Data from agents cannot select an import or
executable. Runtime completion recomputes correspondence, independent finite
checks, and every external check required by the signed task. Stored report
fields alone cannot establish completion. Missing tools, unsupported domains,
stale sources and solver uncertainty prevent completion.

The public CLI starts an isolated worker with an empty bytecode-cache prefix.
A stdlib-only bootstrap binds the static local import closure, including package
initializers, before application imports. A later audit rejects dynamic local
imports outside that closure and `src`/`tools` modules with outside origins.
The signed checker identity hashes this complete closure. The selected ESSO
child also bypasses stale Python bytecode. The Python interpreter, standard
library, installed dependency infrastructure, operating system and integrity
of the bootstrap itself remain trusted host premises. Direct library callers
must keep installed code immutable for the entire process, including the period
before constructing a Project. A late file hash cannot authenticate previously
loaded Python functions.

ASSESS records model acceptance of a candidate; COMPLETE establishes the declared
runtime correspondence and required solver evidence. An omitted observation or
incomplete domain is reported as INCONCLUSIVE/UNKNOWN, and inspecting a candidate
under that declaration produces MODEL_OMISSION without changing the project.
Neither an inspected proposal nor a signed COMPLETE request is a certificate.

The project store uses SQLite transactions with rollback journaling and
`synchronous=FULL`. One transaction owns source blobs, the signed event and its
evidence. Readers reconstruct state from signed commands. The revision is a
digest of the entire signed command, and writes compare the expected parent
inside the transaction. An exact accepted duplicate is idempotent. A conflicting
answer cannot replace the original. Cancellation and revision invalidate late
work. Source edits are permitted only through an owner-approved successor task.

This is an explicit persistence-contract implementation of scenario S22: project
runs have no independently writable JSON current-pointer or partial semantic
record. SQLite recovers an interrupted uncommitted transaction to its previous
revision; a corrupt database fails closed. Successful commit durability assumes
the filesystem honors SQLite's locking and sync requests. An error after commit
may have an uncertain caller outcome; retrying the exact command is safe. The
v1 shell's separate record/pointer recovery tests remain regression evidence.

Two further explicit first-release wire/scope amendments apply to the original
acceptance inventory. S32 rejects a legacy simulated receipt envelope as
MALFORMED_APPROVAL at the signature decoder; a well-formed signed task attempting
to change REAL_OWNER to SIMULATED rejects AUTHORIZATION_PROFILE_MISMATCH. Neither
changes accepted history. S29 supports admission of complete opaque observations
and whole bounded traces into the assessed finite relation: 00 and 11 can be
allowed together while 01 rejects TRACE_NOT_ALLOWED. That operation asserts
finite model membership, not provenance of an observed execution. Generic
finite-state graph completion remains UNKNOWN without an adapter; the release's
actual signal migration graph has its own exhaustive runtime and ESSO parity
adapters. Bounded trace results never become unbounded claims.

Exported bundles describe exact historical snapshots. An operator expecting a
particular revision must supply its independently known expected revision to
replay. A valid old bundle is not evidence of the latest project head, and there
is no command that restores it over a live database. Restoring an old database
outside the tool's API also requires an external trusted latest-head record to
detect rollback; local signatures cannot prove freshness by themselves.

Preflight invariant: every accepted command has authentic, scope-bound approval,
and COMPLETE requires independently recomputed evidence for exact task and code.
Required valid states include authorized answers, explicit requirement retirement,
safe consumer-first migration, queued delivery, cancellation, rollback, revision
after source edits, and restart after a committed or aborted transaction.

Tests must observe exact rejection, unchanged signed history and source blobs,
and absence of external effects. The only outbox is the returned diagnostic;
the store executes no value-moving effects. Public output distinguishes model
closure, bounded runtime evidence, and installed external solver evidence.
