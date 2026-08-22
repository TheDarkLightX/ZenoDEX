# Global Economic Durable Epoch Journal V1

Status: `IMPLEMENTED_TESTED_DISCOVERY`, unmounted.

Production authority: `NONE`.

## Obligation

Persist one ordinary whole-economy epoch as one immutable unit and advance its
head at one SQLite transaction boundary. The persisted unit contains the exact
epoch certificate, canonical global effect plan, complete post-state, command
body hashes, published record, release observation, and raw receipt bytes.

The complete post-state includes balances, supplies, every named accounting
location, liabilities, reserves, Oracle occurrences, replay state, terminal
obligations, history root, and external outbox rows.

## Boundary

`DurableEconomicEpochMaterialV1` owns the exact publisher output. Preparation
snapshots each typed value, validates source, profile, height, state, body,
effect, receipt, data-availability, finality, and release-observation bindings,
then emits a content-derived canonical byte bundle.

The decoder rejects unknown or duplicate fields, noncanonical JSON, truncation,
trailing bytes, non-succinct receipt declarations, invalid proof-shape bounds,
missing complete-state fields, inconsistent derived roots, and malformed array
cardinalities. Distinct command occurrences may carry identical command-body
hashes; occurrence and route identities remain unique.

`GlobalEconomicEpochJournalV1` begins from one exact durable genesis or
migration activation bundle. For that activation it stores a bounded,
contiguous ordinary-epoch history with:

- a journal-minted process-local CAS snapshot token;
- a separate data-slot-free write capability bound to the exact journal
  instance;
- owned activation snapshots and exact activation/epoch head resolution from
  one validated SQLite read snapshot;
- exact byte retry, including historical retry after later epochs;
- globally unique verifier commit identity across the activation history;
- typed stale-head and capacity no-ops;
- one transaction for epoch insertion and singleton-head update;
- `DELETE` journal mode, `synchronous=FULL`, strict tables, trusted schema off,
  an exact schema allowlist, and coherent transactional reads;
- open-time validation checks the existing journal mode and exact store before
  applying persistent connection configuration;
- the verified-publisher factory recovers an exact already committed activation
  when create acknowledgement is lost;
- complete store validation on create, open, read, and commit.

## Disaster-state evidence

The focused suite covers:

- canonical round trip and hostile frozen-object mutation;
- fully rehashed omission of balances, supplies, accounting locations,
  liabilities, reserves, replay state, terminal obligations, history, or
  outbox;
- repeated command bodies under distinct occurrences;
- exact retry, historical retry, stale competing successors, foreign CAS
  tokens, forged or foreign write capabilities, cross-instance races, and zero
  remaining capacity;
- an executable negative witness preserving the underscore-prefixed
  same-interpreter structural-writer bypass as a release blocker;
- schema expansion;
- WAL plus schema-expansion rejection without changing the tested main database
  bytes, journal mode, or stored rows;
- exact verified-publisher activation retry after commit-before-ack;
- exception recovery and abrupt process exit after begin, insert, head update,
  and commit-before-ack.

Recovery yields the complete pre-commit activation/head or the complete
post-commit epoch. Direct create remains strict, and failure before the initial
SQLite transaction can leave an empty target; atomic temporary construction and
no-replace installation remain open work. The tests do not model every
filesystem, storage controller, kernel, or hardware power-loss behavior.

## Authority and nonclaims

The journal verifies structural and content bindings only. It does not verify a
RISC0 receipt, reconstruct verifier-owned route-binding roots, decide policy,
authorize a command, establish data availability or objective finality, deliver
an outbox item, reconcile an acknowledgment, or grant writer authority.

`VerifiedDurableEconomicPublisherV1` now owns one unmounted path from a
profile-governed, release-bound verifier capability through exact
source/body/effect binding and internal bundle derivation to this journal's CAS
transaction. Verification has no durable side effect, and SQLite remains the
publication linearization point. The journal exposes no public ordinary-epoch
commit method. Its module-private factory mints a same-process, instance-bound
write capability for the publisher. Python module privacy is an engineering
interlock and does not establish an OS or cryptographic writer boundary. The
underscore-prefixed structural commit method remains directly callable by code
already executing in the same interpreter and is retained in the writer
inventory as a release blocker.

Production mounting remains forbidden. The verifier release and supplied
artifact bytes are bound in process, while deployed executable loading,
attestation, and real RISC0 receipt replay remain absent. Alternative value
writers are not fenced, migrations and outbox delivery remain outside this
publisher, and Rust/RISC0 runtime parity is incomplete.

Passing this slice narrows VM-10 durable-publication risk. It does not close
VM-09 sole-authority mounting, VM-10 external delivery refinement, VM-11 full
state completeness proofs, or VM-12 release evidence.
