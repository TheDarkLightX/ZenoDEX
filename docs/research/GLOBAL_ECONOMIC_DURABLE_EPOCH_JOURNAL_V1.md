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
- exact byte retry, including historical retry after later epochs;
- globally unique verifier commit identity across the activation history;
- typed stale-head and capacity no-ops;
- one transaction for epoch insertion and singleton-head update;
- `DELETE` journal mode, `synchronous=FULL`, strict tables, trusted schema off,
  an exact schema allowlist, and coherent transactional reads;
- complete store validation on create, open, read, and commit.

## Disaster-state evidence

The focused suite covers:

- canonical round trip and hostile frozen-object mutation;
- fully rehashed omission of balances, supplies, accounting locations,
  liabilities, reserves, replay state, terminal obligations, history, or
  outbox;
- repeated command bodies under distinct occurrences;
- exact retry, historical retry, stale competing successors, foreign CAS
  tokens, cross-instance races, and zero remaining capacity;
- schema expansion;
- exception recovery and abrupt process exit after begin, insert, head update,
  and commit-before-ack.

Recovery yields the complete pre-commit activation/head or the complete
post-commit epoch. The tests do not model every filesystem, storage controller,
kernel, or hardware power-loss behavior.

## Authority and nonclaims

The journal verifies structural and content bindings only. It does not verify a
RISC0 receipt, reconstruct verifier-owned route-binding roots, decide policy,
authorize a command, establish data availability or objective finality, deliver
an outbox item, reconcile an acknowledgment, or grant writer authority.

The current in-memory verifier/publisher and this durable journal remain
separate. Calling them sequentially would leave a two-phase crash window.
Production mounting therefore remains forbidden until one verifier-owned
publisher performs verification freshness checks and the durable CAS commit at
one controlled linearization point, while all alternative value writers are
fenced or retired.

Passing this slice narrows VM-10 durable-publication risk. It does not close
VM-09 sole-authority mounting, VM-10 external delivery refinement, VM-11 full
state completeness proofs, or VM-12 release evidence.
