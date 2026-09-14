# Isolated custody publication V2

Status: implementation and bounded isolated tests. This is the W06 publication
consumer for the existing V2 custody transfer/managed-lifecycle core. It does
not qualify a guest, production ledger, migration or complete economic lane.

The owning API is `IsolatedCustodyPublisherV2.create/open`, with an independently
selected complete genesis pair and `CustodyPublicationConfigurationV2`.
`publish(candidate, request, receipt_bytes=...)` acquires the current
global and custody states itself. A caller cannot supply a replacement source
snapshot, verified handle or raw commit bundle.

`CustodyPublicationRequestV2` owns an exact context/command snapshot. The joint
publisher also accepts the existing `PerpsMarginRequestV2`; the custody-only
publisher rejects it. Publication defensively reconstructs each exact request
after authentication preparation, before receipt/profile checks and store reads.
Request construction grants no authority. The previous loose context/command
source API is removed; canonical request parts, request IDs, receipt frames and
retained publication records are unchanged. Historical verification remains
available through the same decoders and reconstructed requests.

```mermaid
flowchart LR
    A[Selected genesis and verifier configuration] --> B[One SQLite snapshot]
    B --> C[Pure custody transition and global refinement]
    C --> D[Selected signature and receipt verification]
    D --> E[Local commit closure]
    E --> F[Current authority and source comparison]
    F --> G[Atomic record and head commit]
```

## State and authority

Genesis stores the exact canonical global and custody state bytes. Decoding
reuses existing V2 decoders and checks the complete projection, including
physical holdings, retained custody rows and the enabled asset-lane root.
Genesis is an externally selected isolated initialization premise, without a
claim of certified initialization or ownership of live funds.

The separate V2 authority record commits to the genesis ID, chain, deployment,
directory-local store filename, profile, writer epoch, custody guest-role root
and signature-manifest root. Generation zero is ACTIVE. Its sole supported
successor is coordinate-preserving generation-one REVOKED. Revocation is
terminal in this format. Profile rotation and V1/V2 migration remain separate
obligations; no V1 bytes or historical decoder are changed.

Reopening requires the independently supplied genesis and configuration again.
It reconstructs the expected initial authority, validates history, and returns
a publisher only when the current authority is that ACTIVE value. Copying the
database under a different filename fails this store-selection binding. The
filename does not identify a host, backup or globally unique deployment.

## Publication and recovery

Each source read obtains both complete states, publication ID, sequence,
authority root and generation in one read transaction. These coordinates remain
local to the owning call. The economic commit closure is created only after the
profiled verifier returns. It accepts no caller-created record and never
escapes. This replaces a directly callable token-mint/raw-commit pair that
allowed unverified material to be published during development.

Under `BEGIN IMMEDIATE`, the closure validates the full store, recognizes an
exact committed retry, checks current authority and the acquired source, then
inserts the full record and updates the head. The one transaction owns economic
state, replay state and the retained receipt. The existing core preserves
custody, claimant rows, terminal obligations and outbox rows for these commands;
there is no external effect dispatcher in this isolated adapter.

Records contain the existing five-part guest input frame, exact statement,
authentication message, signature and receipt bytes. The publication ID hashes
these bytes and the sequence, predecessor publication ID and authority root.
The retained authority supplies the selected verifier roots without redundant
record fields. Pure replay derives the complete successor custody state and
checks the global successor and statement. Both state roots are consequently
recoverable and checked against the complete projection.

Economic `history_root` remains unchanged, as required by the existing refiner.
Publication ancestry is the separate record chain:

```text
record.source_publication_id = preceding publication ID
record.sequence              = preceding sequence + 1
replayed complete pre-state  = preceding complete committed state
current head                 = validated record-chain tip
```

The authentication message retains the existing domain and canonical closed
schema. Recovery checks its typed intent against the occurrence and command
body digest. Signature/receipt success is a publication-time premise. Recovery
does not reselect historical authorization registries or invoke BLS/RISC0. The
full authentication-candidate codec needed for independent historical
reselection is still absent.

| Outcome | Contract |
|---|---|
| COMMITTED | Complete record and head committed once |
| ALREADY_COMMITTED | Exact context, command, authentication message, signature and receipt match validated retained history; no new write |
| STALE_HEAD | Another source won; this attempt adds no economic change |
| AUTHORITY_STALE | Revoked or changed current authority prevents a new write |
| CAPACITY_EXCEEDED | Operational storage bound prevents a new write |
| Typed economic rejection | Existing core rejection, without record, replay or economic mutation |
| Indeterminate exception | Commit acknowledgment or rollback could not be resolved; retry/history is required |

An exact committed retry remains recognizable after revocation by an existing
publisher. A fresh writer open after revocation fails. A lost response after
COMMIT is classified as indeterminate rather than precommit rejection.

Bootstrap initializes a separate candidate under a directory lock, validates
the selected genesis, links it into the final name without replacement, and
fsyncs the directory before removing the extra candidate link. Retry validates
an interrupted candidate or exact two-link installation using retained inode
identity. Foreign candidates and final files are preserved. Ordinary open and
commit require owned regular 0600 single-link files and reject WAL/SHM artifacts.
SQLite uses DELETE journaling and FULL synchronization.

## Read-only historical audit

`IsolatedCustodyPublisherV2.audit` checks a retained database copy against
separately selected genesis, configuration, publication ID and authority root.
The copy must meet the existing ownership and layout checks, including the
original basename, because that basename participates in the authority identity.
The caller also supplies one historical authentication candidate per record.
Those candidates are untrusted policy witnesses: their prepared messages and
signatures must exactly equal the stored evidence and select the pinned profile.
Missing, duplicated or reordered witnesses do not substitute for the history.

The audit opens SQLite with `mode=ro`, reuses complete economic/lineage replay,
and closes the connection before verifier execution. Each retained occurrence
then passes the same measured signature and receipt admission used by publication.
No new journal fields, economic rules, format or commit function are introduced.
Success returns an ordinary detached snapshot. Revoked history remains auditable
without restoring writer authority; ordinary `open` retains its existing rules.

Checkpoint provenance remains the caller's responsibility. Recomputable local
hashes cannot authenticate a checkpoint, prove its freshness or prove finality.
For independent assurance, run the audit with trusted configuration and checkpoint
selection outside the proposer's trust domain. The development qualification tool
rechecks its fresh isolated history in the same process; it does not establish
that deployment separation. Verifier failure propagates without an audit result.
The audit describes the acquired snapshot, even if another writer later advances
the source. OS, native libraries, selected verifier evidence and data availability
remain explicit assumptions. It neither activates nor publishes anything.

Replay `tests/integration/test_isolated_custody_history_audit_v2.py` for exact
history, rehashed forgeries, checkpoint/witness failures, revoked history,
SQLite write refusal and interleaved margin/transfer evidence. Receipt protocol
fixtures remain distinct from real cryptographic receipt qualification.

## Bounds and nonclaims

This reference store admits at most 64 publication records and 64 MiB of record
components, with a 96 MiB physical-file ceiling. Input codecs retain their
existing individual byte bounds. Authority storage reserves its one revocation
successor independently of publication capacity. These are operational bounds,
without changes to token quantities, fees, rounding or economic policy.

The publisher process, verifier selection, SQLite and filesystem remain trusted.
Python privacy and a local closure do not protect against arbitrary in-process
introspection or direct database writes by a compromised process. Whole-file
rollback, multi-host clones, finality, data availability, deployment-wide writer
exclusion and destination enforcement require the remaining V3 work. A valid
old database can restore old authority in the absence of an independent anchor.
This is economic publication on isolated test state, not SHADOW observation.

The owning `publish` function retains its admission and nonescaping commit
closure together despite the normal function-length threshold. Extracting a
publicly callable raw record sink recreated an authority bypass. The bounded
transaction and rejection branches have dedicated stateful tests; no optimal
complexity or whole-program correctness claim follows from this arrangement.

Replay the focused Python tests in `test_global_economic_authority_head_v2.py`,
`test_asset_lane_custody_frame_decode_v2.py`,
`test_custody_publication_record_v2.py` and
`test_isolated_custody_publisher_v2.py`. The test-hygiene packet supplies exact
source pins, pytest nodes and executable semantic mutants. Receipt IPC fixtures
are not genuine proof evidence. Lean, ESSO, Kani, actual guest/image/receipt
qualification and production gates remain unrun for this slice.
