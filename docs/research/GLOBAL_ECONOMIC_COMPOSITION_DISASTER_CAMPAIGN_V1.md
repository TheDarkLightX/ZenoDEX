# Global Economic Composition Disaster Campaign V1

Status: `TESTED_DISCOVERY`, unmounted.

Production authority: `NONE`.

## Bounded model

The campaign targets `global_epoch_receipt_admission` and the
verifier-to-publication seam. Each trace changes one primary axis while holding
the exact profile, release, backend, journal, capability, and durable source
coordinates observable.

```text
state   = profile + writer_epoch + verifier_release + deployment
        + registry + backend + journal_head + capability_set
actions = bind + verify + publish + rotate + revoke + reopen + retry
bad     = durable head advance without the exact currently authorized relation
```

The independent actors were a hostile deployment operator, a stale publisher,
a crash/retry operator, an evidence producer, and a hostile object supplier.
Each accepted finding required a concrete history, named invariant, exact
no-effect observables, and a negative regression. Mutation tooling was not run
for the current-authority slice.

## Results

| Disaster state | Disposition | Closure or next invariant |
|---|---|---|
| Backend method replaced after binding admits a rejected receipt | `CLOSED_BOUNDED` | Retain and invoke the exact callable resolved at binding; regression proves the replacement is never called. |
| Private authority shape names an absent or coordinate-mismatched release | `CLOSED_BOUNDED` | Retain an owned registry snapshot, reselect the release, and compare every authority coordinate before backend execution. |
| Invalid WAL/schema store changes persistent journal mode before rejection | `CLOSED_BOUNDED` | Inspect existing mode and exact schema before persistent connection configuration; regression checks bytes, mode, and rows. |
| Activation commit succeeds and create acknowledgement is lost | `CLOSED_BOUNDED` | Verified-publisher create may recover only the exact canonical activation already stored. |
| Matching activation already contains nonzero history not replayed by the new verifier | `CLOSED_BOUNDED` | Create recovery requires the exact sequence-zero activation head; nonzero history must use the separately reviewed open path. |
| Two first-time creators race and leak raw SQLite table-exists or lock-timeout failures | `CLOSED_BOUNDED` | A nonblocking advisory directory lock admits one private candidate installer and gives the loser a closed bootstrap-busy exception before SQLite connection setup. |
| First-create adopts a pre-existing final entry without the exact reserved recovery pair | `CLOSED_BOUNDED` | Build a private `0600` same-directory candidate, validate and fsync it, atomically link it to an absent final name, then require exact owner, mode, regular-file type, and one link on reopen. Occupied final names without the exact valid two-name recovery relation reject without mutation. |
| Crash-left WAL/SHM is checkpointed or deleted while open rejects | `CLOSED_BOUNDED` | Reject sidecars or a WAL database header before SQLite opens the store; preserve the complete tested file family. |
| Behaviorful `Path` subclass redirects recovery to another database | `CLOSED_BOUNDED` | Accept exact strings or the exact platform `Path` type and reconstruct an owned path before filesystem access. |
| Live hashes are refreshed while evidence still names an older commit | `CLOSED_BOUNDED` | Compare each mapped artifact with both the live scoped file and the exact Git blob at the declared subject. |
| Git replacement refs alter exact-subject blob lookup | `CLOSED_BOUNDED` | Resolve every evidence blob with replacement objects disabled. |
| Ledger retargets itself to another commit with the same mapped artifacts | `CLOSED_BOUNDED` | The checker pins the exact implementation subject; changing the subject requires a reviewed checker release. |
| Claim path escapes the repository or campaign/semantic anchors drift | `CLOSED_BOUNDED` | Pin exact contract paths, bind campaign and claim hashes, and compare all semantic anchors by exact type and value. |
| Unknown implemented-slice row or dirty live-gate dependency is accepted | `CLOSED_BOUNDED` | Enforce an ordered closed slice registry and bind every executed helper and consumed policy source to the exact subject before lazy import. |
| Proof-admission source changes outside the durable publisher evidence map | `CLOSED_BOUNDED` | Bind `global_economic_proof_v1.py` in the durable publisher and publisher-bound evidence rows. |
| Two differently named epoch databases publish independent sequence-one heads through one directory authority | `CLOSED_BOUNDED` | Bind the current authority to one migration-stable epoch-file root; the second verified publisher rejects before its database is created. |
| Active profile rotation consumes the final history slot and prevents emergency revocation | `CLOSED_BOUNDED` | Every active successor reserves one row and enough bytes for its exact coordinate-preserving revocation. |
| Historical authority generation is reported as a current exact retry | `CLOSED_BOUNDED` | `ALREADY_COMMITTED` requires the successor to remain the current head; older history returns `STALE_HEAD`. |
| Exact already-committed epoch retry is misclassified as a new write after revocation | `CLOSED_BOUNDED` | Resolve a byte-identical durable epoch before authority admission and return `ALREADY_COMMITTED` without changing epoch bytes; any unpublished epoch remains `AUTHORITY_STALE`. |
| In-flight old-profile verification publishes after explicit same-file rotation or revocation | `CLOSED_BOUNDED_DIRECTORY_LOCAL` | Snapshot the authority in the epoch CAS token and recheck the complete active head inside the attached SQLite publication transaction. |
| Oversized epoch history loads bundle BLOB rows before aggregate rejection | `CLOSED_BOUNDED` | Query count and aggregate stored-byte length inside the validation snapshot before selecting bundle rows; one-over capacity never reaches the row-fetch query. |
| Old profile/store publishes after a separately committed migration | `OPEN_ARCHITECTURAL` | Commit migration activation, matching authority successor, writer epoch, and old-writer retirement in one authoritative transaction. The executable blocker currently produces two successful commits. |
| Restoring pre-revocation authority bytes resurrects the old publisher | `CLOSED_BOUNDED_SHADOW_PORT` | `open_with_monotonic_anchor` compares the complete local authority and publication coordinates with an external-current checkpoint and rejects restored bytes without mutation. The result assumes an independently authenticated monotonic backend; unanchored APIs remain open. |
| Restoring only the epoch database to sequence zero permits duplicate publication under unchanged active authority | `CLOSED_BOUNDED_SHADOW_PORT` | The same exact checkpoint rejects a local tip behind the external publication sequence. Only a local tip exactly one epoch ahead may enter exact-retry recovery. A concrete independent backend and production selection remain absent. |
| SQLite epoch commit succeeds before external anchor CAS acknowledgment | `CLOSED_BOUNDED_ONE_STEP_RECOVERY` | Return a typed indeterminate committed outcome; admit only the anchored predecessor and exact already-committed epoch on retry; advance the external checkpoint after independent current read. Outage and stale-CAS histories leave one local epoch. |
| SQLite epoch commit succeeds and local anchor projection then fails | `CLOSED_BOUNDED_ONE_STEP_RECOVERY` | Install the exact predecessor recovery source immediately after `COMMITTED`; map every later preparation or CAS failure to typed indeterminate; the byte-identical retry advances only the anchor. |
| A concurrent exact local commit returns `ALREADY_COMMITTED`, then anchor projection fails | `CLOSED_BOUNDED_ONE_STEP_RECOVERY` | Arm the exact predecessor for every successful local outcome before projection; the next byte-identical retry advances only the anchor. |
| The lower journal commits SQLite and loses its acknowledgment before returning an outcome | `CLOSED_BOUNDED_ONE_STEP_RECOVERY` | Re-read durable authority, tip, and predecessor; arm recovery only for the exact one-epoch relation from the supplied source, otherwise preserve the original no-commit failure or reject divergence. |
| A process-control exception crosses the lower-journal boundary after SQLite commit | `CLOSED_BOUNDED_ONE_STEP_RECOVERY` | Attempt the same durable-head classification, preserve the original control-flow exception, and permit only the exact already-committed retry. If classification itself is unavailable, restart reconstructs the one-step relation. |
| A lower-journal exception occurs before SQLite commit | `CLOSED_BOUNDED_NO_EFFECT` | Re-read durable heads, preserve the original exception when no one-step commit exists, and keep the local and external heads unchanged. The publisher fault matrix covers begin, insert, and head-update boundaries. |
| External anchor CAS writes the exact successor and its confirming read loses acknowledgment | `CLOSED_BOUNDED_ONE_STEP_RECOVERY` | On retry, derive the sole successor from the retained predecessor plus current local authority and tip. Reconcile only byte-exact external equality; any other observed anchor rejects before receipt verification. |
| Another valid writer advances the anchor after a successful CAS but before its confirmation read | `CLOSED_BOUNDED_CURRENT_FORWARD_OBSERVATION` | Accept the installed successor or a later same-authority epoch observation with equal anchor/publication/height deltas; adopt a later tip only after its complete coordinates equal current local durable heads. |
| A confirmation read observes a forward external tip without the corresponding local durable history | `CLOSED_BOUNDED_FAIL_CLOSED` | Refuse adoption, return typed indeterminate for the locally committed epoch, and reject later value movement in that publisher session. Reconciliation requires an exact complete local/external history under the deployment recovery protocol. |
| Current V1 anchor sequence or publication height is exact u64 maximum | `CLOSED_BOUNDED` | A pure representability guard rejects before receipt verification and before the SQLite commit; exact historical retries remain available because they do not require another successor. |
| External backend returns truthy non-Boolean CAS or acknowledges without changing its current head | `CLOSED_BOUNDED` | Require exact `bool`, decode a fresh current observation after success, reject the unchanged predecessor, and require either the successor or validated forward epoch coordinates. |
| An already-open publisher keeps the replaced authority inode | `OPEN_DEPLOYMENT` | A retained executable blocker replaces the pathname with a revoked database while the open publisher commits through its detached active inode. Use exclusive service ownership, descriptor/inode binding, authenticated storage, and recovery fencing. |
| Same-process code invokes the private unauthenticated authority-successor hook | `OPEN_ARCHITECTURAL` | Construct successors only from proved governance or migration admission inside the sole publisher service. |
| Caller supplies a same-process backend whose behavior is unrelated to claimed artifact bytes | `OPEN_DEPLOYMENT` | Use an OS-isolated measured verifier service with authenticated release selection and executable attestation. |
| Retained callable object, closure, globals, or backend state changes semantics without changing identity | `OPEN_DEPLOYMENT` | Execute an immutable measured verifier artifact in an isolated service; Python identity checks remain defense in depth. |
| Same-process code calls the private structural writer or mutates SQLite directly | `OPEN_DEPLOYMENT` | Give one isolated service exclusive database ownership; remove raw database access from command and worker processes. |
| Process loss after link, first directory fsync, candidate unlink, or second directory fsync wedges a valid install | `CLOSED_BOUNDED` | Exact retry opens both names with Linux `O_PATH|O_NOFOLLOW`, requires one private two-link regular inode, reopens the held inode through procfs, validates the complete expected sequence-zero store, removes only the reserved candidate, fsyncs the directory, and requires the final descriptor to have one link. Paired FIFOs reject promptly; byte-identical separate inodes and wrong expected semantics remain untouched. |
| Power loss or a candidate-only crash leaves an ambiguous recovery family | `OPEN_CRASH_INSTALL` | Candidate-only state rejects without deletion or adoption. Hardware/filesystem durability, storage-fault, and operator-recovery matrices remain absent. |
| A parent-version `0644` store becomes unavailable after the private-store contract activates | `OPEN_DEPLOYMENT` | Exact single-link current-UID `0644` stores receive typed non-mutating migration-required rejection. This release is fresh-install-only until a descriptor-validated permission migration and service-UID transition procedure exist. |
| Linked-install recovery runs without Linux `O_PATH` or usable `/proc/self/fd` | `OPEN_DEPLOYMENT` | Return a typed unsupported-platform rejection without path-based fallback or mutation. Portability requires an equivalent descriptor-bound primitive before activation on another platform. |

The bounded closures reduce reachable disaster states in the unmounted Python
reference. They establish no Rust/RISC0 parity, real receipt replay, migration
authority, objective finality, outbox delivery, sole writer, or production
mount.

The cooperating same-path first-create race is serialized before SQLite opens
through a nonblocking advisory directory lock. Final installation uses a
private candidate and atomic no-replace link. Exact linked-name process-crash
states have descriptor-bound recovery. Candidate-only and hardware power-loss
histories remain open. A noncooperating same-UID process can still race names,
and an already-open inode can diverge from its pathname. Exclusive service
ownership, persistent descriptor binding, legacy migration, and
filesystem-level fencing remain deployment requirements.

## Scaled campaign design

Future waves use a fixed two-stage funnel:

1. Discovery workers receive disjoint primary axes and overlapping authority
   seams. Their outputs are structured histories only.
2. The main implementation lane reproduces each history, adds failing evidence,
   applies one closure, and preserves the negative test.
3. Review workers attack the immutable candidate, evidence checker, lifecycle
   model, and claim wording independently.
4. A deterministic gate accepts a wave only when every finding is classified as
   `CLOSED_BOUNDED`, `OPEN_ARCHITECTURAL`, `OPEN_DEPLOYMENT`, or
   `REFUTED_WITH_EVIDENCE`.

Scaling width comes from partitioning axes such as identity, order, time,
resource limits, restart, upgrade, revocation, encoding, and external effects.
Scaling depth comes from longer histories and cross-seam composition. Every
additional state variable must have one canonical owner and one promotion gate.
