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
no-effect observables, and a mutation-killing regression.

## Results

| Disaster state | Disposition | Closure or next invariant |
|---|---|---|
| Backend method replaced after binding admits a rejected receipt | `CLOSED_BOUNDED` | Retain and invoke the exact callable resolved at binding; regression proves the replacement is never called. |
| Private authority shape names an absent or coordinate-mismatched release | `CLOSED_BOUNDED` | Retain an owned registry snapshot, reselect the release, and compare every authority coordinate before backend execution. |
| Invalid WAL/schema store changes persistent journal mode before rejection | `CLOSED_BOUNDED` | Inspect existing mode and exact schema before persistent connection configuration; regression checks bytes, mode, and rows. |
| Activation commit succeeds and create acknowledgement is lost | `CLOSED_BOUNDED` | Verified-publisher create may recover only the exact canonical activation already stored. |
| Live hashes are refreshed while evidence still names an older commit | `CLOSED_BOUNDED` | Compare each mapped artifact with both the live scoped file and the exact Git blob at the declared subject. |
| Proof-admission source changes outside the durable publisher evidence map | `CLOSED_BOUNDED` | Bind `global_economic_proof_v1.py` in the durable publisher and publisher-bound evidence rows. |
| Old profile/store publishes after a separately committed migration | `OPEN_ARCHITECTURAL` | One durable current-authority head must fence profile, writer epoch, verifier release, deployment, and revocation generation. |
| In-flight old-profile verification publishes after rotation or revocation | `OPEN_ARCHITECTURAL` | Recheck the unified authority head after verification and inside the publication CAS transaction. |
| Caller supplies a same-process backend whose behavior is unrelated to claimed artifact bytes | `OPEN_DEPLOYMENT` | Use an OS-isolated measured verifier service with authenticated release selection and executable attestation. |
| Same-process code calls the private structural writer or mutates SQLite directly | `OPEN_DEPLOYMENT` | Give one isolated service exclusive database ownership; remove raw database access from command and worker processes. |
| Failure before SQLite activation initialization leaves an empty final path | `OPEN_CRASH_INSTALL` | Build and validate in a same-directory temporary file, durably install with no-replace semantics, and test the full fault matrix. |

The bounded closures reduce reachable disaster states in the unmounted Python
reference. They establish no Rust/RISC0 parity, real receipt replay, migration
authority, objective finality, outbox delivery, sole writer, or production
mount.

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
