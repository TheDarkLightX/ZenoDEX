# FCIS M6 Task C07 Plan

TASK_ID: C07
TITLE: Produce an exact migration review packet

## Scope

C07 packages the tested, unmounted R03 migration carriers from C02 through
C06 and B09 into one independently recomputable review packet. The packet
must bind the complete old and new state bytes, roots, ordered entry map,
activation sequence, authority epoch root, Lean declaration digests, and
bounded Python/Rust/Julia parity evidence to exact local Git identities.

The packet checker reconstructs the C03 states, re-encodes their canonical
bytes, recomputes both state roots, verifies the C04 sign-dual transport,
round-trips the C03 migration manifest, verifies the selected C05 Lean
declaration spans, checks B09 result and artifact-index digests, and resolves
every declared commit/tree with local Git.

## Inputs

- C02 semantic key and canonical key codec.
- C03 typed state and migration manifest values/codecs.
- C04 retained sign-dual vector and transport checker.
- C05 Lean trace-conjugacy source and proof receipt.
- C06 rotation/reset evidence and dependency receipt.
- B09 parity result and artifact index.
- Exact source head and the recorded C02/C03/C04/C05/C06/B09 Git identities.

## Required outputs

- `TASK_C07_MIGRATION_REVIEW_PACKET.json`
- `experiments/fcis_m6_c07_review_packet_check.py`
- `TASK_C07_REVIEW_PROMPT.md`
- `TASK_C07_PLAN.md`
- `FCIS_M6_C07_MIGRATION_REVIEW_PACKET_SCHEMA_V1.md`
- `TASK_C07_REPORT.md`
- `TASK_C07_EVIDENCE.json`
- `TASK_C07_SOURCE_MANIFEST.sha256`

## Fail-closed checks

The checker rejects missing or changed source files, Git commit/tree drift,
state byte or root drift, changed ordered entry mappings, a non-sign-dual
target, a manifest that does not decode against the exact reconstructed
states, Lean declaration digest drift, B09 result/index drift, and any false
exact-byte parity flag. A successful packet check creates no authority
witness and performs no migration.

## Acceptance

```text
python3 -m experiments.fcis_m6_c07_review_packet_check
python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks C07
sha256sum --check --strict docs/research/m6_tasks/TASK_C07_SOURCE_MANIFEST.sha256
```

The focused C01-C04/C06 regression suite and the C05 Lean target must also
pass. The report must preserve exact implementation and receipt identities,
commands, evidence, nonclaims, and residual risks. C07 remains
`TESTED / UNMOUNTED`.

## Nonclaims

C07 does not authenticate an authority epoch, mount a runtime caller or
datastore, switch migration authority, establish destination idempotency,
prove production Python/Rust refinement, or move value. The C05 theorem is
machine-checked only over its declared research carriers. B09 parity remains
bounded executable evidence.
