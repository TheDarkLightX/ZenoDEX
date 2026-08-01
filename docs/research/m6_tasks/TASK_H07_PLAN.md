# H07 plan: abstract-to-SQL transaction refinement

Status: implemented and tested in an isolated research adapter; unmounted and
non-promotable. H08 and the later outbox, migration, no-bypass, and accounting
waves remain pending.

## Objective

For every abstract Durable Retraction Algebra (DRA) action, name the concrete
H02 SQLite transaction or the exact reason a production refinement remains
open. The matrix is a fail-closed registry. It must cover initialization,
reopen, publication, authority append, acknowledgment, retry, crash recovery,
durability configuration, and effect delivery.

## Matrix contract

Each action row records:

```text
abstract action
status
SQL transaction or absent operation
isolation assumptions
uniqueness constraints
recovery behavior
test evidence
nonclaims
```

The checker rejects missing action IDs, duplicate rows, unknown statuses,
missing fields, empty evidence/nonclaim lists, and type-invalid transaction
descriptions. The required action registry is closed in this version.

## Evidence boundary

H07 demonstrates that the isolated H02/H03/H04/H06 research artifacts have a
complete abstract-action mapping or an explicit open nonclaim. It does not
implement a destination worker, retry classifier, production datastore,
authority-transition fixture, startup durability binding, concurrent
linearizability proof, mounted caller, migration, value movement, or whole-
system zUSD safety theorem. M6 remains unmounted and non-promotable.

