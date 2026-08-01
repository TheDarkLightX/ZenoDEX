# H06 plan: fail-closed SQLite durability configuration

Status: implemented and tested in an isolated checker; research-only and
unmounted. H05 and H07-H08 remain pending.

## Objective

Record and check the SQLite settings assumed by the isolated atomic-publication
model. A weak or ambiguous configuration returns a typed rejection. The checker
does not silently repair a production connection.

## Required profile

```text
file-backed main database
journal_mode = WAL
synchronous = FULL (SQLite value 2)
foreign_keys = ON (SQLite value 1)
busy_timeout >= 5000 ms
locking_mode = NORMAL
```

`configure_sqlite_durability` is a research fixture helper that applies this
closed profile and then invokes the same checker. Production startup must use a
reviewed deployment adapter and fail closed on any mismatch; H06 does not mount
one.

## Negative evidence

The focused suite weakens each required setting independently and checks the
named rejection: journal mode, synchronous level, foreign-key enforcement,
busy timeout, and locking mode. In-memory databases and open transactions are
also rejected before configuration.

## Evidence boundary

H06 establishes configuration-observation and fail-closed checker behavior in
the local SQLite environment. It does not prove filesystem durability, WAL or
fsync semantics under power loss, PostgreSQL equivalence, deployment startup
coverage, concurrent linearization, or value movement. M6 remains unmounted and
non-promotable.
