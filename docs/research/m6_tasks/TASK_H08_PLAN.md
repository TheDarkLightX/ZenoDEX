# H08 plan: independent exact-head atomicity review

Status: repaired and re-reviewed in the isolated adapter; research-only and
unmounted. The declared H08 attack matrix passes. Production approval remains
open.

## Objective

Independently attack the frozen H02/H03/H04/H06 research adapter at the exact
local head. The review must attempt split publication, stale CAS, phantom or
surplus durable rows, and crash mixtures. A passing review requires exact PRE
or POST recovery and no durable layout that the adapter accepts after any
attack.

## Review protocol

1. Use two file-backed connections to race the same pre-state request and
   require the second attempt to reject without changing the committed state.
2. Interrupt every ordinary H03 publication boundary and reopen the database
   through a fresh connection, comparing complete `SQLiteStateV1` values.
3. Delete one committed evidence row and insert one orphan evidence row with
   foreign-key enforcement disabled only to model hostile storage corruption;
   canonical reopen must reject both layouts.
4. Seed an unrelated authority row before initialization and require the
   initialization transaction to reject before writing snapshot metadata.

## Verdict boundary

The stale-CAS, ordinary crash, missing-row, surplus-row, and contaminated
initialization attacks pass. The repair checks every durable table before
writing and performs staged canonical reopen before commit. The former
contaminated-initialization witness remains as a regression test.

M6 remains unmounted and non-promotable. The review does not establish a
production datastore, filesystem power-loss semantics, destination delivery,
runtime caller coverage, migration, value movement, or zUSD safety.
