# Tau ADT/Table ZenoDEX Lab

Disposable shadow experiments for Tau 0.7.0-alpha. The current child campaign
pins IDNI/tau-lang at `1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43`
and the Taumorrow table demos at
`b149ca30f0143e3a4c31f0ce4fc4b5b75ff77c54`, including
`adt_tables_beyond_sql.tau`.

Nothing in this directory is an authorization-path claim. The tests probe which
ZenoDEX semantics can be expressed with current Tau ADTs and the table idioms from
`taumorrow/tau-lang-demos`.

The suite includes typed touched-state settlement witnesses, CPMM arithmetic,
nonce/replay boundaries, immutable intent relations, a bounded UPBA fill witness,
ZenoOracle median logic, 128/256-bit amount smoke tests, an append-only receipt
ledger, and a relation-table scaling benchmark.

## Beyond-SQL extension

The current Tau table model is algebraic rather than a mutable SQL engine:

```text
row       := one Tau fact
Table     := row_1 | row_2 | ...
SELECT(q) := q & Table
append    := Table | row
member    := row & Table' = 0
```

This is a strong fit for immutable ZenoDEX evidence: candidate sets, settlement
receipts, audit facts, replay witnesses, and policy/history ledgers. It is not an
overwrite table. If the same logical key is appended with conflicting content,
both facts remain; mutable account state must therefore keep using an explicit
state-transition model or a version/epoch key.

`09_upba_candidate_table.tau` models a complete tiny raw UPBA price grid as one
Tau value. It keeps denominator-zero rows present but invalid, proves selected
winner membership, proves absent out-of-grid lookup, checks score/dominance rails,
and records append idempotence, replica-order commutativity, monotone retention,
and the no-overwrite architectural control.

`10_epoch_bound_proof_receipts.tau` strengthens the upstream integrity-column
pattern. A receipt at epoch `t` is checked against the candidate table at
`t-1`; the selected candidate witness is met with the receipt to form a
proof-carrying value. A dangling or same-step-only reference collapses to `0`, so
the append-only receipt table cannot grow from it in the executable shadow model.

The intended research architecture is:

```text
host arithmetic / canonical commitments
        -> immutable Tau candidate facts
        -> prior-epoch SELECT / integrity witness
        -> proof-carrying Tau receipt value
        -> Lean theorem bridge for the bounded claim
```

Large arithmetic, hashing, signatures, canonical encoding, and production
settlement authority remain outside this lab.
