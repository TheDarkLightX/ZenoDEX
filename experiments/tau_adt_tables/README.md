# Tau ADT/Table ZenoDEX Lab

Disposable shadow experiments for Tau 0.7.0-alpha at source pin
`0ac2756fdff71338668bdeccd17b2a53e7be5198`.

Nothing in this directory is an authorization-path claim. The tests probe which
ZenoDEX semantics can be expressed with current Tau ADTs and the table idioms from
`taumorrow/tau-lang-demos`.

The suite includes typed touched-state settlement witnesses, CPMM arithmetic,
nonce/replay boundaries, immutable intent relations, a bounded UPBA fill witness,
ZenoOracle median logic, 128/256-bit amount smoke tests, an append-only receipt
ledger, and a relation-table scaling benchmark.
