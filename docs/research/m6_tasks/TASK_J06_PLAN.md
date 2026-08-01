# J06 plan: quiescence enforcement

Status: implemented and tested as a deterministic research model;
research-only and unmounted.

## Objective

Close the final replay/current-head comparison interval with a canonical
quiescence witness. The witness is bound to the J04 migration manifest, the
K01 reviewed entrypoint inventory, the exact J02 QUIESCED authority epoch, the
activation sequence, and equal current/replay heads.

The admission function enumerates the in-scope K01 value-moving surfaces and
returns a typed state-preserving rejection for every writer attempt. The model
covers API, CLI, background delivery/recovery, migration, administrator,
legacy, outbox lease, and direct datastore adapter surfaces.

## Evidence

- the generated J06 vector is regenerated from J02, J04, and K01 dependency
  pins;
- 18 valid writer attempts (nine surfaces times legacy/target profile) reject;
- unknown surfaces and stale epoch/root/head/sequence witnesses reject;
- replay/current-head divergence and mutable accepted-result mutants reject;
- focused tests and strict Python quality gates pass.

## Nonclaims

J06 does not implement a production quiescence barrier, database transaction,
process shutdown protocol, dynamic call-graph audit, or deployment proof. J07
must bind the switch and stale-writer check atomically. M6 remains
research-only, unmounted, and non-promotable.
