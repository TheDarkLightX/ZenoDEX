# J06 plan: quiescence enforcement

Status: implemented and tested as a deterministic research model;
research-only and unmounted.

## Objective

Close the final replay/current-head comparison interval with a canonical
quiescence witness. The witness is bound to the J04 migration manifest and
complete replay-evidence root, the K01 reviewed entrypoint inventory, the
exact J02 QUIESCED authority epoch and both writer-profile roots, the
activation sequence, and equal current/replay heads and durable snapshots.

The admission function enumerates the in-scope K01 value-moving surfaces and
returns a typed state-preserving rejection for every writer attempt. Each
result carries a canonical root over the complete attempted sequence, expected
head, authority root, epoch, command, publisher, and writer profile. The model
covers API, CLI, background delivery/recovery, migration, administrator,
legacy, outbox lease, and direct datastore adapter surfaces.

## Evidence

- the generated J06 vector is regenerated from J02, J04, and K01 dependency
  pins when those pins agree;
- gate and result witnesses require verifier-owned construction tokens and the
  gate is revalidated against verifier provenance at point of use;
- 18 valid writer attempts (nine surfaces times legacy/target profile) reject;
- unknown surfaces and stale epoch/root/profile/head/sequence witnesses reject;
- malformed root bodies and unequal snapshots reject;
- replay/current-head divergence, mutable accepted-result, changed-attempt
  identity mutants reject;
- an exact-class `object.__new__` forged gate is rejected at the admission
  boundary;
- strict Python quality gates pass; the current full receipt is blocked by the
  pre-existing K01 inventory-root drift.

## Nonclaims

J06 does not implement a production quiescence barrier, database transaction,
process shutdown protocol, fresh replay execution, dynamic call-graph audit,
or deployment proof. Equal current/replay heads and snapshots are configured
or derived model premises. J07 must bind the switch and stale-writer check
atomically. M6 remains research-only, unmounted, and non-promotable.
