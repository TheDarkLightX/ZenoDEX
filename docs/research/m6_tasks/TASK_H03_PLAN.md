# H03 plan: deterministic logical crash instrumentation

Status: implementation in progress; research-only and unmounted.

## Objective

Expose deterministic, one-shot fault hooks at every logical publication
boundary named by the M6 taskbook. The hook must raise a dedicated crash
surrogate that the publication path does not translate into a typed rejection.
The later H04 task will close the connection/process and classify the reopened
layout as exact PRE, exact POST, or rejection.

## Hook contract

`H03CrashPointV1` is the closed registry of crash points. `H03FaultHookV1`
selects one point and raises `H03InjectedCrash` exactly when that point is
reached. No hook is installed by default. Invalid hook types fail closed before
`BEGIN IMMEDIATE`.

The publication path covers:

- before and after `BEGIN IMMEDIATE`;
- before the SQL CAS and after a successful CAS row-count check;
- before and after each logical atom, evidence, nullifier, outbox, and ANF
  insert;
- before `COMMIT` and after `COMMIT` before the response.

The optional authority-successor helper also covers its epoch and allowed
writer inserts. The D08 fixture intentionally exercises the ordinary
publication path; the authority helper is tested directly because D08's
current verifier fixture binds the atom to the existing authority epoch.

## Determinism and cleanup

The selected point is an immutable enum value. A fresh connection and the same
request reach the same point. H03 tests explicitly roll back a still-open
transaction after catching the surrogate. H04 remains responsible for a fresh
connection/process reopen and exact PRE/POST comparison.

## Evidence boundary

H03 proves deterministic hook reachability and repeatability in the isolated
adapter. It does not prove operating-system process termination, SQLite
filesystem durability, WAL/fsync behavior, power-loss recovery, concurrent
linearization, or production configuration. M6 remains unmounted and
non-promotable.
