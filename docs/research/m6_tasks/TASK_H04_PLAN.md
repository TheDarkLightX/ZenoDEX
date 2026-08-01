# H04 plan: post-crash canonical reopen

Status: implemented and tested in an isolated harness; research-only and
unmounted. H05-H08 remain pending.

## Objective

For every ordinary H03 publication crash point, launch a fresh Python worker
against a file-backed SQLite seed, inject the named fault, close the worker's
connection through process exit, reopen the database with a fresh connection,
and compare the complete `SQLiteStateV1` to independently prepared PRE and POST
states.

## Harness protocol

1. Build the deterministic D08 fixture and request.
2. Seed `seed.sqlite` with canonical PRE.
3. Prepare `post.sqlite` by running the same request without a fault and reopen
   it as the exact POST oracle.
4. Launch `python -m experiments.fcis_m6_h04_crash_recovery --worker ...` in a
   fresh child process.
5. Require worker exit code `73`, the dedicated H03 injected-crash code.
6. Reopen `seed.sqlite` from a new connection and run canonical `read_state`.
7. Compare the complete state, including all reconstructed rows and roots, to
   PRE or POST. Any third state, malformed state, or unexpected worker exit is
   `REJECTED`.

The post-COMMIT/pre-response point must classify as POST. Every earlier ordinary
publication point must classify as PRE. The four authority-helper-only H03
points remain outside this process matrix because the current D08 fixture does
not construct an authority-transition atom.

## Evidence boundary

H04 demonstrates process-level harness behavior and complete PRE/POST
classification for the declared finite fixture. It does not prove operating
system crash consistency under power loss, SQLite WAL/fsync durability,
production configuration, concurrent linearization, destination effects,
runtime reachability, or value movement. M6 remains unmounted and
non-promotable.
