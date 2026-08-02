# F04 plan: enforce the canonical fixed-point gate

Status: `GAP` in the isolated public research slice.

## Objective

Provide one narrow gate whose success requires complete F03 reopen followed by
independent F02 re-materialization and byte equality. Preserve a minimized
witness whenever the stronger all-table acceptance claim is not implied by the
current schema.

## Procedure

1. Accept only exact layout bytes at the public gate.
2. Reopen through F03 and retain typed rejection provenance.
3. Re-encode the accepted history independently through F02.
4. Require equal layout values, equal canonical bytes, and equal selected root.
5. Recompute the selected layout root for every mutation campaign input.
6. Exercise missing, extra, duplicate, reordered, and crossed row families.
7. Classify an unacknowledged committed outbox as pending delivery when the
   current schema permits it.

## Required evidence

- fixed-point gate and typed result;
- source-bound canonical vector;
- all-table mutation matrix with rehashed roots;
- explicit accepted pending-ack witness;
- focused tests, independent checker, Ruff, strict mypy, and compilation.

## Open repair

R10 or an authenticated prior-state layer must define whether an acknowledgment
is an optional current fact or a mandatory fact for a particular outbox. F04
cannot infer that policy from a single current layout without making a
caller-selected value authoritative.
