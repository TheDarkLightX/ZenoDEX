# J05 plan: shadow replay and dual check

Status: implemented and tested as a deterministic research model;
research-only and unmounted. J06-J09 remain pending.

## Objective

Make target shadow output non-authoritative and allow phase progression only
after either exact result equality or the one explicitly declared reviewed
refinement relation. A mismatch becomes retained divergence evidence and
blocks progression.

The model binds shadow output to the J04 manifest root, activation sequence,
target profile, and target result root. The dual checker recomputes relation
roots and rejects foreign profiles, sequence crossings, forged relation roots,
unknown comparison modes, and authoritative shadow outputs.

## Evidence boundary

J05 is a bounded replay/comparison model. It does not run a production target
replay, prove the reviewed refinement relation for real state, implement phase
advance, mount migration authority, or prove datastore, runtime, no-bypass,
accounting, backing, or zUSD behavior. M6 remains unmounted and
non-promotable.
