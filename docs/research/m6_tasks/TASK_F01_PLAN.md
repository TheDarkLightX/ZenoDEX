# F01 plan: define the authoritative history atom schema

Status: implemented and tested in the isolated public research slice.

## Objective

Define one typed, bounded, canonical atom that binds all durable transition
facts required by M6, including ANF, proof-context, E02 nullifier, authority,
receipt, replay, and outbox identity.

## Procedure

1. Define exact root, text, integer, enum, and collection boundaries.
2. Define nested nullifier and outbox projections with checked relations.
3. Require explicit proof-context presence semantics with a fixed no-context
   sentinel.
4. Encode the complete atom with canonical JSON and derive its root from the
   complete bytes.
5. Decode only exact canonical bytes into a complete value or typed rejection.
6. Add independent vector, round-trip, malformed-input, and crossed-lineage
   checks.

## Required evidence

- exact atom, nullifier, outbox, and configuration schemas;
- canonical codec and source-bound vector;
- strict decoder with typed rejection;
- focused tests and independent checker;
- mutation witnesses for omitted/crossed/unknown/noncanonical data;
- Ruff, strict mypy, Python compilation, and JSON validation.

## Nonclaims

F01 does not implement F02 canonical history materialization, F03 reopen,
production datastore behavior, authentication, proof verification, external
delivery, migration mounting, no-bypass coverage, accounting, backing, zUSD
safety, or value movement. M6 remains unmounted and non-promotable.
