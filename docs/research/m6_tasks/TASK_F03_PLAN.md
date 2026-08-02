# F03 plan: implement total fail-closed reopen

Status: implemented and tested in the isolated public research slice.

## Objective

Reconstruct one complete authorized history from canonical F02 layout bytes or
reject the layout without exposing partial authority.

## Procedure

1. Enforce exact input types, resource bounds, UTF-8, duplicate-key, and
   canonical-byte checks.
2. Decode every header and row family with closed fields, enums, bounds, and
   nested F01 validation.
3. Reconstruct the complete F02 history and replay its state/context/authority
   lineage.
4. Recompute all parallel projections through F02 `encode_history`.
5. Require exact whole-layout fixed-point equality.
6. Return only a complete success value or a stable typed reject.

## Required evidence

- partial reopen relation and typed reject codes;
- valid byte round trip and exact fixed-point result;
- corruption witnesses for missing, surplus, reordered, crossed, stale-root,
  malformed, noncanonical, and incomplete layouts;
- independent vector/checker and focused tests;
- Ruff, strict mypy, Python compilation, and JSON validation.

## Nonclaims

F03 does not implement physical datastore recovery, process-crash handling,
WAL/fsync durability, restart authorization, migration mounting, no-bypass
coverage, accounting, backing, zUSD safety, or value movement. M6 remains
unmounted and non-promotable.
