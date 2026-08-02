# F08 plan: reopen and corruption fault campaign

Status: implemented and tested in the isolated public research slice.

## Objective

Ensure the reference recovery relation never converts a partial or crossed
durable layout into an accepted state. Only exact PRE, exact POST, or explicit
rejection/lock may emerge.

## Procedure

1. Validate the PRE and POST byte strings with the complete F04 fixed-point
   gate.
2. Require the reference pair to be distinct canonical layouts.
3. Compare observations byte-for-byte with PRE and POST before any partial
   reconstruction is exposed.
4. Send every other byte string through F04 and map rejection to a locked
   observation.
5. Reject a valid third fixed point as a non-serializable state.
6. Carry the fresh-authorization latch and movement denial on every successful
   or rejected observation.
7. Preserve a deterministic fault matrix and property campaign.

## Required evidence

- typed PRE, POST, rejected/locked, and setup-reject values;
- independent PRE/POST fixture and 31-fault vector;
- table, byte, selected-root, third-layout, and wrong-type witnesses;
- focused and property tests;
- Ruff, strict mypy, Python compilation, JSON, adjacent regression, and packet
  manifest validation.

## Nonclaims

The relation remains unmounted. Physical transactional atomicity and recovery
refinement are separate H-series obligations.
