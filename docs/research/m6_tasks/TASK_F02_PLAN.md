# F02 plan: implement one canonical history encoder

Status: implemented and tested in the isolated public research slice.

## Objective

Materialize every authoritative durable row from one complete F01 history
through one source-owned encoder. Preserve complete atom bytes, exact row
counts, canonical order, authority lineage, nullifiers, outbox ancestry, and
acknowledgment provenance.

## Procedure

1. Define the typed authorized-history source and authority/ack rows.
2. Validate the F01 atom chain, deployment/verifier context, authority roots,
   writer set, commit IDs, nullifiers, effects, and acknowledgments.
3. Derive the singleton header and every parallel row family in `encode_history`.
4. Retain complete canonical atom bytes in history rows.
5. Check exact order, counts, projections, and the complete layout root.
6. Add deterministic vectors and mutations for missing, reordered, stale, and
   crossed rows.

## Required evidence

- source and layout schemas;
- one public `encode_history` materializer;
- exact row-family types and canonical codec;
- independent vector/checker and focused tests;
- mutation witnesses for row omission, count drift, reordering, authority
  crossing, outbox crossing, and root substitution;
- Ruff, strict mypy, Python compilation, and JSON validation.

## Nonclaims

F02 does not implement F03 reopen, physical datastore storage, crash recovery,
transaction isolation, authentication, external delivery, migration mounting,
no-bypass coverage, accounting, backing, zUSD safety, or value movement. M6
remains unmounted and non-promotable.
