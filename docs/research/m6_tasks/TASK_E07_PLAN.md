# E07 plan: transport-loss campaign

Status: implemented and tested in the isolated E05/E06-dependent research
slice.

## Objective

Keep transport uncertainty outside the durable outcome algebra. After each
loss point, perform a fresh E04 lookup and classify the exact durable state.

## Procedure

1. Build one verifier-owned E05 request with a canonical predecessor and
   successor.
2. Simulate loss before server entry and after validation without invoking the
   transaction.
3. Simulate loss after commit and after response generation by suppressing the
   returned E05 receipt.
4. Use a fresh E04 state/receipt subject for each lookup.
5. Blindly retry the original request and require one commit for PRE losses and
   stale rejection for POST losses.
6. Reopen row counts and replay the campaign twice for byte equality.

## Required evidence

- all four loss points are closed and ordered;
- PRE losses resolve to `ABSENT_RETRYABLE`;
- POST losses resolve to `ALREADY_COMMITTED`;
- all lookups retain `INDETERMINATE` client knowledge;
- blind retries never create a second semantic publication;
- vector/checker, focused tests, Ruff, strict mypy, and compilation pass.

## Nonclaims

E07 is a deterministic transport-shell model. It does not prove real network
behavior, process crash behavior, filesystem durability, production datastore
isolation, runtime reachability, destination idempotency, migration authority,
accounting, backing, zUSD safety, or value movement. M6 remains unmounted.
