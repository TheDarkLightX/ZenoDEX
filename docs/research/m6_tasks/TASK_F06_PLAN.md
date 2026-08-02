# F06 plan: require fresh reopened-head authorization

Status: implemented and tested in the isolated public research slice.

## Objective

Keep a canonically reopened process quiesced until an external authority has
approved the exact current head, then invalidate that approval whenever the
head changes.

## Procedure

1. Revalidate the F03 success and reopen its canonical bytes again.
2. Revalidate F05 genesis and require the reopened history's genesis state,
   configuration, and first authority root to match it.
3. Derive one head root over snapshot, state, authority, epoch, deployment,
   genesis, and external authorization roots.
4. Require external evidence to match every head field and its epoch window.
5. Call an external verifier before issuing the token.
6. Revalidate the exact head, evidence, epoch window, operation enum, and
   external verifier decision at every commit, acknowledgment, or migration
   use.
7. Preserve deterministic rejection witnesses for crossed evidence, forged
   token roots, changed heads, rejecting verifiers, and expired tokens.

## Required evidence

- typed head, evidence, token, use-success, and rejection values;
- source-bound head/evidence/token vector and independent checker;
- focused tests for issue, all operation kinds, wrong type, and expiry;
- deterministic property tests for generated token-root substitutions;
- Ruff, strict mypy, Python compilation, JSON, adjacent regression, and packet
  manifest validation.

## Nonclaims

F06 does not authenticate the verifier adapter, implement a production
configuration/quorum boundary, prove transaction durability, or enable value
movement. The token relation remains unmounted research evidence.
