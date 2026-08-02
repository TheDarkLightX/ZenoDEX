# E01 plan: authenticated request identity

Status: implemented and tested as a verifier-owned deterministic research
model; research-only and unmounted.

## Objective

Define a canonical retry identity that can only be derived from an
authenticated-command witness plus the current deployment, sequence, and
authority context. Close the identity codec against caller-mintable witnesses,
malformed roots, enum confusion, boolean-as-integer values, and width drift.

## Evidence

- the strict builder regenerates the authenticated-command and identity vector;
- same command/context values produce the same identity;
- command-root and sequence mutations change the identity;
- extra, missing, malformed, and boolean fields reject;
- public command and identity constructors reject without verifier-owned tokens;
- focused tests and strict Python quality gates pass.

## Nonclaims

E01 models the post-authentication verifier boundary. It does not implement a
cryptographic authenticator, authorize a commit, consume a nonce, provide a
concurrent transaction, mount an API, or move value. M6 remains research-only,
unmounted, and non-promotable.
