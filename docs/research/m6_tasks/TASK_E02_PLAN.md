# E02 plan: nonce/nullifier relation

Status: implemented and tested as a verifier-owned deterministic research
model; research-only and unmounted.

## Objective

Bind one verified E01 request identity to the next sender nonce and derive a
canonical nullifier from the exact deployment, sender, nonce, and command
family tuple.

## Contract

```text
current nonce = n
command nonce = n + 1
nullifier = H(deployment, sender, nonce, command family)
```

The domain separator, canonical field set, u64 bounds, closed command-family
enum, verifier-owned witness, and exact rejection behavior are frozen in the
E02 schema document and vector.

## Required evidence

- deterministic vector regenerated from the E01 source vector;
- exact next-nonce and overflow rejection;
- deployment, sender, nonce, and command-family mutation tests;
- strict missing/extra/Boolean/unknown-enum rejection;
- caller-minted and exact-class forged witness rejection;
- mutation invalidates verifier provenance;
- focused Python quality gates and packet manifest validation.

## Nonclaims

E02 does not implement cryptographic authentication, consume a production
nonce, enforce a database uniqueness constraint, provide concurrent CAS,
classify retries, mount a caller, or move value. M6 remains research-only,
unmounted, and non-promotable.
