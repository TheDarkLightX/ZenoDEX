# G01 plan: define proof-context values

Status: implemented and tested in the isolated public research slice.

## Objective

Represent every proof-context authority dimension as one exact immutable value
with a deterministic root and closed epoch validity rules.

## Procedure

1. Use fixed digest fields for state, configuration, verifier key, and genesis
   authority roots.
2. Use bounded text fields for deployment, version, implementation, schema,
   and algorithm identifiers.
3. Use exact u64 epoch fields with explicit inclusive activation and expiry.
4. Derive the context root from all fields except the root itself.
5. Revalidate exact values at point of use and return typed rejection.
6. Keep value construction separate from proof verification and registry
   authority.

## Required evidence

- immutable typed context value and root builder;
- valid vector and independent checker;
- epoch-boundary, root-substitution, incomplete-object, and wrong-type tests;
- deterministic property tests for generated state-root substitutions;
- Ruff, strict mypy, Python compilation, and JSON validation.

## Nonclaims

G01 does not implement canonical bytes/Rust parity, a verifier registry,
public-input binding, proof verification, runtime mounting, or value movement.
