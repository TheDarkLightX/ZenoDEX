# F05 plan: bind authenticated genesis

Status: implemented and tested in the isolated public research slice.

## Objective

Prevent a caller-selected empty or foreign history from becoming the starting
authority by requiring one root-bound genesis value to match a deployment-pinned
genesis relation.

## Procedure

1. Bind chain and deployment identity, initial state and configuration roots,
   authority profile, history schema, proof-context policy, and migration policy
   into one immutable genesis value.
2. Derive `genesis_root` from every governed genesis field.
3. Represent the deployment expectation as a separate pin with a root derived
   from all repeated expected fields and its activation epoch.
4. Revalidate both values at the relation boundary and compare every field,
   including the genesis root and authority profile identity.
5. Return typed rejection for wrong types, forged roots, crossed roots, state,
   chain, authority, schema, proof-policy, and migration-policy mismatches.
6. Run deterministic property mutations over generated initial-state roots.

## Required evidence

- immutable genesis and deployment-pin values;
- independent checker and source-bound root vector;
- focused tests for matching, foreign, forged, and wrong-type inputs;
- deterministic property tests for generated state-root substitutions;
- Ruff, strict mypy, Python compilation, JSON, broad M6 regression, and packet
  manifest validation.

## Nonclaims

F05 does not authenticate the origin of the deployment pin, implement a signer
or quorum, issue the F06 reopen-head token, prove a datastore layout, or mount
runtime value movement. The pin is a deployment-owned input premise for this
research slice.
