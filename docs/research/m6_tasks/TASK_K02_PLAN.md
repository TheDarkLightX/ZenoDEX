# K02 plan: unique publication capability

Status: implemented and tested as a deterministic research model;
unmounted and non-promotable.

## Objective

Define one narrow publication edge that consumes only a verifier-produced D08
acceptance witness. The witness owns the complete immutable publication atom;
K02 derives every publication field from that aggregate and revalidates D08
provenance at use. Return a new immutable port state or a typed rejection. Keep
side-effect adapters out of core and record the dependency policy that K03 will
enforce structurally.

## Procedure

1. Use the existing controlled D08 acceptance witness as the only request
   input type.
2. Require the D08-owned publication aggregate and derive exact bounded roots,
   sequence, and immutable request fields from it.
3. Construct one module-owned singleton port with a private construction token.
4. Reject arbitrary port objects, caller-minted port tokens, raw ANF objects,
   malformed current state, stale heads, sequence crossings, and commit
   fingerprint collisions.
5. Revalidate D08 provenance, then recompute request, response, and
   successor-head roots at the port boundary.
6. Return `NEWLY_COMMITTED` or `ALREADY_COMMITTED` with the exact state, or a
   typed rejection with no state-changing result.
7. Classify malformed current state as `WRONG_STATE` and malformed caller input
   as `WRONG_REQUEST` before evaluating publication relations.
8. Preserve dependency rules as a closed JSON input for K03.

## Evidence boundary

K02 does not prove the production port is unique, does not run a datastore,
does not perform an AST/Rust reachability audit, and does not mount any API,
worker, migration, recovery, or value-moving path. Those obligations remain
K03-K08 and the R13 whole-system work.
