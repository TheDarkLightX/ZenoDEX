# E08 plan: public finite-state classifier model

Status: implemented and tested in the isolated public-model research slice.

## Objective

Provide a public exhaustive bounded model for concurrent commit/retry and
migration authority words. Preserve at-most-once nullifiers and monotone
quiescence/switch barriers in every reachable state.

## Procedure

1. Define a closed finite phase, state, action, and transition relation.
2. Give two competing commands one shared sender/nonce nullifier and one
   predecessor head.
3. Make successful publication atomic over head, commit ID, and nullifier.
4. Make exact retry and every rejected action explicit stutters.
5. Explore every action word through the declared depth using breadth-first
   search.
6. Check named invariants after every edge.
7. Construct minimized invalid witnesses for five semantic mutants.
8. Regenerate the source-bound vector and repeat the complete exploration.

## Required evidence

- closed action manifest and depth bound;
- reachable state and transition counts;
- zero invariant failures;
- named mutant kill list;
- repeatable independent checker and vector;
- focused tests, Ruff, strict mypy, and Python compilation.

## Nonclaims

E08 is a public finite-state model and does not prove the SQL adapter, a real
TLA/TLC run, production concurrency, migration mounting, runtime no-bypass
coverage, accounting, backing, zUSD safety, or value movement. M6 remains
unmounted.
