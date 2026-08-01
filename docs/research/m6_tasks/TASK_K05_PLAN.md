# K05 plan: dynamic bypass mutants

Status: implemented and tested as a bounded research mutation matrix;
unmounted and non-promotable.

## Objective

For every K01 entrypoint, check the six required bypass mutations and preserve
the exact invariant that kills each one.

## Procedure

1. Regenerate the K01 entrypoint ID set and require its canonical fifteen rows.
2. Require a clean K03 protected-source scan before running the matrix.
3. Build one exact D08 acceptance witness, K02 port, and immutable pre-state.
4. Evaluate all six mutations for every entrypoint.
5. Route the current-root mutation through K02 and require `STALE_HEAD`.
6. Require every other mutation to produce its named missing-evidence or
   legacy rejection classification.
7. Require exactly 90 killed results and six results per entrypoint.

## Evidence boundary

K05 does not rewrite or execute production entrypoint source, prove dynamic
deployment reachability, or mount the unique commit port. It is a deterministic
contract/mutation model for the future integration campaign.
