# Perps margin lifecycle: independent scoped review

Implementation subject: `88c9f27d992cb57664870887542e379f91c1e0fa`.
Evidence: [source pins, commands, failures and bounds](perps_margin_lifecycle_v1_20260912.json).

Astra independently selected the settled margin-account lifecycle and reviewed
the Lean model. Daybreak independently reviewed runtime effect ownership,
state reconstruction, guard priority, mutation quality and the inherited golden
failure. Both issued scoped acceptance. They reviewed source and parent results;
they did not independently rerun the final suites. Root implemented and replayed.

Reviewed Lean SHA-256:
`875d0cd04d05777c1ccea718706cc047ea9e7621ae4fcace8d8165b9ca4d7fae`.
Final harness SHA-256:
`31536aa1980daf8876a1cadfc2682fd5cf87cdaf6cabf697d48436b65b9c46af`.
The evidence file also pins the native driver, production implementations,
reused fixtures and repaired coordinator test.

## Corrections accepted before integration

- Account selection is explicit. The absorbing history theorem restricts every
  command to the same account; it does not prove arbitrary market lookup.
- Close derives an open, already-flat, empty pre-account, the exact nonce
  successor and tombstone. It neither closes a position nor silently drains it.
- The liveness theorem derives withdrawal and close under explicit amount and
  nonce capacity, matching subject, available market mode and absent Oracle.
- Independent runtime assertions protect every sibling account, market field,
  exact effect principal/domain/delta, occurrence and terminal row. The accepted
  64th-account case has 63 siblings, so frame preservation is exercised.
- Six executable mutations each change one source site. The mutant must import
  and return a typed accepted result before the semantic oracle rejects it.
- The same-market history uses only actual accepted transitions. Separate
  supplied-state cases cover `DRAIN_ONLY`; governance authority is not modeled.
- Commit `06ecdc30d` changed the shared Oracle fixture's occurrence and updated
  the Rust vectors. Two Python hashes were missed. Source-history inspection and
  matching Rust replay justify the two-string repair. Economic assertions and
  production source remain unchanged.

## Verification and assessment

Final evidence: eight formal/differential/mutation tests passed in 29.66 seconds;
49 Python core/coordinator tests passed; 18 Rust margin tests and the exact Rust
coordinator vector passed. The fresh Lean closure checks six independently typed
theorem consumers and their axioms. All 38 static outcomes and seven history
attempts agree across the selected-account model and both actual runtimes at
their declared observation levels.

Astra recommended the following fixed-rubric amendment, conditional on those
gates and resolution of the golden mismatch. Both conditions are now satisfied.

| Row | Before | After |
| --- | --- | --- |
| `margin_deposit` preservation/refinement | .30/.35 | .35/.40 |
| `margin_withdraw` preservation/refinement | .30/.35 | .35/.40 |
| W09 low/central/high | .23/.31/.41 | .24/.32/.42 |

Semantics stay .50 and uncertainty stays H for both capabilities. All other
scores, including whole-market terminal closeout, are inherited unchanged.
The unchanged calculator yields formal **21.169% → 21.219%** (+.050 points)
and V3 **23.969% → 24.069%** (+.100 points). These are planning estimates.
No lane, route, release or value-safety gate closes.

Universal implementation refinement, complete market reconstruction proofs,
cryptographic authentication, funding, liquidation, insurance and publication
remain outside this result. The Lean effect identities are algebraic helpers;
full runtime effect ownership is finite executable evidence.
