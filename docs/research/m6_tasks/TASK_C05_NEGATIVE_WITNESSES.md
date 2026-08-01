# FCIS M6 C05 Retained Proof-Repair Witnesses

Status: retained and repaired

## W-C05-01: nonexistent structure extensionality theorem

The first C05 target build rejected:

```text
Unknown constant `FCISFeeApportionmentAGQESRGDTraceConjugacy.SignedState.ext`
```

The proof was repaired by destructing `SignedState` and discharging the three
coordinate equalities with the checked `update_sign_dual` theorem. The
corrected focused target and full project build pass.

## W-C05-02: wrong fold rewrite direction

The first word-fold proof attempted to rewrite
`phiState (foldSRGD D segment state)` inside a target where that term was
inside the outer word fold. The tactic reported that the pattern was absent.
The proof was repaired by rewriting the AGQE segment fold backward to the
mapped SRGD segment fold, then applying the induction hypothesis at the
post-segment source state.

## W-C05-03: unbuilt local import graph

Direct `lake env lean` invocation before the local `Proofs` library was built
reported a missing `Proofs.FCISFeeApportionmentSRGDAdaptiveTrace.olean`. The
exact B04 dependency target was then built first. The C05 target build and
full 8,151-job build passed afterward. This is an environment/build-order
witness, not a theorem counterexample.

These witnesses remain documentation of the repair loop. No proof placeholder,
user axiom, unsafe declaration, or weakened theorem premise was introduced.
