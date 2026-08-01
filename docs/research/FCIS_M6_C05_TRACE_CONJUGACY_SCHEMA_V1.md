# FCIS M6 C05: Lean Trace Conjugacy V1

Status: PROVED / UNMOUNTED within the declared Lean carrier

## Carrier and map

The C05 module defines a shared `SignedState` carrier and the coordinatewise
sign map:

```text
phi(c0, c1, c2) = (-c0, -c1, -c2)
```

The SRGD fold applies `updateDeficit`; the AGQE fold applies
`updateSurplus`. Both folds consume the same ordered nested word of
authenticated occurrences, preserving segment boundaries.

## Theorems

The public theorem surface includes:

```text
phi_state_involution
phi_keyed_state_key_preserved
one_step_sign_dual
fold_segment_sign_dual
fold_word_sign_dual
valid_srgd_segment_sign_dual
valid_srgd_word_sign_dual
trace_conjugacy
```

The central equality is:

```text
phiState (foldSRGDWord D word state) =
  foldAGQEWord D word (phiState state)
```

The validity theorem transports each source-valid occurrence, segment, and
nested word to the corresponding AGQE relation. The involution and key
theorems are separately explicit.

## Evidence boundary

The focused module build, full 8,151-job `lake build`, placeholder scan, and
explicit theorem axiom audit are retained in the task receipt. Lean uses the
existing local mathlib checkout through the documented ephemeral
`external -> ../external` link, which is removed after each gate. No runtime
caller, authority adapter, datastore, deployment, or value-moving path is
mounted.
