# RISC Zero Workspace Patches

This directory contains narrow local `crates.io` patches used only by the
`zk/state_proof_risc0` workspace.

## `ark-relations-0.5.1`

Reason: RISC Zero `2.3.2` reaches `ark-relations/std` through its Groth16 stack.
The published `ark-relations 0.5.1` crate pins optional R1CS tracing to
`tracing-subscriber 0.2.x`, which is below the patched range for
`RUSTSEC-2025-0055` / `GHSA-xwfj-jgwm-7wp5`.

Local delta:

- upgrade the optional `tracing-subscriber` dependency to `0.3.20+`
- update the tracing `Layer` hook name from `new_span` to `on_new_span`

The patch should be removed when arkworks or RISC Zero publishes an upstream
release with the same dependency shift.
