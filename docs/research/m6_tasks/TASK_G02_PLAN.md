# G02 plan: canonical proof-context codec and parity

Status: implemented and tested in the isolated public research slice.

## Objective

Give the immutable G01 proof-context value one exact, bounded, fail-closed
binary representation and reproduce its bytes and transport root in an
independent Rust harness.

## Procedure

1. Freeze the fifteen-field order, field tags, magic, version, and frame widths.
2. Validate the exact G01 value before encoding.
3. Decode only the complete canonical sequence and rederive the G01 semantic
   context root before returning success.
4. Derive a separate length-framed G02 codec root without changing G01 root
   semantics.
5. Return typed rejection for malformed, noncanonical, resource-exceeding, or
   semantically crossed input.
6. Run deterministic property mutations over state-root substitutions and
   trailing bytes.
7. Compare Python and Rust payload hex and codec root from a committed vector.

## Required evidence

- immutable typed success/rejection results and bounded codec implementation;
- fixed canonical vector and independent Python checker;
- Rust payload/root parity harness and committed input/output vectors;
- focused tests for round trip, version, field, tag, frame, and root failures;
- deterministic property tests for generated state-root and trailing-byte
  mutations;
- Ruff, strict mypy, Python compilation, Rustfmt, Clippy, JSON, and packet
  manifest validation.

## Nonclaims

G02 does not authenticate a proof, own a verified witness, pin a verifier
registry, bind public inputs to ANF, prove semantic validity in Lean, mount a
runtime caller, refine a production datastore, or enable value movement.
