# Tau artifact workbench: third-cycle experiment contract

Date: 2026-09-08 UTC. Status: implemented experiment contract. Authority: NONE.
Base: `17a3bfce09886ce4386f0a52d0b2c6ae6115ef91`. Earlier compiler and replay
sources remain frozen. This cycle connects local choices to actual code bytes.
Acceptance evidence and the final claim scope are recorded in the
[accompanying study](tau_workbench_20260908.md).

## Ranked candidates

1. **Exact finite component workbench.** Measure each candidate over the whole
   component input domain; group behaviorally equal implementations; derive
   compatible local class sets with Tau; check actual assembled code against an
   independent oracle. This closes the planning-flag-to-artifact gap and allows
   equivalent local replacements without recompilation.
2. **Revision and renegotiation.** Explain which choices survive a changed
   specification or a new behavior. Useful next extension after the artifact
   binding is established; stale environments and missing intermediate inputs
   are decisive failure cases.
3. **General Python semantic merging.** Higher reach, much larger proof and
   execution boundary. Deferred. Existing semantic merge verification is direct
   prior art, including [SafeMerge](https://arxiv.org/abs/1802.06551).

## Selected object and experiment

A human supplies ordered stages, a finite integer domain, allowed initial
inputs, expected end-to-end outputs, and an anchor naming one candidate per
stage. Each agent supplies ordinary Python source for exactly one pure unary
function `transform(x)`. The admitted subset has one return expression, bounded
syntax, integer literals and arithmetic/bitwise/comparison/conditional
expressions. Calls, imports, state, loops and arbitrary Python execution are
outside this profile. Unsupported source is rejected before execution.

The whole component domain is `0 .. 2^bits - 1`, with `1 <= bits <= 8`. Every
candidate must return an exact integer in that domain for every input in it.
Equality on the initial inputs alone is insufficient: later stages may see
different intermediate values. The component interpreter measures complete
tables. Immutable source bytes and the complete domain identify each artifact.

Stage-wise equivalence is equality of the complete tables. The quotient retains
all candidate names and bytes in each class. A bounded exhaustive composition
of the tables supplies a global class relation; invalid selector bit patterns
are explicitly excluded. The existing Tau Swarm compiler derives local class
domains from that relation. Lifting them through the table equivalence retains
compatible actual implementations. The expected property remains a human
specification, not a model-generated claim of correctness.

Pilot: three agents maintain a compact message encoder, a version/tag adapter,
and a decoder. The payload has six bits and the wire value has eight. Competing
code versions use different tags, tag removal and decoder tolerance. The human
requires exact payload round trips for all 64 payloads. Equivalent expression
forms and behaviorally distinct strategies are counted separately.

An isolated CPython process loads only sources admitted by the restricted
profile, then executes complete assembled bundles. It compares all actual
outputs to the human's expected table. This is independent of the interpreter
and the Tau relation. It establishes only the declared finite profile; no
general-purpose Python sandbox or unrestricted-program correctness is claimed.

## Baselines and obligations

- Cached centralized checking over artifact combinations.
- The same exact behavioral quotient with centralized checking.
- Quotient plus Tau local delegation, with independent finite cofactor parity.

Measure source evaluations, distinct behavior classes, global checks, accepted
artifact and behavior combinations, rejected proposed combinations, compile
cost and equivalent-replacement reuse. Count a renegotiation only for a declared
candidate-replacement event. These measurements do not measure human time or
general LLM productivity. A finite Python rectangle construction is an
additional oracle; Tau need not be faster on a tiny domain.

Proof obligations: the complete component domain is closed under every admitted
candidate; equivalent tables compose equivalently; class selectors are valid;
lifted local products satisfy the original end-to-end relation; final checks
use exact candidate bytes; replacements either preserve an admitted behavior
class or explicitly require renegotiation. Cached metadata grants no authority.

The finite relation is rendered using the smaller of positive-table enumeration
and bounded classical Shannon factoring. Exhaustive selector-row parity must
preserve its meaning. Paired native compilation measures representation cost
separately from source analysis. A 3,375-product exhaustive oracle supplies the
maximum product and an alternative valid anchor for this fixed pilot only.

Negative evidence: source disagreement on a reachable intermediate value,
out-of-domain or Boolean output, unsupported source, forged/stale artifact
metadata, absent selector classes, unsafe independently feasible choices,
changed expected outputs, and interpreter/native disagreement. Preserve all
earlier source hashes, and reject native UNKNOWN or missing required evidence.

Completion requires reviewed implementation, CLI and demonstration, independent
CPython replay, focused tests, source-bound results, lessons and an honest
comparison. Only a completed successful research slice may be committed.
