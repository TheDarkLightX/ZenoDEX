# Critical Region Dispatch v1

## Result

The bounded experiment selects failing-region midpoint refinement as the
certificate compiler for this corpus. The derivative-aware candidate remains
as a falsified comparator.

All methods use exact `Rational{BigInt}` arithmetic and the same acceptance
rule. A result is accepted only when a complete partition of `[0,1]` is emitted
and every Bernstein coefficient on every interval is nonnegative.

## Bounded domain

- 240 normalized Gegenbauer envelope and Turan obligations from v185;
- 154 endpoint-max-normalized Jacobi envelopes from v186;
- 378 cone-oriented Jacobi Turan obligations from v188;
- seven negative controls, including a polynomial that is positive at both
  endpoints and negative in the interior;
- at most 32 emitted leaves per adaptive search;
- equal-subdivision candidates in `{1,2,4,8,16,32}`.

The de Casteljau interval-restriction backend is differentially checked against
the older power-basis affine-composition formula on 12 exact cases.

## Algorithms

Let `B_I(p)` be the exact Bernstein coefficients of polynomial `p` on interval
`I`.

Equal subdivision tries the fixed partitions with 1, 2, 4, 8, 16, then 32
pieces. It accepts the first partition satisfying

```text
forall I in partition, min(B_I(p)) >= 0.
```

Midpoint adaptive refinement starts with `[0,1]`, selects a currently failing
leaf, and bisects only that leaf. It stops with `UNKNOWN` when the leaf budget
is exhausted.

The critical-aware candidate computes the Bernstein coefficients of `p'` from
adjacent differences of `B_I(p)`. Sign changes propose a derivative-root
landmark. The landmark is snapped to the global `1/64` grid before splitting,
which bounds endpoint denominator growth. Derivative information changes only
the search policy. It cannot authorize acceptance.

An earlier coefficient-interpolated landmark was discarded. Recursive exact
interpolation made split denominators depend on coefficient height and caused
severe big-integer growth. A certificate compiler needs an explicit arithmetic
work bound as well as a sound acceptance rule.

## Measurements

| Method | Positive accepts | False accepts | Pieces | Max pieces | Canonical bytes | Compiler scalar updates |
|---|---:|---:|---:|---:|---:|---:|
| Equal | 772/772 | 0/7 | 3,592 | 16 | 4,076,028 | 2,914,114 |
| Adaptive midpoint | 772/772 | 0/7 | 2,928 | 8 | 2,663,176 | 886,139 |
| Derivative landmark | 772/772 | 0/7 | 2,943 | 8 | 4,270,358 | 948,693 |

Relative to equal subdivision, adaptive midpoint refinement saves 664 pieces
(1,848 basis points) and 1,412,852 canonical bytes (3,466 basis points). It is
never worse per case on either metric in this corpus: 322 cases improve and 450
tie.

At a six-leaf budget, equal subdivision certifies 532 obligations and leaves
240 `UNKNOWN`; adaptive midpoint certifies 767 and leaves five `UNKNOWN`. At an
eight-leaf budget, the counts are 767/5 and 772/0 respectively.

The derivative-aware candidate saves pieces relative to equal subdivision but
adds 194,330 bytes overall. Relative to midpoint refinement it adds 15 pieces
and 1,607,182 bytes. The evidence does not support promoting it for these
Jacobi/Gegenbauer families.

## Proof and authority boundary

This experiment generates ordinary Bernstein interval certificates.
`Proofs/AdaptiveBernsteinRegionCertificates.lean` proves arbitrary-degree
nonnegative Bernstein combinations, one-step de Casteljau evaluation
invariance, recursive de Casteljau scalar evaluation, the exact
power-to-Bernstein coefficient formula, and the finite-cover lifting theorem.
The dispatcher itself is an advisory search policy.

Lean now binds an arbitrary Bernstein combination to the scalar produced by
recursively reducing all de Casteljau levels at an evaluation point. It also
proves that Julia's lower-triangular power-to-Bernstein coefficient formula
preserves every degree-bounded power-basis polynomial. The remaining unproved
compiler transformation is the construction of left/right coefficient arrays
for affine subinterval restriction. That transformation uses exact arithmetic
and participates in 12 differential checks against the power-basis reference.
A full affine subdivision theorem remains open.

No DEX state, Tau policy, oracle decision, settlement transition, or runtime
claim depends on this code. Exhausting a budget, finding a malformed cover, or
failing any coefficient check means `UNKNOWN`.

## Replay

```bash
python3 experiments/math_object_innovation_v132/run_critical_region_dispatch.py
pytest -q experiments/math_object_innovation_v132/test_critical_region_dispatch.py
```

Generated evidence:

- `generated/critical_region_dispatch.tsv`
- `generated/critical_region_dispatch_parity.txt`
- `generated/critical_region_dispatch_report.json`

## Non-claims

- The bounded corpus is not a general Jacobi or Gegenbauer theorem.
- The measurements do not establish an asymptotic complexity improvement.
- Midpoint refinement can still return `UNKNOWN` outside the tested domain.
- The canonical byte framing is the experiment's explicit interval/coefficient
  encoding, not a production FIRE or Tau receipt ABI.
- The exact compiler implementation is differentially checked, not end-to-end
  extracted from or verified by Lean.
