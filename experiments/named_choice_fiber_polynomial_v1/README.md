# Named Choice Fiber Polynomial V1

Status: `BOUNDED_RESEARCH_ONLY`

Authority: `NONE`

This packet repairs and preserves the useful core of the notation presented at
[duplexnumbers.com](https://duplexnumbers.com/). It uses a clean implementation;
no website source code was imported.

## Exact object

For a closed manifest of named signs, define

```text
f(epsilon) = sum over S of c[S] * product(epsilon[i] for i in S)
epsilon[i] in {-1, +1}
```

The website's `a +/- b +/- c` notation is the degree-one affine fragment. The
full multilinear form is closed under multiplication because
`epsilon[i]^2 = 1`; multiplying monomials combines their choice sets by
symmetric difference.

The packet keeps five concepts separate:

```text
closed choice manifest
named function
uniform assignment distribution
distinct support set
source occurrence lineage
```

The semantic manifest root contains only the ordered choice identifiers and
correlation rule. A separate lineage-manifest root contains exact source
occurrences, and the complete manifest root binds both. Likewise, the function
root excludes source lineage while the complete polynomial root includes it.
The truth-table root preserves named assignment order; the distribution root
commits only to the reduced uniform output-probability histogram.

Equal choice names inside one manifest mean a shared sign. Separately sourced
choices remain distinct even when their printed coefficients are equal.

## Mathematical corrections

- `n` signs give exactly `2^n` labeled assignments and at most `2^n` distinct
  values. `0 +/- 1 +/- 1` has branches `(-2, 0, 0, 2)` and support
  `(-2, 0, 2)`.
- Mean equal to the center and variance equal to the sum of squared affine
  coefficients require independent fair signs with assignment multiplicity.
- Not every finite symmetric support set is a flat signed sum. In particular,
  `{+/-1, +/-2, +/-4, +/-8}` is not the support of a three-sign affine form.
- Addition needs named correlation semantics. Shared and independent copies of
  the same printed expression can have different results.
- Closure under arbitrary multiplication requires allowing interaction terms.
  The affine fragment alone is not closed.
- Compact syntax does not make every query cheap. Affine extrema are linear in
  the number of choices, while exact target membership contains subset-sum.

The object is established mathematics under nearby descriptions: weighted
Rademacher sums, signed subset sums, affine Boolean-cube images, and degree-one
Fourier-Walsh polynomials. The name `duplex numbers` also already denotes
split-complex or hyperbolic numbers. This packet makes no novelty claim.

## Bounded results

The Python model and independent report establish:

```text
shared sign support:      {22, 38}
independent sign support: {22, 28, 32, 38}
independent product:      {136, 184, 204, 276}
product interaction:      6 * epsilon[risk] * epsilon[policy]
```

The pinned Tau experiment contains fifteen queries over 8-bit and 16-bit
domains. It checks shared and independent identities, affine closure, sharp
bounds, multiplication non-closure, and exact interaction recovery. All
fifteen expected verdicts matched.

Nine permanent semantic mutants cover identity freshening, premature
deduplication, interaction loss, foreign-source aliasing, false symmetric-set
universality, modular-wrap confusion, function-identity substitution,
truth-table/distribution confusion, and semantic/lineage confusion.

The executable research profile admits at most 256 named choices, 4,096
canonical terms, 256 choice occurrences per raw monomial, and signed
coefficients with magnitude below `2^256`. Exact branch enumeration is capped
at twelve choices; affine bounds remain available for larger admitted
manifests. Polynomial products reject before exceeding 1,000,000 term-pair
probes.

## ZenoDEX use

Promising research uses:

1. bounded adversarial scenario families;
2. Alignment-Theorem sensitivity and robustness checks;
3. exact ZRPF subcube-coverage certificates;
4. fixed-roster governance and coalition experiments;
5. Tau, ESSO, Lean, and runtime parity-case generation.

The affine safety condition

```text
minimum(f) = center - sum(abs(coefficients))
```

compresses an exact `2^n` branch extremum check into linear work. Nonlinear
terms may require exponentially many interaction coefficients.

For opinion maps, Tau's Boolean algebra remains the semantic judge. A durable
ledger owns authenticated membership, multiplicity, and open-population counts.
This polynomial can analyze bounded numerical consequences of policy choices.

## Replay

From this directory:

```bash
python3 -m pytest -q test_choice_fiber_polynomial_v1.py
python3 reference_semantics.py
python3 run_mutation_checks.py
python3 check_packet.py
```

Tau replay requires the exact source and binary named in `tau_profile.json`:

```bash
python3 run_tau_contract.py \
  --tau-bin PATH_TO_PINNED_TAU_BINARY \
  --tau-source PATH_TO_PINNED_TAU_SOURCE
```

The optional single-host timing observation is outside the deterministic claim
gate:

```bash
python3 benchmark_tau_affine.py --tau-bin PATH_TO_PINNED_TAU_BINARY
```

## Nonclaims

- No settlement, governance, migration, verifier, proof, or M6 authority.
- No Tau Net throughput or scalability result.
- No arbitrary correlated-sign distribution; distinct IDs are independent
  only under the uniform assignment projection.
- No claim that nonlinear expressions remain compact.
- No general-purpose circuit-verification shortcut.
- No worldwide novelty, patentability, or freedom-to-operate conclusion.
- No production dependency or mounted runtime path.
