# Named Choice-Fiber Experiments V1

Status: `BOUNDED_RESEARCH_ONLY`

Authority: `NONE`

This checkpoint preserves three related experiments derived from exact analysis
of finite named `+/-` choices.

## Preserved results

1. [Named Choice Fiber Polynomial V1](../../experiments/named_choice_fiber_polynomial_v1/README.md)
   defines the canonical multilinear function, separates semantic, lineage,
   truth-table, distribution, and support identities, and includes a pinned Tau
   replay.
2. [Choice-Fiber Robustness V1](../../experiments/choice_fiber_robustness_v1/README.md)
   gives exact minimum certificates for affine polynomials, pairwise forests,
   and disconnected bounded components.
3. [ZRPF Choice-Subcube Coverage V1](../../experiments/zrpf_choice_subcube_coverage_v1/README.md)
   gives exact coverage checks for arbitrary subcube partitions and a linear
   canonical-tree discipline for scheduler-controlled partitions.

All three use established mathematics. The current disposition is:

```text
usefulness: useful bounded research and test-generation infrastructure
novelty: no current novelty claim
production authority: none
```

## Evidence

The core packet retains thirteen focused tests, nine semantic mutation killers, an
independent direct enumerator, and fifteen expected Tau judgments against a
pinned alpha toolchain.

The robustness packet retains twenty-two focused tests, 1,418 bounded cases,
11,440 exact assignment checks, and four minimized falsifiers. It records the
NP-hardness boundary for general pairwise minimization.

The coverage packet retains ten focused tests, 156 recursively generated
partitions through three choices, a complete classification of 154 exact
partitions at three choices, the first five-cell nonrecursive counterexample,
and eleven named attack rejections.

Each packet has a closed source manifest or checker. Timings remain
single-host observations outside deterministic acceptance.

## Nonclaims and residual risks

These experiments do not establish:

- completeness of a governance or adversarial world model;
- open-population counting, Sybil resistance, or preference legitimacy;
- cryptographic receipt soundness or correct ZRPF leaf computation;
- Tau Net throughput or mainnet semantics;
- M6, settlement, governance, proof, verifier, migration, or runtime authority;
- novelty, patentability, or freedom to operate.

The reference implementations use bounded Python profiles. Production use
would require an owned runtime schema, cross-language canonical bytes,
cryptographic receipt admission, formal proofs for the selected verifier, and
a mounted no-bypass consumer.

## Next frontier

The highest-value continuation is a treewidth-bounded robustness certificate
whose decomposition is source-bound and whose ZRPF leaves are paired
structurally with exact named subcube scopes. That work should proceed only
with a verifier-owned receipt type and a falsifier for incomplete or overlapping
scope coverage.
