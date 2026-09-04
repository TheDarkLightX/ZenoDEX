# Named Choice-Fiber Polynomial experiment

This bounded research experiment separates the useful part of “duplex
numbers” from the claims that do not survive exact analysis.

The admitted object is a canonical multilinear pseudo-Boolean polynomial

```text
f(epsilon) = sum_S c[S] * product(i in S, epsilon[i])
epsilon[i] in {-1, +1}
```

over a closed manifest of named choices. Exact occurrence identities map to
shared base choices with an optional polarity. This makes the difference
between shared, negated, and independent choices explicit.

Four exact minimization lanes are retained:

1. exhaustive replay over all `2^n` assignments, used as the bounded oracle;
2. a linear affine certificate;
3. a linear dynamic-programming certificate for pairwise forests;
4. exact component enumeration for disconnected higher-order interactions.

All certificate verifiers reconstruct owned values and recompute the
certificate from the exact polynomial. Caller-supplied tables, minima,
partitions, or assignments carry no authority in this research checker.

The resource profile admits at most 256 named choices, 4,096 exact choice
occurrences, 4,096 raw and canonical terms, 256 occurrences per raw term,
128-byte identifiers, and signed coefficients with magnitude below `2^256`.
Whole-cube and per-component enumeration are capped at 20 choices and at
20,000,000 estimated term-incidence evaluation steps per call. Interaction
components are discovered in time linear in retained term incidence. Oversized
inputs fail with typed capacity rejection before exponential work.

## Replay

```bash
cd experiments/choice_fiber_robustness_v1
python3 -m unittest -v
python3 run_experiments.py
python3 -m py_compile named_choice_fiber.py run_experiments.py test_named_choice_fiber.py
```

## Claim boundary

This is a useful composite of established pseudo-Boolean optimization,
Fourier-Walsh multilinear forms, Ising/tree dynamic programming, factor-graph
decomposition, and correlation-sensitive affine forms. No novelty or
production-authority claim is made.

Python process integrity remains an external premise. Production use requires
canonical-byte decoding or process isolation plus a verifier-owned authority
type; these frozen reference dataclasses are not such a boundary.
