# ZenoEnergy Suffix-Bound Early Stop

This benchmark checks a deterministic early-stop certificate: a verifier-checked winner must dominate the checked prefix, and every unchecked candidate must have a declared objective upper bound no better than that winner.

## Summary

| mode | count | objective-equiv accepts | suffix stops | full fallback | mean calls | p95 | p99 | mean checked ratio | mean suffix disqualified |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| exhaustive | 119 | 119 | 119 | 0 | 2.6218 | 5 | 7 | 0.1092 | 19.1597 |
| random | 119 | 119 | 117 | 2 | 13.1849 | 23 | 24 | 0.5494 | 8.9832 |
| hand | 119 | 119 | 119 | 0 | 1.4202 | 3 | 5 | 0.0592 | 19.1597 |
| learned | 119 | 119 | 119 | 0 | 1.0084 | 1 | 1 | 0.0420 | 19.1597 |
| hybrid | 119 | 119 | 119 | 0 | 1.0084 | 1 | 1 | 0.0420 | 19.1597 |

Cross-seed stress is recorded in
[ZENO_ENERGY_SUFFIX_BOUND_CROSS_SEED.md](./ZENO_ENERGY_SUFFIX_BOUND_CROSS_SEED.md).
Across nine bounded synthetic configs, learned and hybrid orderings averaged
1.0132 verifier calls with zero invalid accepts.

Adversarial suffix stress is recorded in
[ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS.md](./ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS.md).
It shows deterministic disqualifiers close injected high-declared-output
invalid suffix candidates, while declared-output-only bounds fail every case.

## Safety Boundary

- The scorer only orders candidates.
- The accepted candidate is verifier-checked.
- The stop condition is a deterministic suffix-bound certificate.
- Candidate-family coverage is still required for production bounded-grid claims.

## Limits

- This benchmark uses bounded synthetic finite candidate lists.
- The suffix bound is deterministic, but a production bounded-grid claim still needs candidate-family coverage.
- Attractive invalid unchecked candidates can force more verifier calls because their declared outputs remain upper bounds until checked.
