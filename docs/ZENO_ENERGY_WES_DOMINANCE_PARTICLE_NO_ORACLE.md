# ZenoEnergy WES Dominance Search

WES ranks candidate dominance-cover pruning claims. The UPBA verifier and deterministic dominance-cover checker provide the labels.

## Summary

WES commit: `5a26bcc1d97c90503bb66e67c7c2a2cf40d41bb6`

| policy | checked | useful@k | calls to first useful | near misses@k | non-useful@k |
| --- | ---: | ---: | ---: | ---: | ---: |
| model_online | 80 | 24 | 1 | 24 | 1 |
| model_frozen | 80 | 24 | 1 | 24 | 1 |
| declared_priority | 80 | 25 | 1 | 25 | 0 |
| cheap_first | 80 | 17 | 1 | 13 | 8 |
| input_order | 80 | 17 | 1 | 13 | 8 |
| random_seeded | 80 | 17 | 1 | 15 | 8 |

## Boundary

- WES changes checker order only.
- A passing WES result does not authorize settlement.
- The dominance-cover checker still depends on deterministic UPBA verification.
- The benchmark uses bounded synthetic full lists, so production promotion still requires real replay and full-list completeness evidence.

## Negative Knowledge

- Weak pruned sets remain useful negative controls because the checker rejects uncovered better verified candidates.
- A passing WES search report does not remove the full-list completeness obligation for bounded-grid claims.
- Raw particle archives are poor dominance-cover claims. They can contain generated candidates that do not pass deterministic structural verification, so the dominance-cover certificate fails even when the archive contains high-quality candidates.
- The useful particle lane is verifier-filtered: `particle_best_obligation` checks the generated archive, keeps the best verifier-accepted representative, and submits that singleton as the WES dominance-cover claim.

## Lane Finding

No-oracle run:

```text
seed: 20260571
batches: 40
candidates_per_batch: 40
input_candidates: 240
top_k: 25
```

| policy | useful particle-best claims@25 | raw particle non-useful@25 | invalid accepts |
| --- | ---: | ---: | ---: |
| model_online | 24 | 0 | 0 |
| model_frozen | 24 | 0 | 0 |
| declared_priority | 25 | 0 | 0 |
| input_order | 5 | 4 | 0 |
| random_seeded | 6 | 3 | 0 |

Interpretation: WES benefits when the particle search branch emits a
verifier-filtered dominance-cover claim. Raw particle archives remain useful as
negative controls for pruned-set soundness.
