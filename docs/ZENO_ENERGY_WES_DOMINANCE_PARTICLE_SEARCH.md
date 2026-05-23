# ZenoEnergy WES Dominance Search

WES ranks candidate dominance-cover pruning claims. The UPBA verifier and deterministic dominance-cover checker provide the labels.

## Summary

WES commit: `5a26bcc1d97c90503bb66e67c7c2a2cf40d41bb6`

| policy | checked | useful@k | calls to first useful | near misses@k | non-useful@k |
| --- | ---: | ---: | ---: | ---: | ---: |
| model_online | 80 | 25 | 1 | 25 | 0 |
| model_frozen | 80 | 25 | 1 | 25 | 0 |
| declared_priority | 80 | 25 | 1 | 25 | 0 |
| cheap_first | 80 | 15 | 1 | 10 | 10 |
| input_order | 80 | 15 | 1 | 10 | 10 |
| random_seeded | 80 | 15 | 1 | 10 | 10 |

## Boundary

- WES changes checker order only.
- A passing WES result does not authorize settlement.
- The dominance-cover checker still depends on deterministic UPBA verification.
- The benchmark uses bounded synthetic full lists, so production promotion still requires real replay and full-list completeness evidence.

## Negative Knowledge

- Weak pruned sets remain useful negative controls because the checker rejects uncovered better verified candidates.
- A passing WES search report does not remove the full-list completeness obligation for bounded-grid claims.
