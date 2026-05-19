# ZenoEnergy Dominance-Cover Runtime Prototype

This bounded research harness checks a deterministic dominance-cover receipt over verified UPBA v2 candidates. It is advisory evidence for pruning mechanics, and deterministic UPBA verification remains authoritative.

## Summary

| mode | count | ok | failed | structural verify ok | mean uncovered | max uncovered |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| winner_only | 79 | 79 | 0 | 79 | 0.0000 | 0 |
| hand_top1 | 79 | 56 | 23 | 56 | 0.3924 | 3 |
| weak_pruned | 75 | 0 | 75 | 0 | 3.6400 | 8 |

## Safety Boundary

- The checker consumes verifier results and never accepts a settlement.
- `winner_only` demonstrates a passing dominance witness over the supplied full list.
- `weak_pruned` is a nonvacuous negative control: it keeps a weak valid candidate and must fail when better verified candidates are uncovered.
- The result is scoped to bounded synthetic full lists. A production or bounded-grid claim still needs a separate full-list completeness proof for the full candidate family.

## Negative Knowledge

- A weak pruned set with an uncovered better verified candidate fails the dominance-cover check.
- Dominance-cover certificates are about pruning correctness, not about model accuracy.
