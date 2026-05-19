# ZenoEnergy Dominance-Prefix Cover

This offline audit measures how many ranked verifier calls are needed before the accepted prefix has a dominance-cover certificate over the verified finite candidate list.

## Summary

| mode | count | ok | mean checked | p95 checked | p99 checked | mean checked ratio | full fallback count |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| exhaustive | 119 | 119 | 2.5210 | 6 | 7 | 0.1052 | 0 |
| random | 119 | 119 | 12.8824 | 23 | 24 | 0.5373 | 5 |
| hand | 119 | 119 | 1.4454 | 3 | 4 | 0.0603 | 0 |
| learned | 119 | 119 | 1.0000 | 1 | 1 | 0.0417 | 0 |
| hybrid | 119 | 119 | 1.0000 | 1 | 1 | 0.0417 | 0 |

## Safety Boundary

- The audit consumes deterministic verifier results and never accepts a settlement.
- A passing prefix certificate is a finite-list statement over already verified candidates.
- Live early stop still needs a verifier-facing unchecked-suffix bound or deterministic full fallback.
- A bounded-grid production claim still needs a separate full-list completeness proof.

## Negative Knowledge

- Dominance-prefix certificates measure ranked search cost; they do not make model scores authoritative.
- If a ranked prefix reaches the full candidate list, the certificate gives no verifier-call savings over full fallback.
