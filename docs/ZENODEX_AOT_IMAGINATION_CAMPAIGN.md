# ZenoDEX AoT 1000 Imagination Campaign

This document describes the replayable Atom-of-Thoughts-style imagination
campaign implemented by:

```bash
python3 tools/zenodex_aot_imagination_campaign.py --format text
```

The campaign enumerates a fixed 1000-node grid:

```text
10 mechanism surfaces * 10 perturbation axes * 5 adversary classes * 2 timing models
```

It is a hypothesis generator. It does not close any disaster state by itself.
Its job is to create a stable work queue of Tau Net / Tau Lang aligned threat
candidates, with EVM-only assumptions filtered out and every candidate tied to
an evidence lane.

## Current Receipt

```text
status = accepted
candidate_count = 1000
rejected_evmism_count = 0
```

## Top Diverse Promotion Targets

The generator ranks all 1000 candidates, then selects a diverse top-five queue
so we avoid spending a cycle on five near-duplicates.

1. `AOT-0727`: Perps funding and liquidation value binding under a governance
   operator in a single epoch.
2. `AOT-0474`: ZenoProof verifier registry canonicalization under a bonded
   reporter across epochs.
3. `AOT-0394`: Governance amendment activation cross-module sync under a
   bonded reporter across epochs.
4. `AOT-0268`: Reporter economics and slashing source/proof independence under
   a governance operator across epochs.
5. `AOT-0613`: Quote receipt settlement time freshness under a bonded reporter
   in a single epoch.

Each target includes:

- a fixed game surface;
- an attack query;
- a bounded Tau-native model;
- a mitigation sketch;
- a runtime adapter path;
- an evidence lane;
- a first 24-hour falsifier;
- a promotion gate;
- explicit non-claims.

## Promotion Discipline

The campaign output should be treated as `hypothesis` until a target receives
one of:

- exact integer/rational replay with positive and mitigated negative cases;
- Tau policy replay;
- receipt mismatch replay;
- bounded temporal model with explicit fairness assumptions;
- Lean/ESSO theorem whose statement exactly matches the promoted claim.

## Non-Claims

The campaign does not claim:

- exhaustive production disaster search;
- full Tau Net consensus safety;
- global Tau Lang solver complexity bounds;
- live oracle network safety.

## Why This Is Better Than Raw Imagination

Raw campaigns tend to overfit dramatic narratives. This replay uses a fixed
grid, stable scoring, Tau-specific assumption filters, explicit evidence lanes,
and non-claims. The result is a repeatable promotion queue that can be tested,
diffed, and extended.
