# FCIS M6-R01/R04 Source-Bound Fee Lineage

**Date:** 2026-07-30  
**Status:** `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`  
**Base:** M6-R01 Segmented Lineage Normal Form and M6-R04 Lineage Certificate Closure

## Result

This checkpoint removes caller-selected fee boundary, policy, witness, semantic,
and lineage roots from the concrete R04 derivation surface.

The new source chain is:

```text
exact retained pre-state + settlement + intents + context
  -> independent exact step replay
  -> exact settlement index
  -> direct-swap protocol-fee witness tuple
  -> transition-local SLNF segment
  -> semantic_stream_root + lineage_stream_root
  -> evaluation/receipt/bundle/outbox closure
```

The public source-bound function accepts no occurrence segment and no root.

This narrows the source-continuity gap. It does not authenticate the shell input,
prove that the retained state is the datastore-current head, or establish a
production deployment/configuration authority.

## Source-bound extractor

`src/core/fcis_fee_occurrence_extractor.py` consumes one exact
`FCISStepEvaluationOkV1`.

Before extracting a witness, it:

1. revalidates every retained evaluation root;
2. reruns the exact evaluator from the retained committed pre-state, settlement,
   intents, and context;
3. requires the replayed evaluation to equal the supplied evaluation;
4. derives the exact settlement index and intent/fill coverage relation;
5. derives boundary and fee-policy roots from retained source values;
6. creates source-witness roots from the exact command/context/state lineage,
   settlement position, intent, assets, pool, fill values, and protocol fee;
7. invokes the existing SLNF normalizer.

For a direct swap, the witness key is:

```text
("protocol-fees", asset_in)
```

and the witness amount is the exact `protocol_fee_paid` retained by the accepted
fill. Zero protocol fees remain explicit witnesses.

## Honest route boundary

The current route fill retains one aggregate `fee_paid` value but no ordered
per-leg protocol-fee amounts and assets. A route may cross multiple fee assets.
Therefore a filled route under a nonzero protocol-fee share rejects with:

```text
route_fee_provenance_gap
```

The extractor does not fabricate a single asset key or flatten a heterogeneous
route fee into one scalar.

Closing this gap requires the exact route replay to retain a per-leg protocol-fee
witness tuple or an independently proved equivalent representation.

## Policy-root boundary

The source-bound policy root commits:

```text
SRGD algorithm profile
fixed role order
fee distribution domain
buyback/treasury/rewards weights
protocol fee share
protocol fee custody recipient
```

The residual state key remains independent of ordinary custody rotation. The
current context does not yet provide the complete deployment-pinned P4B5A
configuration and three semantic destinations, so this root is a source-bound
research identity, not final configuration authority.

## Source-bound R04 composition

`src/core/fcis_source_bound_lineage.py` performs:

```text
evaluate
  -> source-bound fee extraction
  -> decide
  -> bundle
  -> concrete lineage closure
```

It returns one controlled `FCISSourceBoundLineageCertificateV1` retaining:

```text
source extraction
concrete R04 closure
exact transition budget
```

The wrapper requires object identity between:

```text
extraction.evaluation
closure.evaluation
```

and between:

```text
extraction.segment
closure.occurrence_segment
```

It also requires the closed claim set to contain every member of the frozen
`FCISLineageClaimKeyV1` registry.

The defensive verifier does not trust the cached closed set. It freshly:

1. re-extracts the fee occurrence segment from the retained evaluation;
2. rebuilds the complete concrete closure from evaluation, decision, bundle,
   budget, and source-derived segment;
3. compares the fresh extraction and closure with the retained values.

A coordinated attacker cannot remove or alter a claim and merely recompute the
claim-set root.

## Commit-port and crash evidence

The focused tests pass the source-bound bundle through the actual immutable
reference commit port.

Expected outcomes are checked for:

```text
crash before linearization -> unchanged PRE
ordinary publication       -> complete POST
crash after linearization  -> complete POST
store-current mismatch     -> STALE, no publication
crossed outbox plan         -> INVALID, no publication
```

This is executable refinement evidence for the abstract PRE/POST law. The
reference port remains a pure model, not a production datastore or recovery
proof.

## Permanent mutants

The new tests retain:

- no caller root or occurrence-segment parameter;
- zero protocol-fee witness retention;
- nonzero direct-swap fee-to-input-asset binding;
- two-witness settlement order and unique source roots;
- policy rotation changes occurrence context but not the entitlement state key;
- missing fee-distribution policy rejection;
- corrupted evaluation-lineage rejection;
- missing required claim with attacker-recomputed root;
- conflicting digest with attacker-recomputed root;
- stale current-state rejection;
- crossed-outbox rejection;
- PRE/POST crash behavior.

## Remaining gaps

This checkpoint does not yet prove or implement:

- shell authentication of command, state, context, policy, or deployment;
- datastore-current rederivation before evaluation or publication;
- a deployment-pinned complete fee-distribution configuration;
- route per-leg protocol-fee provenance;
- roots embedded in the production candidate, receipt, and bundle schemas;
- Python/Rust extraction and root parity;
- transactional datastore publication and real crash recovery;
- history/nullifier reconstruction;
- outbox acknowledgment semantics;
- mounted no-bypass.

The next safe artifact is a schema-reviewed candidate/receipt/bundle extension
that embeds the source-derived roots, followed by datastore-current and
transactional publication evidence. Nothing in this checkpoint authorizes a
mount.
