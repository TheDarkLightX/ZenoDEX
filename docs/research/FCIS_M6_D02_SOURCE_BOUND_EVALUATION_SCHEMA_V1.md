# FCIS M6 D02 Source-Bound Evaluation Schema V1

Status: TESTED / UNMOUNTED

D02 makes source-derived SLNF evidence an input to evaluation. It does not
attach roots after a candidate or decision has already been computed.

## Controlled binding

`FCISFeeOccurrenceBindingV1` contains:

```text
segment: CanonicalFeeOccurrenceSegmentV1
boundary_root
policy_root
witness_tuple_root
semantic_stream_root
lineage_stream_root
```

Its constructor requires an evaluator-controlled token. It accepts only the
exact segment type, re-runs the segment projection check, and compares every
carried root with the segment’s freshly available root. Caller-supplied root
tuples therefore cannot mint the binding through the public value constructor.

## Evaluation flow

The source-bound entry point performs this sequence:

```text
exact SourceBoundFeeOccurrenceV1
  -> fresh source-occurrence verification
  -> controlled evaluator binding
  -> exact command/context/state admission
  -> segment projection before fee-state transition
  -> candidate with the binding
  -> evidence with the identical binding object
  -> source-bound decision derivation from that evaluation
```

`FCISStepEvaluationOkV1` requires candidate and evidence to carry the same
binding identity. The source-bound lineage module calls this evaluator before
decision derivation and uses the same source occurrence for closure.

## Wire-schema boundary

`FCISFeeAllocationV1` remains the existing four-field allocation value:

```text
buyback_amount
treasury_amount
rewards_amount
dust_carried
```

The source binding is deliberately carried by `FCISStepCandidateV1` and
`FCISStepEvaluationEvidenceV1`. Adding it to `FCISFeeAllocationV1` would alter
the established commit-plan codec and would make unrelated receipt/decision
construction reject. D02 preserves the wire schema while requiring the fee
transition to validate the source segment before applying its existing fee
accumulator input.

## Required equalities

For an accepted source-bound evaluation:

```text
evaluation.material == extraction.material
candidate.source_fee_occurrence is evidence.source_fee_occurrence
candidate.source_fee_occurrence.segment is extraction.segment
binding roots == extraction.segment roots
decision.next_state == evaluation.candidate.state
```

For a foreign or crossed segment:

```text
fresh source verification -> typed source_occurrence_rejected
candidate acceptance -> impossible
```

## Evidence boundary

The focused tests and deterministic checker establish the equalities on the
declared fixture and kill the crossed-segment and caller-minting mutants.
Strict Python typing, Ruff, formatting, compilation, and dependent regression
tests are separate executable gates.

This packet does not claim that a production caller is forced through the
source-bound entry point, that B06’s SLNF allocator is mounted into the live
fee amount, or that any datastore atomically persists this evidence. Those are
later integration and publication obligations.
