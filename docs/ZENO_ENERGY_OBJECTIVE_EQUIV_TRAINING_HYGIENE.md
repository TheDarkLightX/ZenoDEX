# ZenoEnergy Objective-Equivalent Training Hygiene

Date: 2026-05-18

Artifact:
`data/upba_energy/upba_v2_objective_equiv_training_hygiene_receipt.json`

## Claim

The pairwise trainer now supports an objective-equivalent positive class:

```text
Positive_objective_equiv(c) :=
  VerifierAccepts(c)
  and objective(c) = max objective over verifier-accepted candidates in the batch
```

This aligns the learning signal with the formal quotient boundary used by the
runtime telemetry. If two verifier-accepted candidates have the same
`(objective_volume, objective_surplus)`, the trainer can give both the same
winner-pair pressure against lower candidates instead of privileging the
hash-selected representative.

## Modes

```text
--positive-class hash-winner
--positive-class objective-equivalent
```

`hash-winner` preserves old receipts and model artifacts. `objective-equivalent`
is the recommended research setting for new runs because it trains on the whole
tied maximum-objective class.

The pairwise loss still skips equal-label pairs:

```text
score(good) <= score(bad) -> no pair update
```

So tied maxima are not trained against each other. They only receive equal
positive pressure against lower valid or invalid candidates.

## Safety Boundary

This is a training-target change only. It does not change verifier acceptance,
candidate validity, fallback, state roots, or consensus imports.

```text
LowEnergy(c) and not VerifierAccepts(c) -> SettlementRejected
```

The model remains an advisory ordering function. Deterministic verification
still decides every accepted settlement.

## Replay

Focused unit tests cover:

- `hash-winner` selects only the dataset's canonical winner.
- `objective-equivalent` selects every tied valid argmax candidate.
- winner-pair weight follows the selected positive class.
- the no-dependency trainer accepts `positive_class="objective-equivalent"`.

Receipt replay checks are wired through
`tools/check_zenoenergy_research_evidence.py`.

## Research Consequence

This does not claim a new benchmark improvement by itself. It removes an
avoidable source of label noise before the next model run: arbitrary hash
tie-breaking should not teach the model that one objective-equivalent
verifier-accepted candidate is better than another.
