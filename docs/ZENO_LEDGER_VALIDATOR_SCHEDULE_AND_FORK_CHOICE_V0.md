---
title: ZenoLedger Validator Schedule And Fork Choice V0
type: note
permalink: autonomous-tau-dex-review/docs/zeno-ledger-validator-schedule-and-fork-choice-v0
---

# ZenoLedger Validator Schedule And Fork Choice V0

This note describes the first pure policy layer for moving ZenoLedger from a
designated-writer public-testnet rehearsal toward a validator network.

## Scope

The v0 policy is implemented in
`src/integration/zeno_ledger_validator_schedule_v0.py` and covered by
`tests/integration/test_zeno_ledger_validator_schedule_v0.py`.

It provides:

- canonical validator-set construction and hashing;
- weighted round-robin proposer duties;
- scheduled-header admission against `header.sequencer_set_hash`;
- extend-only fork choice for already verified local and candidate tips.

## Validator Set

The validator set is canonicalized by sorting entries by
`(validator_id, key_id)` and hashing the body without `validator_set_hash`.
Only active validators enter the proposer schedule.

```text
ActiveSlotCount :=
  sum(v.voting_power for v in validators if v.status = "active")
```

The schedule rejects empty active sets and caps individual voting power and
total active slots so a malformed registry cannot create an unbounded schedule.

## Proposer Duty

For a validator set with `start_height = h0`:

```text
offset(height) := height - h0
slot_index(height) := offset(height) mod ActiveSlotCount
cycle(height) := floor(offset(height) / ActiveSlotCount)
```

The active validator occupying `slot_index(height)` is the scheduled proposer.
Weighted voting power is represented by repeated deterministic slots.

## Scheduled Header Admission

A header is admitted under this policy only when:

```text
header.chain_id = validator_set.chain_id
header.sequencer_set_hash = validator_set.validator_set_hash
scheduled_proposer(header.height) = claimed_proposer
```

This binds the block header to the current validator set and to the deterministic
proposer duty for its height.

## Fork Choice

The v0 fork-choice rule is intentionally conservative:

```text
CandidateAccepted :=
  same chain
  and same validator_set_hash
  and candidate extends the local tip
```

A candidate tip that requires a local reorg is rejected. A shorter candidate is
kept only when it is proven to be a prefix of the local chain. Same-height
conflicts are rejected as equivocation evidence for the surrounding network
layer to process.

## Residual Limits

This is a pure policy and replay surface. It does not yet implement open block
gossip, validator peer discovery, network transport authentication, slashing, or
automatic signer-quorum verification on live headers. Those are the next wiring
steps.
