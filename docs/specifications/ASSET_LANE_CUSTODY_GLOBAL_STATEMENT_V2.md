# Custody and global statement V2

Status: bounded native implementation and guest integration candidate. This
specification grants no release, verifier-profile, migration or publication
authority. It extends the explicit V2 custody successor; it does not reinterpret
historical account-only or ABI V1 bytes.

## Economic contract

The typed producer receives an owned ASSET_TRANSFER context, complete custody
lane predecessor, a selected transfer or managed lifecycle command, and complete
global pre/post disclosures. It calls the existing custody coordinator. An
economic rejection returns the unchanged typed rejection before global relation
validation, with identical lane roots and empty effects.

For an accepted command, the existing custody/global refiner must establish the
complete projection, unchanged custody and claimant rows, actual physical supply,
lane/release/writer binding, exact occurrence, replay and global effect relation.
Its current empty-reserve restriction and sender-as-fee-owner admission refusal
remain. No arithmetic, rounding, ownership or command policy changes here.

Only successful refinement produces canonical JSON bytes with these exact fields:

```text
schema: "zenodex/asset-lane-custody-global-statement/v2"
module_journal: the accepted LaneModuleTransitionJournalV2
global_pre_state_root: the refiner's returned predecessor root
global_post_state_root: the refiner's returned successor root
```

The producer reads the roots from the completed refiner result. It does not
validate one snapshot and then reread caller-owned state to select output roots.
Python snapshots context before execution. Rust uses immutable owned inputs.

The journal binds lane states, effects, occurrence and the new coordinator's
semantic receipt commitment. The global roots commit the complete global tables,
including custody and claimant liabilities. Fixed empty terminal/Oracle plans
and derived refinement/delta roots add no independently variable statement
information for this restricted producer.

## Framed witness boundary

The inner input frame is exactly:

```text
8 bytes:  ZDXCGV2 followed by one zero byte
1 byte:   0 = TRANSFER, 1 = MANAGED_LIFECYCLE
five components, each: length:u32LE followed by exactly length raw bytes
order: context, custody_pre_state, selected command, global_pre, global_post
```

All other route bytes reject. Each component is nonempty and at most 1,048,576
bytes. The frame is at most `8 + 1 + 5*(4 + 1,048,576) = 5,242,909` bytes.
Truncation, oversized lengths and any extra frame bytes reject. The Rust entry
validates the entire structure before decoding context, custody state, selected
command and both global states with their existing exact canonical decoders.
Decoded values then enter the typed producer. A malformed disclosure therefore
can reject before a typed economic rejection; a well-formed disclosure's global
relation is checked only after a successful custody transition.

The Python encoder checks route, exact byte types and individual lengths. It
creates a witness frame; it does not attest canonical or economic validity.
There is no new accepted-witness decoder or caller-constructible authority type.

Guest stdin adds one bounded outer `u32LE` length and requires EOF after the
frame. The guest aborts on transport, decoding, transition or refinement failure
and commits exactly the statement bytes on success. No inner self-image field
or recursive receipt is introduced.

## Remaining admission obligations

This is the inner economic payload, not a complete admitted CBC profile. Its
occurrence commits a route release, subject and grant, but hashing those values
does not authenticate them or establish active policy membership. Matching the
predecessor root establishes consistency with the supplied disclosures; current
store authority must be acquired and revalidated by the publication shell.

Qualification still requires the actual rebuilt guest image, genuine receipt
verification of the exact image and journal, explicit release/profile/context
admission, authenticated intent, durable state and atomic publication. A proof
producer or compromised publisher must have no alternate value-writing path.
Native tests and this format do not discharge those obligations.

Retained five-case Python/Rust replay includes custody-bearing transfer, issue,
full account burn preserving custody, dormant issue and return to dormancy.
Regenerate disclosures and independent expected frame hashes with:

```bash
python3 tools/render_asset_lane_custody_statement_v2_golden.py
python3 tools/render_asset_lane_custody_statement_v2_golden.py --check
```
