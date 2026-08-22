# Economic Initial-State RISC0 Guest

This workspace contains the bounded RISC0 3.0.6 guest and host verifier for an
`EconomicInitialStateJournalV1`. The guest checks the canonical typed input,
the exact explicit-row coverage statement, predecessor-state binding, and the
bounded replay, terminal-obligation, and outbox-preservation relations, then
commits the canonical journal. The host requires the measured method image, a Succinct receipt, the
exact journal bytes, and successful receipt verification.

## Fast contract gate

The placeholder build compiles and tests the shared and host contracts. It
cannot produce or verify a real receipt.

```bash
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
```

## Real proof and byte replay

Run this on the proof machine with `RISC0_SKIP_BUILD` and `RISC0_DEV_MODE`
unset:

```bash
cargo test --locked \
  -p zenodex-economic-initial-state-risc0-host \
  --test real_proof \
  real_economic_initial_state_proves_and_replays_the_exact_journal \
  -- --ignored --exact --nocapture
```

The ignored test builds the real guest method, derives an input that names the
measured image, produces a Succinct receipt, verifies it, canonically encodes
and decodes the receipt, verifies the decoded receipt again, and constructs the
initialization certificate with a range-checked declared cycle budget. It
reports the image, method and receipt hashes, serialized sizes, host-observed
RISC0 cycle counts, and elapsed time. The reported cycle counts are diagnostics.
Receipt verification does not authenticate host-reported performance metadata
or establish a release-selected `max_cycles` ceiling.

## Claim boundary

```text
MOUNT_STATUS = UNMOUNTED
PRODUCTION_AUTHORITY = NONE
WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY = UNPROVED
```

This guest covers the explicit target global-state rows currently enumerated by
the initial-state ABI: balances, supplies, accounting-control-domain rows,
liabilities, reserves, and terminal obligations. A migration input must also
disclose the full predecessor `GlobalEconomicStateV1`; the guest recomputes its
state root and binds its chain, deployment, profile, writer epoch and height to
the public journal. This is a predecessor-content commitment.

The guest does not prove that the disclosed predecessor is the finalized ledger
head. For replay state, genesis requires an empty replay table and migration
preserves every disclosed predecessor replay row unchanged. The derived public
root commits the complete predecessor and target replay tables. Target-only
replay rows remain unauthenticated and can consume future identifiers, so this
relation does not establish full nonce or nullifier continuity.

For external-effect outbox state, genesis requires an empty table and migration
requires exact preservation of every row, including delivery status, under a
4,096-row preflight bound. Migration-time enqueue, deletion, acknowledgment or
compaction rejects. This relation does not prove that a source row came from an
authorized effect, or that external delivery, finality, retry, acknowledgment
and destination idempotency are correct.

For terminal obligations, genesis commits the complete target table whose rows
must also be classified by the initial-state atom manifest. Migration requires
exact preservation of the complete predecessor table. Creation, deletion,
claimant, lane, asset, amount, status, or order changes reject under the common
4,096 explicit-row preflight ceiling. The relation does not establish that an
obligation is valid, funded, controlled by the named claimant, reachable through
a payable terminal route, or correctly drained or tombstoned before migration.

The guest also does not prove private lane-root contents, predecessor migration
classification totality, source authorization legitimacy, Oracle continuity,
private-lane nullifiers, ledger-history continuity, terminal-obligation
validity and payable-path completeness, external delivery, mounted writer
exclusivity, or
whole-economy value-movement safety.
