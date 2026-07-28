# FCIS M5-P4B5A preflight

Status: `FROZEN_BEFORE_SOURCE_EDIT`

Start head:

```text
6c4e7c6be89f76605e86c5532a4841d5e271611b
```

Branch:

```text
agent/codex-fcis-m5-p4b5a-fee-custody-20260728
```

Worktree:

```text
/tmp/zenodex-fcis-m5-p4b5a-fee-custody-20260728
```

## Invariant

For each exact custody key `k = (source_pubkey, asset)`:

```text
fresh_protocol_credit[k] + retained_dust[k]
  =
buyback[k] + treasury[k] + rewards[k] + next_dust[k]
```

No term for one key may be combined with a term for another key.

The balance candidate applies:

```text
source[k] -= buyback[k] + treasury[k] + rewards[k]
destination(role, k) += role_amount[k]
```

Residual dust remains in `source[k]`.

## Authority boundary

The exact strong-settlement replay owns fee-credit derivation. It uses the
admitted intent input asset, recomputed protocol fee, and authenticated
settlement-context recipient from one replay lineage.

The fee leaf transition consumes only exact immutable values and returns one
typed rejection or one owned candidate. The shell receives no independent
instruction to recreate or reapply the distribution.

## Trusted evidence layers

Required:

1. Source-derived minimized counterexamples for both audit findings.
2. Exact value and transition tests.
3. Per-key conservation, partition, alias, and rejection properties.
4. Structural checker and mechanism mutation tests.
5. Canonical encoding golden vectors.
6. Direct Python/Rust byte parity.

The legacy scalar implementation is a negative oracle and migration input. It
does not decide the V2 semantics.

## Refactoring preflight

### What behavior is wrong?

The current evaluator sums every `fill.fee_paid` into one scalar. That erases
asset units and includes LP-owned fees that were never credited to protocol
custody.

### Which layer owns the repair?

Exact replay owns credit derivation. A dedicated fee-custody transition owns
per-key splitting and balance application. Admission and codec modules own
untrusted source conversion. Decision and bundle code may only retain the
already derived exact values.

### What must remain unchanged?

- Mounted DEX and integration behavior.
- The legacy scalar implementation and its evidence artifacts.
- Existing exact AMM, route, settlement, nonce, and patch arithmetic.
- Rejection atomicity and canonical state-root rules outside the new version.

### What new abstraction pays for itself?

One bounded per-custody fee machine removes two confirmed accounting defects
and makes the conservation law independently testable. The abstraction is
restricted to protocol fee custody. It is not a general money framework.

### What is the simplest safe migration?

Only zero scalar dust can migrate because nonzero V1 dust has no recoverable
asset or owner. The migration emits an empty V2 accumulator. Any nonzero scalar
dust rejects.

### Which alternate designs were rejected?

- Attaching one asset after scalar summation: fails for mixed assets and routes.
- Splitting `fee_paid`: spends LP-owned value.
- Keying dust by asset only: loses custody when the protocol recipient changes.
- Emitting shell transfers without changing the balance candidate: permits
  partial publication and double execution.
- Guessing an asset for old dust: silently creates authority.
- Treating buyback as an implicit asset conversion: no authenticated market,
  price, or execution relation exists.

## Current source observations

- `src/core/fcis_step_evaluator.py::_total_settlement_fees_v1` sums
  `fill.fee_paid`.
- `_fee_candidate_observed_v5` passes that scalar to the dust-carry splitter.
- `CommittedFeeAccumulatorStateV1` stores one scalar `dust`.
- `FCISFeeAllocationV1` stores four unitless integers.
- `OwnedDexEffectsV1` commits one scalar `total_swap_fees`.
- Ordinary exact swap replay recomputes `protocol_fee_paid` and credits the
  configured protocol recipient in `asset_in`.
- Route replay records per-leg assets and total LP fees but creates no protocol
  fee credit.
- The current fee policy has basis points only and names no destination
  custodians.

## Tool triage

The style classifier returned no path-specific rule for the worktree paths, so
the strict value-moving profile applies.

The security red-flag scanner reported zero findings across the initial eight
files. This is triage only.

Design metrics identified existing large-file and long-function debt in the
evaluator, decision derivation, authority dispatch, and state snapshot values.
New fee semantics should live in focused modules. Existing broad functions
should receive narrow orchestration changes only.

## Nonclaims

This preflight does not close P4B5A, authorize mounting, prove datastore
atomicity, close context provenance, close nonce policy, or establish
cross-language parity.
