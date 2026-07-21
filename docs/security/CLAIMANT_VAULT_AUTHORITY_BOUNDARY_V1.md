# Claimant Vault Authority Boundary V1

## Audit defect

The legacy `src/core/vault.py` and its generated bounded reference store one
global share count and accept a caller-supplied `entry_acc` during harvest. They
do not contain claimant identity, per-account shares, reward debt, activation
state, a claim nonce, or an owned reward lot. Agreement between that runtime and
its generated specification therefore proves the wrong multi-user relation: a
caller can ask the aggregate model to compute rewards over all global shares.

The legacy module is retained only for bounded generated-reference parity and
historical research. Its code now declares:

```text
LEGACY_AGGREGATE_VAULT_MULTI_USER_AUTHORITY = False
```

No production profile may treat the legacy `VaultState` or `harvest(entry_acc)`
result as claimant authority.

## Replacement functional core

`src/core/vault_claimant.py` introduces a claimant-indexed immutable state:

```text
claimant -> active_shares
claimant -> pending_shares
claimant -> reward_debt
claimant -> claimable
claimant -> last_nonce
```

and aggregate state:

```text
acc_reward_per_share
reward_balance
explicit_residue
cumulative_deposited
cumulative_claimed
cumulative_drained
last_funding_nonce
```

Every constructor rederives and checks:

```text
total_active_shares = sum(account.active_shares)
total_pending_shares = sum(account.pending_shares)

owned(account)
  = account.claimable
  + floor(account.active_shares * accumulator / scale)
  - account.reward_debt

aggregate_owned = sum(owned(account))
reward_balance = aggregate_owned + explicit_residue

cumulative_deposited
  = reward_balance + cumulative_claimed + cumulative_drained
```

All persisted values are U256-bounded. Products use a U512 intermediate before
exact integer division.

## User requirements represented

### Existing staker

Funding increases the accumulator over the exact active-share total. The
claimant's owned reward is derived from their own shares and reward debt.
Claiming settles and clears only that claimant.

### Late staker

Shares enter `pending_shares` first. Activation moves them to active shares and
sets reward debt at the current accumulator, so the activated shares have zero
historical entitlement.

### Unstaking staker

Unstake settles the account before reducing active shares. Already earned value
moves into `claimable` and cannot be erased by changing the share balance.

### Protocol reward funder

Funding has its own exact sequential nonce. Every deposited atom is either
claimant-owned or explicit residue. Deposits made without active stakers remain
residue and are not silently granted to a later staker.

### Terminal operator

Explicit residue can leave only through `DrainResidue`, and only when active,
pending, and claimant-owned balances are all zero. The returned transfer is an
effect value, not an executed transfer.

## FCIS interpretation

The core accepts already authenticated values and returns either:

```text
ClaimantVaultStepResult(ok=False, state=None, effects=None, error=...)
```

or:

```text
ClaimantVaultStepResult(
  ok=True,
  state=immutable_next_state,
  effects=immutable_exact_transfer_plan,
)
```

The imperative shell remains responsible for:

- authenticating the funder or claimant;
- verifying that LP shares or reward assets are actually available;
- comparing the expected pre-state root;
- atomically committing state, replay nonce, receipt, and outbox;
- delivering the returned transfers idempotently.

The shell must not recompute reward entitlement or substitute a different
transfer amount.

## Evidence in this PR

The focused suite covers:

- two stakers where the late staker cannot claim the first deposit;
- three staggered stakers with exact `150 / 60 / 30` ownership;
- pending activation across a historical deposit;
- unstake preserving earned rewards;
- exact-nonce replay and skipped-nonce rejection as no-ops;
- claim-order independence;
- tiny-reward rounding and explicit residue;
- terminal residue-drain conditions;
- forged ownership, duplicate claimants, canonical ordering, and immutability;
- an executable assertion that the legacy aggregate model has no multi-user
  authority.

## Remaining promotion work

This PR does not yet mount the claimant state into the canonical `DexState`
snapshot or replace the generated vault YAML/reference artifacts. Production
promotion still requires:

1. a versioned snapshot migration that refuses nonzero legacy aggregate vaults,
   because claimant identities cannot be reconstructed;
2. an authenticated shell command format and atomic state/effect/outbox commit;
3. generated Python/Rust refinement from one source contract;
4. bounded ESSO/TLA exploration over claimant vectors and command permutations;
5. Lean proofs for accumulator ownership, residue, and conservation;
6. differential replay between generated and mounted implementations.

Until those gates close, `vault_claimant` is the correct claimant relation and
the legacy aggregate model remains explicitly non-authoritative, but no complete
production vault claim is made.
