# PR #477 Committed-State Schema

This file is normative for the PR #477 repair. It defines accepted legacy
ingress values, committed outputs, exact field rules, pure updates, and caller
migration.

## 1. Target type graph

```text
DexState
  balances        CommittedBalanceTableV1
  pools           OwnedMapV1[str, CommittedPoolStateV1]
  lp_balances     CommittedLPTableV1
  nonces          CommittedNonceTableV1
  vault           None | CommittedVaultStateV1
  oracle          None | CommittedOracleStateV1
  fee_accumulator CommittedFeeAccumulatorStateV1
  perps           None | CommittedPerpsStateV1
```

`DexState` remains the committed aggregate and keeps `frozen=True, slots=True`.
Its admission boundary delegates to eight field-specific snapshot functions.
There is no optional-module catch-all.

## 2. Exact committed core inputs

Authority-bearing readers and transitions accept the exact committed classes
listed in section 1. They do not accept structural protocols, mutable source
classes, or unions that include both. This prevents a legacy mutable builder
from satisfying a read-shaped interface and crossing the ownership boundary.

```text
CommittedBalanceTableV1
CommittedLPTableV1
CommittedNonceTableV1
CommittedPoolStateV1
```

Serialization or UI adapters may define non-authoritative projection protocols,
but those protocols cannot appear in the normative core call graph. Core
updates are module-level pure functions with exact committed input and output
types.

## 3. Balance table

### Accepted source

```text
exact BalanceTable
or exact CommittedBalanceTableV1 with matching schema revision
```

For an exact `BalanceTable`, require:

- `type(_balances) is dict` before iteration;
- each key has `type(key) is tuple`, length two;
- `type(pubkey) is str`, `type(asset) is str`;
- identifiers are non-empty and at most the currently mounted field limits;
- `type(amount) is int`, `amount >= 0`;
- zero entries are rejected as noncanonical because mutable `BalanceTable.set`
  omits them;
- duplicate canonical keys are impossible after exact-source validation and
  remain checked during owned construction.

Do not call `get_all_balances`, `set`, comparison, or conversion before these
checks. Read the exact builtin dictionary through trusted direct access.

### Output

`CommittedBalanceTableV1` uses composition. It stores canonical sorted entries
and a fresh private read-only index. It does not inherit `BalanceTable`.

### Pure updates

Balance transitions use a return-new function with an explicit result, for
example `apply_balance_delta(pre, key, add, sub) -> Reject | CommittedBalanceTableV1`.
There is no public conversion back to `BalanceTable`.

### Numeric nonclaim

The existing balance model has no source-pinned semantic upper bound beyond
bounded snapshot bytes. PR #477 enforces exact nonnegative integers and the
mounted entry/byte limits. `BALANCE-UPPER-BOUND` remains open; the agent must not
invent a monetary cap.

## 4. LP table

### Accepted source

```text
exact LPTable
or exact CommittedLPTableV1
```

Require exact builtin dictionaries for:

```text
_balances
_last_mint_timestamps
_last_remove_timestamps
_churn_tiers
_last_churn_update_timestamps
```

Every key is an exact two-string tuple `(pubkey, pool_id)`. Every numeric value
is an exact nonnegative integer. Additional invariants:

- zero LP balances are absent;
- a last-mint timestamp exists only for a positive LP balance;
- churn tier zero is absent from sparse storage;
- metadata maps use the same canonical key language;
- all maps together stay within `max_lp_balances=200_000` under the mounted
  snapshot accounting rule;
- LP amounts and supply respect existing `DEX_LP_*` domain constants wherever
  the mounted transition already requires them.

### Output and pure updates

`CommittedLPTableV1` uses five owned maps behind one read-only aggregate. It
does not inherit `LPTable`. LP transitions return a new committed aggregate and
update balances, mint timestamps, remove timestamps, churn tiers, and
churn-update timestamps as one candidate before invariant checking.

## 5. Nonce table

### Accepted source

```text
exact NonceTable
or exact CommittedNonceTableV1
```

Require `type(_last) is dict`, exact non-empty string pubkeys, exact integers,
and `0 <= nonce <= 0xffffffff`. Use canonical key order. Do not call
`canonical_hex_fixed_allow_0x` on a string subclass; exact string admission
comes first.

### Output and pure updates

`CommittedNonceTableV1` uses composition and does not inherit `NonceTable`.
Nonce validation and application accept the exact committed type. Application
returns a new committed nonce table or a typed rejection; it never mutates or
reconstructs `NonceTable`.

## 6. Pools

### Accepted source map

```text
exact dict[str, PoolState]
or exact OwnedMapV1 with schema_id = "zenodex/pools/v1"
```

The source dictionary is bounded by `max_pools=50_000`. Validate every key as
an exact non-empty string before sorting. Each value must have
`type(value) is PoolState`; `FrozenPoolState` and any subclass from the old PR
are not grandfathered.

### Pool record schema

| Field | Rule |
| --- | --- |
| `pool_id` | exact non-empty string; existing pool-ID format and identity rule |
| `asset0` | exact non-empty string |
| `asset1` | exact non-empty string; existing canonical pair rule |
| `reserve0` | exact int, `0..DEX_POOL_RESERVE_MAX` |
| `reserve1` | exact int, `0..DEX_POOL_RESERVE_MAX` |
| `fee_bps` | exact int, `0..10_000` |
| `lp_supply` | exact int, `0..DEX_LP_SUPPLY_MAX` |
| `status` | exact `PoolStatus` |
| `created_at` | exact nonnegative int |
| `curve_tag` | exact non-empty string accepted by current curve registry |
| `curve_params` | exact canonical string accepted by current curve registry |

Order of operations:

1. exact record type;
2. exact scalar/enum fields;
3. numeric/string bounds;
4. `normalize_curve_config` validation without accepting a changed spelling;
5. `validate_pool_identity` under the same profile as the caller;
6. construct distinct `CommittedPoolStateV1`.

Do not call `copy_pool_state` before admission. The committed pool does not
inherit `PoolState`. Batch clearing computes an immutable pool patch or a new
`CommittedPoolStateV1` from the exact committed pre-state. Application returns
the complete committed pool map as part of the same candidate.

## 7. Vault, Oracle, and fee accumulator

These records contain only scalars, but they still receive distinct committed
records so source and committed stages remain explicit.

### Vault

Accepted source: `None`, exact `VaultState`, or exact
`CommittedVaultStateV1`.

| Field | Rule |
| --- | --- |
| `acc_reward_per_share` | exact nonnegative int |
| `last_update_acc` | exact nonnegative int |
| `pending_rewards` | exact nonnegative int |
| `reward_balance` | exact nonnegative int |
| `staked_lp_shares` | exact nonnegative int |

Run the current vault invariant set after construction. This ownership PR does
not repair the separate claimant/accumulator economic model.

### Oracle

Accepted source: `None`, exact `OracleState`, or exact
`CommittedOracleStateV1`.

| Field | Rule |
| --- | --- |
| `price_timestamp` | exact nonnegative int |
| `max_staleness_seconds` | exact positive int |

This snapshot does not establish timestamp authority; consensus-context
provenance remains a separate obligation.

### Fee accumulator

Accepted source: exact `FeeAccumulatorState` or exact
`CommittedFeeAccumulatorStateV1`. `dust` is an exact nonnegative integer and
must satisfy any current split invariant.

## 8. Perps exhaustive registry

### Top level

Accepted source: `None`, exact `PerpsState`, or exact
`CommittedPerpsStateV1`.

`PerpsState` fields:

| Field | Rule |
| --- | --- |
| `version` | exact int accepted by the mounted perps version registry |
| `markets` | exact dict, at most 10,000 entries, canonical exact-string keys |

Each market value dispatches by exact record type. The allowed source record
types are exactly:

```text
PerpMarketState
PerpClearinghouse2pMarketState
PerpClearinghouse3pTransferMarketState
PerpClearinghouseNpMarketState
```

The output types are distinct committed counterparts. A `kind` string never
selects a Python class before the exact record type is known; the exact type and
exact `kind` literal must agree.

### Isolated market

`PerpMarketState` fields:

| Field | Rule |
| --- | --- |
| `quote_asset` | exact non-empty string |
| `global_state` | exact dict with exactly `PERP_ISOLATED_GLOBAL_KEYS` |
| `accounts` | exact dict, total perps account limit 200,000 |
| `kind` | exact string equal to `isolated_v2` |

Global state rules:

- keys are exact strings and the key set is exact;
- `breaker_active`, `clearing_price_seen`, and `oracle_seen` are exact bools;
- `epoch_phase` is exact int in `{0, 1, 2}`; string and 0/1 compatibility
  normalization is decode-stage behavior and rejects here;
- every other declared value is an exact integer;
- each integer uses the current perps kernel/domain bound for that named field;
- construct the exact immutable committed candidate after admission and run a
  pure semantic invariant predicate over its fields;
- no constructor-added default is permitted at committed admission; all fields
  must already be present.

Accounts use exact `PerpAccountState` and the declared fields:

```text
position_base                exact bounded int
entry_price_e8               exact nonnegative bounded int
collateral_quote             exact nonnegative bounded int
funding_paid_cumulative      exact bounded int
funding_last_applied_epoch   exact nonnegative bounded int
liquidated_this_step         exact bool
```

Run current account and market consistency invariants after construction.

### Two-party and three-party clearinghouses

Require exact outer record type, exact canonical quote asset/pubkeys, exact
literal `kind`, and an exact builtin state dictionary whose key set equals the
corresponding `PERP_CLEARINGHOUSE_*_STATE_KEYS` constant.

Boolean keys use the corresponding exact bool-key registry. Every other value
is an exact integer and uses the current field/domain bounds. Run parameter
ordering, distinct-account, net-position, collateral, fee-pool, and
net-deposited conservation invariants through the trusted constructor and
explicit postcheck.

### N-party clearinghouse

Require:

- exact `PerpClearinghouseNpMarketState`;
- exact quote asset and literal kind;
- exact builtin `global_state` dictionary with its current exact key registry;
- exact tuple of exact `PerpClearinghouseNpAccount` records;
- exact tuple of exact `PerpClearinghouseNpPendingIntent` records;
- total account and pending-intent limits;
- canonical unique pubkey/nonce/order rules already owned by the N-party
  constructor;
- exact scalar checks on every account and pending-intent field before calling
  that constructor.

The registry-drift test must compare every dataclass field set and every
global-state key set with the schema manifest. Adding a perps field or variant
must fail tests until this schema, encoder, decoder, proof/ref adapter, and
evidence mapping are updated.

## 9. DexState admission order

`DexState.__post_init__` executes in this fixed order:

```text
1. balances
2. pools
3. LP balances
4. nonces
5. vault
6. oracle
7. fee accumulator
8. perps
9. aggregate state invariant check
10. canonical state-size check
```

The function builds all eight owned candidates first. It assigns them to the
frozen aggregate only after every field succeeds. If a field rejects, no
partially admitted `DexState` escapes.

## 10. Caller migration

### Pure readers and transitions

Update authority-bearing reader annotations to exact committed classes.
State-root, support-root, snapshot encoding, quote validation, and settlement
validation read those immutable values directly.

Replace each mutating path with a return-new transition:

```text
committed pre-state
  -> deterministic calculation of immutable domain patches
  -> validate complete candidate
  -> new committed state + exact effects + receipt
```

High-risk callers include batch clearing/application, Tau gate settlement,
perps integration, zUSD monetary bridge, testnet plugin, and nonce application.
Search all direct calls to `set`, `add`, `subtract`, pool field assignment,
`dataclasses.replace`, mutable table copy helpers, and `to_scratch_*`. Replace
them at a domain boundary rather than hiding them behind a compatibility
protocol.

### Forbidden compatibility shortcut

Do not make committed types inherit mutable types so old annotations continue
to pass. Do not add mutator methods that always raise, expose a structural
protocol accepted by both stages, or create a public mutable projection. Update
the contract and callers explicitly.

## 11. Observable compatibility

For every canonical valid pre-state already accepted at the pinned base:

```text
canonical_snapshot_before == canonical_snapshot_after
state_root_before          == state_root_after
support_root_before        == support_root_after
step_acceptance_before     == step_acceptance_after
post_state_bytes_before    == post_state_bytes_after
effect_bytes_before        == effect_bytes_after
```

Intentional rejection expansion is limited to malformed, behavior-bearing,
cyclic, oversized, unregistered, noncanonical, or alias-unsafe inputs named in
the audit. Any other observable delta requires a separate decision record.
