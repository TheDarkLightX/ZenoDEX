# Rust Functional Core / Imperative Shell Policy V1

## Status

This document and `RUST_VALUE_MOVEMENT_INVENTORY_V1.json` begin the Rust-side
assurance ratchet. They do not claim that the complete Rust core or complete
value-moving system is verified.

The release claim remains **blocked** while any production value-moving surface
is partial CBC, produces incomplete effects, lacks atomic candidate commit, or
has stale semantics relative to the normative transition.

## Normative transition shape

An authoritative Rust transition should have the semantic shape:

```text
step(validated_pre_state, authorized_command, execution_context)
  -> Reject(stable_reject)
   | Accept(transition_candidate)
```

where one immutable candidate owns:

```text
expected_pre_state_root
execution_context_hash
algorithm_version
policy_version

next_state
next_state_root

effects
effects_root

receipt
receipt_root

nonce_updates
outbox_entries
```

The core is responsible for the complete economic decision. The shell may
authenticate external evidence, schedule pure work, compare the expected root,
atomically persist the candidate, and deliver committed outbox entries. It may
not recompute amounts, recipients, fees, claimant identity, ordering, roots, or
rejection semantics.

## Purity and immutability

Local mutation of a newly owned candidate is permitted. Observable mutation of
an accepted pre-state, command, context, global, host resource, or shared
interior-mutable object is prohibited.

Committed state and authoritative command graphs must not contain:

```text
UnsafeCell / Cell / RefCell
Mutex / RwLock / atomics
raw pointers
behavior-bearing trait objects
closures or function pointers
host handles
mutable global state
```

Protocol state should use private fields and checked constructors. Wire DTOs are
not domain values. The core should receive newtypes and enums such as
`AmountE8`, `PriceE8`, `BasisPoints`, `Epoch`, `AccountId`, `AssetId`,
`FinalizedOracle`, and `AuthorizedCommand`.

Distressed but real economic state remains representable. A finalized adverse
price is not a malformed state merely because it triggers liquidation or
recovery behavior.

## Determinism profile

Consensus output must not depend on:

```text
unordered hash iteration
pointer or allocation identity
worker completion order
system time or randomness
environment, filesystem, network, process, or thread state
locale
platform usize width or native endianness
floating-point behavior
debug-versus-release overflow behavior
Debug/Display formatting
serde-derived field order
```

Every arithmetic operation must declare widths, overflow behavior, division and
rounding rules, dust destination, and boundary behavior. Saturating arithmetic
is allowed only when saturation is the specified mathematical rule.

Canonical output uses explicit ordered and versioned byte framing. Authority
parsers consume the complete input and accept only exact canonical re-encodings.

## Policy ratchet

`tools/check_rust_fcis_policy.py` validates:

- exact Rust toolchain pinning;
- committed `Cargo.lock`;
- full inventory coverage of every public core module;
- deployment-profile agreement with the inventory;
- release blocking for partial Rust authority;
- release blocking for value-moving surfaces without proved atomic commit;
- prohibition of unsafe constructs, floats, host I/O, randomness, unordered
  maps, interior mutability, and panic-family calls in production source;
- a bounded temporary exception ledger for four existing `.expect(...)` calls.

The exception ledger is a no-regression ceiling, not an approval. Counts may
decrease; increases fail CI. A released claim may not retain any exception.

## Semantic synchronization rule

Whenever a normative semantic source changes, CI must require either:

```text
Rust implementation updated
+ formal artifact updated when semantics changed
+ differential and independent evidence refreshed
```

or:

```text
affected Rust authority is demoted to python_authority
+ the release claim remains blocked
```

Known immediate examples are the zUSD global debt-cap and finalized-Oracle
repairs. The current inventory records the Rust parity gaps explicitly.

## Value-Movement Closure

Full Rust CBC is necessary but not sufficient. The stronger release condition
is:

```text
for every externally observable value change e,
there exists exactly one authenticated, authorized, accepted, atomically
committed transition whose Rust-owned effect plan contains e, and whose
deterministic effect_id makes delivery idempotent.
```

Value movement includes wallet and pool balances, debt, collateral, LP shares,
fees, rewards, perps positions/PnL/funding, treasury operations, bridges,
proof-market payouts, insurance, migration, recovery, and shutdown behavior.

The complete repository-wide value-path inventory and atomic outbox proof remain
future work. This first inventory is intentionally limited to the current
`zenodex-runtime-core` surface and fails closed rather than claiming closure.

## Promotion rule

A surface may move from Python authority to Rust authority only after:

```text
formal relation defined
Rust entrypoint refines that relation
Python/independent oracle agrees over the admitted domain
complete effects and receipt are Rust-owned
reject is an exact no-candidate result
atomic candidate commit is proved/refined
crash and duplicate-delivery behavior is covered
exact source/toolchain/evidence hashes are bound to the release
```

`rust_authority_with_python_shadow` remains the first load-bearing promotion
mode. Pure `rust_authority` requires sustained zero-disagreement evidence and an
explicit profile/schema decision.
