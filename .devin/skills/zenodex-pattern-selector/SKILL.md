---
name: zenodex-pattern-selector
description: >-
  Concrete, agent-facing pattern-selection guide for ZenoDEX code generation.
  Answers "which code pattern do I use right now, and what does it look like?"
  Uses three independent axes (authority, lifetime/ownership, failure semantics)
  instead of a mutually-exclusive taxonomy. Covers: pure deterministic
  authoritative core, transitively immutable state, mutable local builders,
  typed rejections, imperative shell, effect plans, refactoring preflight,
  representation rules, and Rust guidance. Use BEFORE writing or editing any
  value-moving, state-carrying, or transition code in any language in the repo.
  Routes to zenodex-design-principles for the underlying rationale,
  zenodex-style-map for directory routing, and the reference files in this
  skill for before/after examples and migration guardrails.
---

# ZenoDEX Pattern Selector

This skill answers a single question: **which code pattern do I use right now,
and what does it look like?** It is written for agents that generate code, to
prevent the mutability and stringly-typed bugs found in the immutability audit.

For the underlying "why", read `zenodex-design-principles`. For "which
directory am I in", read `zenodex-style-map`. For before/after examples and
migration guardrails, read `reference/before-after-examples.md` and
`reference/refactoring-preflight.md`.

## Three independent axes

Every piece of code has three independent properties. Decide each one
separately.

### Axis 1: Authority — does this code decide or bind value?

```text
Does it decide or bind admission, authorization, amounts, fees, ordering,
freshness, replay, roots, or an effect plan?
→ Pure deterministic authoritative core.
  No IO, no wall clock, no randomness, no network, no filesystem, no
  global mutable state, no floats. Integer-only arithmetic with explicit
  rounding and dust policy. Output depends only on inputs.

Does it acquire external input or execute an already-decided effect?
→ Imperative shell.
  Parsing, validation, subprocess calls, network, filesystem, clock.
  The shell never decides settlement semantics. It validates at the
  boundary, calls the core, and emits effects.
```

A single function can be pure core in its arithmetic but call into shell for
IO. The boundary between them is what matters: `src/core/**` must not import
from `src/integration/**`.

### Axis 2: Lifetime and ownership — does this value escape?

```text
Does the value escape, persist, hash, sign, cache, or enter a receipt?
→ Transitively immutable.
  @dataclass(frozen=True) with only immutable field types: int, bool, str,
  Enum, tuple, frozenset, or other frozen dataclasses. No Dict, no List,
  no mutable class fields. Transitions return a new value via replace().

Is it fresh, exclusively owned, function-local scratch space?
→ Mutable builder permitted inside either core or shell.
  Honestly mutable (@dataclass without frozen=True, or a plain class).
  Freshly constructed per computation. Never aliased with committed state.
  Discarded on rejection. Produces immutable output at the boundary.
```

The key question is not "is this a builder?" but "does this value escape to a
context where someone else holds a reference?" If yes, it must be transitively
immutable. If no, honest mutation is fine.

### Axis 3: Failure semantics — what kind of failure is this?

```text
Expected protocol rejection (stale oracle, expired intent, violated
invariant, wrong proof binding)?
→ Typed outcome. Return a discriminated result with a RejectCode enum
  and immutable structured details. The caller handles both tracks.

Operational I/O failure (network down, file missing, subprocess crash)?
→ Shell error/retry policy. Retry must be idempotent or explicitly
  non-idempotent with a safe replay rule.

Violated internal invariant after trusted construction (out-of-domain
int after a validated type was already constructed)?
→ Exception. This is a programmer error, not a protocol path. Raise
  ValueError/TypeError (survives python -O). Never use assert for
  runtime validation. In Rust, panic is acceptable for internal
  invariant violations but never for attacker-reachable inputs.
```

Whether a range failure is a rejection or an exception depends on the trust
boundary: malformed transaction input is a rejection; the same value after
construction of a validated domain type is an internal invariant failure.

### Common compositions

These are the most frequent combinations in the codebase:

- **Authoritative core + typed rejection (A1+C1):** A value-moving transition
  that can reject. This is the most common pattern in `src/core/`. Example:
  `src/core/zusd.py` `step()` returns `ZUSDStepResult` with `ok`, `state`,
  `error` fields.
- **Authoritative core with internal mutable builder (A1+B):** A pure function
  that uses local mutable scratch space internally. Example:
  `src/state/support_root.py` `_SupportAccumulator` builds an immutable
  `BatchStateSupport` at the boundary.
- **Shell + typed rejection (D+C1):** A shell handler that parses, validates,
  calls core, and returns a typed result. Example: `src/integration/zusd_api.py`
  HTTP handlers.

---

## Mandatory invariants for authoritative state

These apply to every type that escapes, persists, hashes, signs, or enters a
receipt. They are safety requirements, not style preferences.

### 1. Transitive immutability

`@dataclass(frozen=True)` with only immutable field types. `frozen=True` is one
Python mechanism, not the definition. The actual requirement is: no retained
mutable aliases, no mutable contents, no mutation after construction.

`MappingProxyType` is a read-only view, not an immutable value — if the
backing dict is retained elsewhere, it can still be mutated. A canonical sorted
tuple or purpose-built immutable map is stronger.

### 2. No stringly-typed state bags

Every field is a named, typed field on a frozen dataclass. No
`Dict[str, Any]` or `Dict[str, Value]` as a state representation. Missing keys
silently return `None` or a default; named fields are visible at construction
time and checkable by the type system.

### 3. Transitions return a new state, never mutate in place

Use `dataclasses.replace(state, field=value)`. Never write `state.field = value`
or `state.balances.add(...)` on committed state.

When refactoring a mutable API (e.g., `BalanceTable.add() -> None`) to an
immutable API, use a deliberately different method name (e.g., `with_delta()`)
to prevent silent value-loss at existing call sites that ignore the return
value. See `reference/before-after-examples.md` for the migration pattern.

### 4. Integer-only arithmetic

No floats in consensus, accounting, settlement, core state, proof, or verifier
paths. Use integer base units with explicit scale, rounding, and dust policy.

### 5. No assert for runtime validation

`assert` vanishes under `python -O`. Use explicit guards that return typed
rejections or raise `ValueError`/`TypeError`.

### 6. Canonical encoding independently of in-memory representation

If data is hashed or signed, require a single canonical encoding per semantic
value. Define normalization rules (ordering, trimming, sentinel
representations). The canonical encoding is an ABI — changing it breaks
signatures and state roots.

### 7. Effect plans are first-class

An accepted authoritative transition returns a transitively immutable,
canonical, asset-qualified effect plan. Deltas are aggregated by
`(principal, asset, custody-domain)` before commitment. Conservation is checked
across the complete plan. The transition binds pre-root, command, post-root,
effect-plan hash, and replay identity.

The shell applies the core's exact effects once; it must not reconstruct
economic amounts.

---

## Representation rules

"Use sorted tuples instead of dicts" is too mechanical. Choose by semantics:

| Semantic type | Representation rule |
|---|---|
| Ordered sequence | Immutable tuple in protocol-defined order. Never sort automatically. |
| Set (no duplicates) | Define duplicate policy and canonical total order. `frozenset` is immutable but not canonically ordered across languages. |
| Dynamic map | Persistent/immutable map, canonical tuple, or privately owned map behind an immutable API. For large hot state, preserve complexity — benchmark before replacing maps with tuples. |
| Hash/signature encoding | Canonicalize by specified bytes, independently of in-memory representation. |
| Large hot state | Preserve O(1) lookup complexity. Benchmark before replacing maps with linear-scan tuples. |

A tuple permits duplicate keys, can contain mutable elements, and turns balance
lookups into O(n) operations. For a 10-key market config, a sorted tuple is
fine. For a 100,000-entry balance table, a tuple is quadratic. Choose by the
actual access pattern and size.

---

## Typed rejections

For new authoritative code, use a discriminated result with a `RejectCode`
enum and immutable structured details:

```python
class RejectCode(Enum):
    NEGATIVE_AMOUNT = "negative_amount"
    INSUFFICIENT_BALANCE = "insufficient_balance"
    STALE_ORACLE = "stale_oracle"
    EXPIRED_INTENT = "expired_intent"
    # ...

@dataclass(frozen=True)
class StepOk:
    state: MyState
    effect: MyEffect

@dataclass(frozen=True)
class StepReject:
    code: RejectCode
    details: RejectDetails  # frozen dataclass, not str

def step(state: MyState, command: MyCommand) -> StepOk | StepReject:
    if command.amount < 0:
        return StepReject(code=RejectCode.NEGATIVE_AMOUNT, details=...)
    return StepOk(state=new_state, effect=...)
```

Legacy boolean/string results (`rejection: str | None`, `(ok, reason)` tuples)
can remain behind compatibility adapters. Do not mix Result APIs in the same
function — the shell example in `reference/before-after-examples.md` shows the
correct exhaustive handling pattern.

Negative tests assert the rejection enum, not the error message string.

---

## Mutable builder rules

A mutable builder is acceptable inside either core or shell when:

1. **Honestly mutable.** `@dataclass` without `frozen=True`, or a plain class.
   Never `@dataclass(frozen=True)` on a mutable builder — the `frozen=True` flag
   is a lie if the fields are `list` or `dict`.
2. **Freshly constructed per computation.** Never reused across batches,
   transactions, or requests.
3. **Never aliased with committed state.** If the builder holds a
   `BalanceTable`, it must be a deep copy, not the original. Copying the outer
   container is not enough — nested mutable values must also be copied.
4. **Discarded on rejection.** If the computation fails, the builder is thrown
   away. The pre-state is untouched.
5. **Output at the boundary is transitively immutable.** The builder produces
   a frozen dataclass with tuple fields, not a mutable list or dict.

### Repository exemplars

**Correct builder pattern:**
- `src/state/support_root.py:58-63` — `_SupportAccumulator` with mutable `set`
  fields, produces immutable `BatchStateSupport` (frozen dataclass with sorted
  tuples) at the boundary.
- `src/core/settlement.py:336-360` — `Settlement` is
  `@dataclass(frozen=True, init=False)` with `tuple[Fill, ...]` fields. `Fill`,
  `BalanceDelta`, `ReserveDelta`, `LPDelta` are all `@dataclass(frozen=True)`
  with immutable fields. This is a transitively immutable boundary type.

**Transitional exemplars (not yet safe, do not copy as templates):**
- `src/core/batch_clearing_compute.py:30-37` — `_SettlementBuffers` is honestly
  mutable, but its output path must convert lists to tuples at the Settlement
  boundary (this is done correctly today, but the builder itself is not a
  general-purpose safe template).
- `src/core/batch_clearing_single_pool.py:71-76` — `_SinglePoolRuntime` is
  honestly mutable and returns `runtime.fills` (a mutable `List[Fill]`) directly.
  The caller converts to tuple when building `Settlement`, but the runtime
  itself does not enforce the immutable-boundary contract.
- `src/integration/perp_engine.py:7396-7428` — `_build_perp_apply_ctx` copies
  the outer `markets` dict but nested `PerpMarketState` values remain aliased
  to the original state. Operationally careful today (frozen dataclass prevents
  field reassignment), but `global_state: Dict[str, Value]` inside
  `PerpMarketState` is still mutable and aliased. Do not copy as a general
  ownership template.
- `src/core/batch_clearing.py:496-512` — `apply_settlement_pure` copies before
  mutating, but returns mutable `BalanceTable`, `dict`, and `LPTable`. The
  copy-then-mutate pattern is correct in spirit, but the return types are not
  transitively immutable.

---

## Imperative shell rules

1. **Parse-don't-validate at the boundary.** Convert raw input into typed
   domain objects once, then pass typed objects to the core.
2. **The shell never decides settlement semantics.** Business rules belong in
   the core.
3. **Capture external time, randomness, and IO once, label them, pass them
   explicitly inward.** The core never reads the clock or environment.
4. **Exhaustive result handling.** The shell must handle both success and
   rejection from the core. See `reference/before-after-examples.md` for the
   correct shell template.
5. **Atomic commit.** The shell must atomically commit: expected pre-root/
   version, post-state, complete typed effect plan, nonce/replay record, and
   receipt or effect-plan hash. Persisting only state and dropping the effect
   plan is a bug.
6. **Retries must be idempotent** or explicitly non-idempotent with a safe
   replay rule.
7. **Demo paths must never become authority.** Module-level mutable state in
   demo/audit code is acceptable for testing but must not be promoted to
   production.

---

## Refactoring preflight

Before editing existing value-moving or state-carrying code, record:

1. **Exact artifact being changed** — not merely its directory.
2. **Authority and commit boundaries** — what does this code decide or bind?
3. **Constructors, mutation sites, and retained aliases** — who constructs,
   who mutates, who holds a reference?
4. **Public APIs and callers** — what breaks if the API changes?
5. **Snapshot/wire serialization** — does changing the representation break
   canonical encoding?
6. **State-root, hash, signature, and proof consumers** — does changing the
   representation break any hash or signature?
7. **Python/Rust parity consumers** — does changing one side break parity?
8. **Existing order, duplicate, rounding, and rejection semantics** — must
   be preserved unless the change is intentionally semantic.
9. **Current complexity and performance budget** — does the refactor change
   Big-O? Benchmark before replacing maps with tuples on hot paths.
10. **Representation-only or intentionally semantic?** Representation and
    semantic changes should be separate patches. No opportunistic neighboring
    refactors.

Committed or wire-visible changes require a schema version/migration and
golden vectors. See `reference/refactoring-preflight.md` for the full
checklist.

---

## Rust guidance

The skill applies to Rust code in `zk/state_proof_risc0/**` and any future
Rust surfaces. Rust-specific rules:

- **Maps:** Use `BTreeMap` for canonically ordered key-value state. Use
  `Vec` only for ordered sequences where order is protocol-defined. Do not
  use `HashMap` for state that will be hashed or serialized canonically
  (iteration order is non-deterministic).
- **Interior mutability:** `Cell`/`RefCell` for single-threaded scratch space
  is acceptable inside a builder. `Mutex`/`RwLock` for shared state is shell
  territory. Neither belongs in the authoritative core.
- **Checked arithmetic:** Use `checked_add`, `checked_sub`, `checked_mul`
  for all value-moving arithmetic. Python/Rust integer-domain parity must be
  verified — Python ints are arbitrary precision, Rust ints overflow.
- **Stable enum discriminants:** Enum discriminants are part of the canonical
  encoding. Do not reorder variants. New variants are trailing.
- **Canonical Serde encoding:** Derive `Serialize`/`Deserialize` with
  explicit field order. Use `#[serde(rename_all = "snake_case")]` for
  stable wire names. Do not rely on struct field order for canonical bytes.
- **`#[must_use]` on returned transitions and effect plans:** Prevents
  silently ignoring a returned state or effect.
- **No panic for attacker-reachable inputs:** Return `Result<T, E>` for
  any input that crosses a trust boundary. `panic!`/`unwrap`/`expect` are
  for internal invariant violations only, never for attacker-controlled data.
- **Ownership moves preserve replayable pre-state:** The pre-state must not
  be consumed by the transition. Take `&State`, return `State` (owned new
  value), or take `State` by value and return a new `State` (the caller
  retains the old one if they cloned it before the call).

---

## Quick reference for agents

When generating code, ask yourself:

1. **Does this code decide or bind value?** → Pure deterministic core. No IO,
   no floats, no hidden state.
2. **Does this value escape, persist, hash, or sign?** → Transitively
   immutable. Frozen dataclass with immutable field types.
3. **Is this fresh, function-local scratch space?** → Mutable builder
   permitted. Honestly mutable, discarded after use, immutable output at
   boundary.
4. **Can this step reject with a typed reason?** → Typed result with
   `RejectCode` enum. Negative tests assert the enum.
5. **Am I using `Dict` or `List` inside a `@dataclass(frozen=True)`?** → Stop.
   This is the frozen lie. Use `tuple` or make the builder honestly mutable.
6. **Am I using `Dict[str, Any]` as a state type?** → Stop. This is a
   stringly-typed bag. Use a frozen dataclass with named fields.
7. **Am I mutating a state object in place?** → Stop. Use `replace()` to
   return a new state. The only exception is a local builder that is
   discarded after use.
8. **Am I using `assert` for runtime validation?** → Stop. Use explicit
   guards that return typed rejections or raise `ValueError`/`TypeError`.
9. **Am I using floats in value-moving math?** → Stop. Use integer base
   units with explicit scale, rounding, and dust policy.
10. **Am I refactoring an existing mutable API to immutable?** → Use a
    deliberately different method name (e.g., `with_delta()` not `add()`).
    Existing call sites that ignore the return value would silently stop
    moving value. Run the refactoring preflight (see above).
11. **Am I persisting only state and dropping the effect plan?** → Stop.
    The shell must atomically commit state + effect plan + nonce/replay
    record + receipt hash.
12. **Am I adding a pattern because it is familiar?** → Stop. Use the
    smallest pattern that makes the boundary clearer. Judge observable
    properties (purity, immutability, ownership, authority), not style
    labels (FP, OOP, KISS).

---

## Reference files

- `reference/before-after-examples.md` — concrete before/after code for each
  pattern, including the correct shell template, BalanceTable migration with
  `with_delta()` API, and anti-patterns.
- `reference/refactoring-preflight.md` — full preflight checklist for
  refactoring value-moving code.
