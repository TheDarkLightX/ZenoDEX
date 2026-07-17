---
name: zenodex-pattern-selector
description: >-
  Concrete, agent-facing pattern-selection guide for ZenoDEX code generation.
  Teaches functional core / imperative shell (FCIS) through three independent
  axes: authority, lifetime/ownership, and failure semantics. Covers pure
  deterministic authoritative core, transitively immutable state, mutable
  local builders, typed rejections, imperative shell with atomic commit,
  effect plans, refactoring preflight, representation rules, and Rust
  guidance. Use BEFORE writing or editing any value-moving, state-carrying,
  or transition code in any language in the repo. Reference files in this
  skill provide before/after examples and the full preflight checklist.
---

# ZenoDEX Pattern Selector

This skill teaches functional core / imperative shell (FCIS) for agents that
generate code. It exists to prevent the mutability, stringly-typed, and
silent-value-loss bugs found in the immutability audit.

For before/after examples and migration guardrails, read
`reference/before-after-examples.md`. For the full refactoring preflight
checklist, read `reference/refactoring-preflight.md`.

## FCIS foundation

The system is many small core/shell pairs, not one enormous core and shell.
A perps engine, a zUSD vault, and a spot DEX each have their own boundary.

```text
Imperative shell
  acquire bytes, authenticate transport, capture consensus inputs,
  load snapshot
      ↓
Functional core
  parse canonical domain values, verify authorization/replay/freshness,
  decide acceptance, calculate amounts, produce post-state + effect plan
      ↓
Imperative shell
  atomically commit state + effects + nonce + receipt using the pre-root
```

Dependencies point inward. A shell function may call pure core functions.
A pure core function never calls shell or I/O. If one function contains both,
extract the deterministic decision into a separate pure function.

The validation boundary has three layers:

1. **Shell:** acquire bytes/evidence, enforce transport/resource limits.
2. **Pure decoder/smart constructors:** canonical syntax and domain types.
   A parser that takes already-acquired bytes and returns a typed result
   without IO is functional core, not shell.
3. **Authoritative core:** authorization, admission, signatures/proofs,
   freshness, replay, and economics.

The rule: `src/core/**` must not import from `src/integration/**`.

## Three independent axes

Every piece of code has three independent properties. Decide each separately.

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
  Acquiring bytes from the network, subprocess calls, filesystem, clock.
  The shell never decides settlement semantics.
```

A Python `def` doing filesystem access is still imperative shell. An
immutable value object with pure methods is functional core. A local mutable
builder inside a pure computation is core when it is exclusively owned, never
escapes, and the function remains observationally pure.

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

`frozen=True` is one Python mechanism, not the definition. The actual
requirement is: no retained mutable aliases, no mutable contents, no mutation
after construction. `MappingProxyType` is a read-only view, not an immutable
value — if the backing dict is retained elsewhere, it can still be mutated.

### Axis 3: Failure semantics — what kind of failure is this?

```text
Expected protocol rejection (stale oracle, expired intent, violated
invariant, wrong proof binding)?
→ Typed outcome. Return a discriminated result with a RejectCode enum
  and immutable structured details.

Operational I/O failure (network down, file missing, subprocess crash)?
→ Shell error/retry policy. Retry must be idempotent or explicitly
  non-idempotent with a safe replay rule.

Violated internal invariant after trusted construction?
→ Exception. This is a programmer error, not a protocol path. Raise
  ValueError/TypeError (survives python -O). Never use assert. In Rust,
  panic is acceptable for internal invariant violations but never for
  attacker-reachable inputs.
```

Whether a range failure is a rejection or an exception depends on the trust
boundary: malformed transaction input is a rejection; the same value after
construction of a validated domain type is an internal invariant failure.

### Rejection does not always mean "do not persist"

Distinguish two cases:

- **No-commit rejection:** pre-state and effects remain untouched. The
  caller discards the result and retries from the same pre-state.
- **Committed failure:** protocol semantics consume a nonce or charge a fee
  even on rejection. The result type must indicate that state was committed.

The skill's shell template assumes no-commit rejection. If a transition has
committed-failure semantics, the result type must say so explicitly.

### Common compositions

- **Impure-pure-impure sandwich (shell → core → shell):** The canonical
  ZenoDEX flow. Shell acquires bytes and loads snapshot → core decides and
  produces post-state + effect plan → shell atomically commits.
- **Core + typed rejection:** A value-moving transition that can reject.
- **Core with internal mutable builder:** A pure function using local
  scratch space. Observationally pure from the caller's perspective.
- **Pure parser + typed rejection:** A parser taking already-acquired bytes,
  returning a typed domain value or rejection. Core, not shell.
- **Shell + typed rejection:** A shell handler that acquires raw input,
  calls core, returns a typed result.

---

## Mandatory invariants for authoritative state

These apply to every type that escapes, persists, hashes, signs, or enters a
receipt.

1. **Transitive immutability.** No retained mutable aliases, no mutable
   contents, no mutation after construction.
2. **No stringly-typed state bags.** Every field is a named, typed field on
   a frozen dataclass. No `Dict[str, Any]` as a state representation.
3. **Transitions return a new state.** Use `replace()`. When refactoring a
   mutable API (e.g., `add() -> None`) to immutable, use a deliberately
   different method name (e.g., `with_delta()`) to prevent silent value-loss
   at call sites that ignore the return value.
4. **Integer-only arithmetic.** No floats in consensus, accounting,
   settlement, core state, proof, or verifier paths.
5. **No assert for runtime validation.** Use explicit guards that return
   typed rejections or raise `ValueError`/`TypeError`.
6. **Canonical encoding independently of in-memory representation.** If data
   is hashed or signed, require a single canonical encoding per semantic
   value. The canonical encoding is an ABI.
7. **Effect plans are first-class.** An accepted transition returns a
   transitively immutable, canonical, asset-qualified effect plan. Deltas
   are aggregated by `(principal, asset, custody-domain)` before commitment.
   Conservation is checked across the complete plan. The transition binds
   pre-root, command, post-root, effect-plan hash, and replay identity. The
   shell applies the core's exact effects once; it must not reconstruct
   economic amounts. External effects require a transactional outbox plus
   idempotent delivery.

---

## Representation rules

"Use sorted tuples instead of dicts" is too mechanical. Choose by semantics:

| Semantic type | Representation rule |
|---|---|
| Ordered sequence | Immutable tuple in protocol-defined order. Never sort automatically. |
| Set (no duplicates) | Define duplicate policy and canonical total order. `frozenset` is immutable but not canonically ordered across languages. |
| Dynamic map | Persistent/immutable map, canonical tuple, or privately owned map behind an immutable API. For large hot state, preserve complexity. |
| Hash/signature encoding | Canonicalize by specified bytes via a versioned protocol encoder. Do not rely on in-memory iteration order. |
| Large hot state | Preserve O(1) lookup. A tuple turns balance lookups into O(n); repeated updates become O(n²). Benchmark before replacing maps with tuples. |

A tuple permits duplicate keys and can contain mutable elements. A privately
owned map with canonical serialization may be safer and faster than an
immutable tuple with linear updates. Using a dictionary should trigger
classification and verification, not an automatic tuple rewrite.

---

## Typed rejections

For new authoritative code, use a discriminated result with a `RejectCode`
enum and immutable structured details:

```python
class RejectCode(Enum):
    NEGATIVE_AMOUNT = "negative_amount"
    INSUFFICIENT_BALANCE = "insufficient_balance"
    # ...

@dataclass(frozen=True)
class StepOk:
    state: MyState
    effect_plan: MyEffectPlan

@dataclass(frozen=True)
class StepReject:
    code: RejectCode
    details: RejectDetails  # frozen dataclass, not str

def step(state: MyState, command: MyCommand) -> StepOk | StepReject:
    ...
```

Legacy boolean/string results (e.g., `ok: bool`, `error: str | None`) are
migration targets, not exemplars. Do not cite them as typed-rejection
patterns. Do not mix Result APIs in the same function.

Negative tests assert the rejection enum, not the error message string.

---

## Mutable builder rules

A mutable builder is acceptable when:

1. Honestly mutable (`@dataclass` without `frozen=True`).
2. Freshly constructed per computation.
3. Never aliased with committed state. Copying the outer container is not
   enough — nested mutable values must also be copied.
4. Discarded on rejection.
5. Output at the boundary is transitively immutable.

### Repository status (do not copy as templates)

The following types are **unsafe migration targets** at the current commit.
Do not present them as correct exemplars. They are listed here so agents
know what needs fixing:

- `src/core/settlement.py` — `Fill`, `BalanceDelta`, `ReserveDelta`,
  `LPDelta`, `Settlement` are `@dataclass` (NOT frozen) with `List` fields
  and `Optional[List[Dict[str, Any]]]` events. They are mutable.
- `src/core/batch_clearing_compute.py` — `_build_settlement_from_buffers`
  passes builder lists directly into `Settlement` without tuple conversion.
- `src/core/batch_clearing_single_pool.py` — `_SinglePoolRuntime` returns
  its mutable `fills` list directly.
- `src/integration/perp_engine.py` — `_build_perp_apply_ctx` copies the
  outer `markets` dict but nested `PerpMarketState` values remain aliased.
- `src/core/batch_clearing.py` — `_copy_lp_table` copies balances and mint
  timestamps but drops remove timestamps, churn tiers, and churn-update
  timestamps. Even an empty settlement can erase duration-risk metadata.
  `apply_settlement_pure` uses this lossy copier and returns mutable types.
- `src/state/balances.py` — `BalanceTable` is a mutable class with
  in-place `add()`/`subtract()`/`set()` that return `None`.
- `src/core/zusd.py` — `ZUSDStepResult` uses `ok: bool`, `error: str | None`
  with `Mapping[str, Any]` effects. Legacy boolean/string result, not a
  discriminated typed result.

**Correct builder pattern (safe to copy):**
- `src/state/support_root.py` — `_SupportAccumulator` with mutable `set`
  fields, produces immutable `BatchStateSupport` (frozen dataclass with
  sorted tuples) at the boundary.

---

## Imperative shell rules

1. **Parse-don't-validate at the boundary.** Convert raw input into typed
   domain objects once, then pass typed objects to the core.
2. **The shell never decides settlement semantics.**
3. **Capture external time, randomness, and IO once, label them, pass them
   explicitly inward.**
4. **Exhaustive result handling.** Handle both `StepOk` and `StepReject`
   explicitly. Do not assume every non-reject is success.
5. **Atomic commit with compare-and-swap.** The shell must call an explicit
   commit operation that takes the expected pre-root and version, the
   post-state, the effect plan, and the replay record. The commit returns
   `CommitOk` (with receipt) or `CommitConflict`. See
   `reference/before-after-examples.md` for the correct template.
6. **External effects require a transactional outbox** plus idempotent
   delivery. Persisting the effect plan is not the same as executing it.
7. **Retries must be idempotent** or explicitly non-idempotent with a safe
   replay rule.
8. **Demo paths must never become authority.**

---

## Refactoring preflight

Before editing existing value-moving or state-carrying code, record:

1. Exact artifact being changed.
2. Authority and commit boundaries.
3. Constructors, mutation sites, and retained aliases.
4. Public APIs and callers.
5. Snapshot/wire serialization and canonical encoding.
6. State-root, hash, signature, and proof consumers.
7. Python/Rust parity consumers.
8. Existing order, duplicate, rounding, and rejection semantics.
9. Current complexity and performance budget.
10. Representation-only or intentionally semantic? Separate patches.
11. **CAS/concurrency:** what happens on concurrent commits? Is there a
    compare-and-swap on the expected pre-root/version?
12. **Crash points:** what happens if the process crashes between persisting
    state and delivering external effects? Is there an outbox?
13. **Outbox/idempotence:** are external effects delivered exactly-once?
    What is the replay key?
14. **Conservation postconditions:** does the transition verify that
    `sum(post) == sum(pre) + sum(external_in) - sum(external_out)`?
15. **Retained-alias tests:** is there a test that verifies no mutable alias
    from the pre-state survives into the post-state?
16. **Deterministic activation/versioning:** does the commit record the
    exact code version and activation epoch?
17. **Forward recovery:** if new consensus state was committed and the
    process crashed, what is the recovery procedure? "Rollback" is unsafe
    once new state is committed.

See `reference/refactoring-preflight.md` for the full checklist.

---

## Rust guidance

- **Maps:** `BTreeMap` supplies deterministic key iteration order, not
  canonical bytes. Canonical wire encoding requires a versioned protocol
  encoder with explicit widths, normalization, and field/tag encoding. Do
  not rely on `BTreeMap` iteration order or Serde struct field order for
  canonical bytes. Do not use `HashMap` for state that will be hashed or
  serialized canonically.
- **Interior mutability:** `Cell`/`RefCell` for single-threaded scratch
  space inside a builder. Neither belongs in the authoritative core.
- **Checked arithmetic:** Use `checked_add`, `checked_sub`, `checked_mul`
  for all value-moving arithmetic. Python/Rust integer-domain parity must
  be verified — Python ints are arbitrary precision, Rust ints overflow.
- **Enum discriminants:** "Never reorder variants" only matters if ordinal
  discriminants are explicitly part of the versioned protocol encoding. If
  they are, state that explicitly. New variants are trailing.
- **`#[must_use]`** on returned transitions and effect plans.
- **No panic for attacker-reachable inputs.** Return `Result<T, E>`.
  `panic!`/`unwrap`/`expect` are for internal invariant violations only.
- **Ownership moves preserve replayable pre-state.** Take `&State`, return
  owned `State`.
- **Python/Rust golden vectors:** any canonical encoding change requires
  golden vectors that verify both sides produce identical bytes.

---

## Quick reference for agents

When generating code, ask yourself:

1. **Does this code decide or bind value?** → Pure deterministic core. No IO,
   no floats, no hidden state. If the function does IO, it is shell. Extract
   the pure decision into a separate function.
2. **Does this value escape, persist, hash, or sign?** → Transitively
   immutable. Frozen dataclass with immutable field types.
3. **Is this fresh, function-local scratch space?** → Mutable builder
   permitted. Honestly mutable, discarded after use, immutable output at
   boundary.
4. **Can this step reject with a typed reason?** → Typed result with
   `RejectCode` enum. Negative tests assert the enum.
5. **Am I using `Dict` or `List` inside a `@dataclass(frozen=True)`?** → Do
   not commit this form. Reclassify: either make the fields immutable or
   make the builder honestly mutable. Continue after the invariants pass.
6. **Am I using `Dict[str, Any]` as a state type?** → Do not commit this
   form. Replace with a frozen dataclass with named fields.
7. **Am I mutating a state object in place?** → Do not commit this form. Use
   `replace()` to return a new state. The only exception is a local builder
   that is discarded after use.
8. **Am I using `assert` for runtime validation?** → Do not commit this form.
   Use explicit guards that return typed rejections or raise
   `ValueError`/`TypeError`.
9. **Am I using floats in value-moving math?** → Do not commit this form.
   Use integer base units with explicit scale, rounding, and dust policy.
10. **Am I refactoring an existing mutable API to immutable?** → Use a
    deliberately different method name. Run the refactoring preflight.
11. **Am I persisting only state and dropping the effect plan?** → Do not
    commit this form. The shell must atomically commit state + effect plan +
    nonce + receipt via compare-and-swap.
12. **Am I adding a pattern because it is familiar?** → Do not commit this
    form. Use the smallest pattern that makes the boundary clearer. Judge
    observable properties (purity, immutability, ownership, authority), not
    style labels.

---

## Reference files

- `reference/before-after-examples.md` — concrete before/after code,
  including the correct shell template with compare-and-swap commit, and
  the BalanceTable migration with `with_delta()` API.
- `reference/refactoring-preflight.md` — full preflight checklist.
