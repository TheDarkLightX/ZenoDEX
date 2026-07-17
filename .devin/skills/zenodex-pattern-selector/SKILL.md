---
name: zenodex-pattern-selector
description: >-
  Concrete, agent-facing pattern-selection guide for ZenoDEX code generation.
  Answers "which code pattern do I use right now, and what does it look like?"
  Covers: pure immutable deterministic functions (what they are, when to use
  them, when not to), mutable local builders (when mutation is honest),
  railway-oriented programming (when to use Result vs exceptions), KISS vs FP
  vs OOP (which is better and when), and the frozen-dataclass immutability
  rules that prevent the mutability bugs found in the immutability audit.
  Use BEFORE writing or editing any value-moving, state-carrying, or
  transition code in any language in the repo. Routes to zenodex-design-principles
  for the underlying rationale and zenodex-style-map for the directory routing.
---

# ZenoDEX Pattern Selector

This skill answers a single question: **which code pattern do I use right now,
and what does it look like?** It is written for agents that generate code, to
prevent the mutability and stringly-typed bugs found in the immutability audit.

For the underlying "why" behind each pattern, read
`zenodex-design-principles`. For "which directory am I in and what style
applies there", read `zenodex-style-map`. This skill is the concrete "what to
type" layer.

## The four patterns

Every piece of code in this repo falls into exactly one of four patterns. Pick
the pattern by answering two questions:

1. **Does this code move value, decide settlement, or carry committed state?**
   (Yes = Pattern A. No = continue.)
2. **Is this a short-lived computation buffer inside a single batch/transaction?**
   (Yes = Pattern B. No = continue.)
3. **Is this a fallible boundary or transition step that can reject?**
   (Yes = Pattern C. No = continue.)
4. **None of the above** (parsing, IO, tooling, UI, research) = Pattern D.

```text
Does it move value or carry committed state?
├── YES → Pattern A: Pure Immutable Deterministic Function
└── NO
    └── Is it a short-lived computation buffer?
        ├── YES → Pattern B: Local Mutable Builder (honestly mutable)
        └── NO
            └── Is it a fallible boundary or transition step?
                ├── YES → Pattern C: Railway/Result
                └── NO → Pattern D: Imperative Shell
```

---

## Pattern A: Pure Immutable Deterministic Function

### What it is

A function that:

1. **Pure** — no side effects. No IO, no network, no filesystem, no wall clock,
   no randomness, no environment variables, no global mutable state, no logging.
   The function's output depends only on its inputs.
2. **Immutable** — every state value is a frozen dataclass whose fields are all
   immutable types (`int`, `bool`, `str`, `Enum`, `tuple`, `frozenset`, or
   other frozen dataclasses). No `Dict`, no `List`, no mutable class fields.
   The function does not mutate its inputs. It returns a new state.
3. **Deterministic** — same inputs always produce the same output. No hidden
   state, no mutation, no side effects. The function can be replayed with the
   same inputs and the output is guaranteed identical.

### Signature shape

```python
@dataclass(frozen=True)
class MyState:
    field_a: int
    field_b: str
    accounts: tuple[tuple[str, AccountState], ...]  # sorted, immutable

@dataclass(frozen=True)
class MyCommand:
    action: MyAction  # Enum
    amount: int

@dataclass(frozen=True)
class MyResult:
    state: MyState
    effect: MyEffect

def step(state: MyState, command: MyCommand) -> MyResult:
    # guards
    # compute new state
    new_state = replace(state, field_a=state.field_a + command.amount)
    return MyResult(state=new_state, effect=MyEffect(...))
```

### When to use it

- **Value-moving state transitions**: settlement, mint/burn/redeem, swap math,
  liquidation, funding, margin checks, conservation invariants.
- **Committed state types**: any type that represents a snapshot of system
  state that will be hashed, signed, persisted, or replayed.
- **Core math**: AMM output amounts, fee splits, LP ratios, funding rates,
  liquidation penalties, compensation splits.
- **Proof witnesses and receipt bodies**: anything that feeds a hash or
  signature.

### When NOT to use it

- When the code does IO (file, network, subprocess, clock) — that is Pattern D.
- When the code is a short-lived computation buffer that is freshly constructed,
  never aliased with committed state, and discarded after use — that is
  Pattern B.
- When the code is at a fallible boundary that must return a typed rejection —
  that is Pattern C (which is Pattern A plus a Result return type).

### Rules

1. **Every state type is `@dataclass(frozen=True)` with only immutable field
   types.** Allowed: `int`, `bool`, `str`, `Enum`, `tuple`, `frozenset`,
   other frozen dataclasses. Forbidden: `Dict`, `List`, `set`, mutable classes.
   A `Mapping` annotation is acceptable only if the backing object is a
   copied-and-frozen dict that is never retained elsewhere; a canonical sorted
   tuple is stronger.

2. **Transitions return a new state, never mutate in place.** Use
   `dataclasses.replace(state, field=value)` to produce a new state. Never
   write `state.field = value` or `state.balances.add(...)`.

3. **Collections are sorted tuples, not dicts.**
   ```python
   # BAD: mutable, non-deterministic iteration
   accounts: Dict[str, AccountState]

   # GOOD: immutable, canonical iteration
   accounts: tuple[tuple[str, AccountState], ...]  # sorted by key
   ```

4. **No stringly-typed state bags.** Every field is a named, typed field on a
   frozen dataclass. No `Dict[str, Any]` or `Dict[str, Value]` as a state
   representation.
   ```python
   # BAD: missing keys silently return None
   global_state: Dict[str, Value]

   # GOOD: every field is named and typed
   global_state: PerpGlobalState  # frozen dataclass with named fields
   ```

5. **Integer-only arithmetic.** No floats in consensus, accounting, settlement,
   core state, proof, or verifier paths. Use integer base units with explicit
   scale, rounding, and dust policy.

6. **No `assert` for runtime validation.** Use explicit guards that return
   typed rejections or raise `ValueError`/`TypeError` (which survive
   `python -O`).

### Repository examples

- `src/core/perp_v2/types.py` — `PerpState` is a frozen dataclass with only
  `int`, `bool`, `Enum` fields. The correct reference model.
- `src/core/zusd.py` — `ZUSDState` and `ZUSDMultiState` are frozen dataclasses
  with only `int` and `bool` fields.
- `src/core/perp_v4/` — all types frozen, all math pure, transitions via
  `replace()`.
- `src/core/cross_shard_decision_certificate.py` — frozen dataclasses with
  `str`, `int`, `Enum`, `tuple` fields only.
- `src/core/cpmm.py` — pure CPMM math over integer reserves.

### What goes wrong when you don't use it

The immutability audit (`IMMUTABILITY_AUDIT.md`) found 22 findings caused by
violating these rules:

- `PoolState` was mutable (`@dataclass` not frozen) — reserves mutated in place
  during settlement, risking snapshot corruption.
- `BalanceTable` was a mutable class with `set`/`add`/`subtract` — balances
  mutated in place, risking aliasing bugs.
- `PerpMarketState.global_state` was a `Dict[str, Value]` — missing keys
  silently returned defaults, hiding incomplete state construction.
- `Intent.fields` was a `Dict[str, Any]` — stringly-typed bag with no
  compile-time field checking.
- `Settlement` was mutable — fills and deltas could be mutated after validation.

---

## Pattern B: Local Mutable Builder (honestly mutable)

### What it is

A mutable object that accumulates results during a computation, then produces
an immutable output at the boundary. The builder is freshly constructed for
each computation, never aliased with committed state, and discarded after the
immutable output is produced.

### Signature shape

```python
@dataclass  # honestly mutable — no frozen=True
class _SettlementBuffers:
    fills: list[Fill]
    balance_deltas: list[BalanceDelta]
    reserve_deltas: list[ReserveDelta]

def compute_settlement(...) -> Settlement:
    buffers = _SettlementBuffers(fills=[], balance_deltas=[], ...)
    # ... accumulate into buffers ...
    return Settlement(
        fills=tuple(buffers.fills),           # immutable at boundary
        balance_deltas=tuple(buffers.balance_deltas),
        ...
    )
```

### When to use it

- **Batch clearing internals**: accumulating fills, deltas, and events during
  a single batch computation.
- **Support root derivation**: accumulating keys and IDs while scanning intents.
- **Settlement application**: applying deltas to a working copy of state before
  producing the committed post-state.
- **Any computation where the intermediate accumulator is short-lived, freshly
  owned, and never shared with committed state.**

### When NOT to use it

- When the builder's state is committed state (use Pattern A).
- When the builder escapes its construction scope (use Pattern A).
- When the builder is aliased with a prior snapshot (use Pattern A).
- When the builder is retained after a rejection (use Pattern A — the builder
  must be discarded, and the pre-state must be untouched).

### Rules

1. **The builder is honestly mutable.** Do not write `@dataclass(frozen=True)`
   on a builder. The `frozen=True` flag is a lie if the fields are `list` or
   `dict`. Either make it `@dataclass` (honestly mutable) or refactor to
   functional accumulation.

2. **The builder is freshly constructed per computation.** Never reuse a
   builder across batches, transactions, or requests.

3. **The builder is never aliased with committed state.** If the builder holds
   a `BalanceTable`, it must be a copy, not the original.

4. **The builder is discarded on rejection.** If the computation fails, the
   builder is thrown away. The pre-state is untouched.

5. **The output at the boundary is immutable.** The builder produces a frozen
   `Settlement`, frozen `BatchStateSupport`, or other immutable type. The
   caller never sees the mutable builder.

6. **The observationally pure boundary is preserved.** From the caller's
   perspective, the function is pure: same inputs always produce the same
   output. The internal mutation is an implementation detail.

### Repository examples

- `src/state/support_root.py:58-63` — `_SupportAccumulator` with mutable `set`
  fields, produces immutable `BatchStateSupport` (frozen dataclass with sorted
  tuples) at the boundary. Correct builder pattern.
- `src/core/batch_clearing_compute.py:30-37` — `_SettlementBuffers` is
  honestly `@dataclass` (not frozen), accumulates fills/deltas, feeds into
  `Settlement` at the boundary. Correct builder pattern.
- `src/core/batch_clearing_single_pool.py:70-76` — `_SinglePoolRuntime` is
  honestly mutable, accumulates fills and reserves, feeds into the fill list
  at the boundary. Correct builder pattern.
- `src/core/batch_clearing.py:496-512` — `apply_settlement_pure` copies state
  before mutating, returns the copy. The original is untouched. Correct
  copy-then-mutate-then-return pattern.

### What goes wrong when you lie about it

- `src/core/batch_clearing_compute.py:40-45` — `_SettlementExecutionState` is
  `@dataclass(frozen=True)` but holds `Dict`, `BalanceTable`, and
  `_SettlementBuffers` (mutable). The `frozen=True` flag is misleading. It
  should be `@dataclass` (honestly mutable) since it is a builder.

---

## Pattern C: Railway / Result

### What it is

A function that returns a typed result: either a success carrying a value, or
a failure carrying a typed rejection reason. The caller handles both tracks
explicitly. Failures short-circuit the pipeline without exceptions or nested
`if` ladders.

### Signature shape

```python
@dataclass(frozen=True)
class StepOk:
    state: MyState
    effect: MyEffect

@dataclass(frozen=True)
class StepError:
    code: str   # stable rejection code
    message: str

def step(state: MyState, command: MyCommand) -> StepOk | StepError:
    if command.amount < 0:
        return StepError(code="negative_amount", message="amount must be non-negative")
    # ... compute ...
    return StepOk(state=new_state, effect=MyEffect(...))
```

### When to use it

- **Fallible boundaries**: parsing, validation, command acceptance.
- **Transition steps that can reject**: deposit, withdraw, swap, liquidate,
  mint, burn, redeem.
- **Anywhere the rejection reason is part of the protocol contract** and tests
  must assert *why* it failed.
- **Anywhere a failure should short-circuit a pipeline** without exceptions.

### When NOT to use it

- **Inside a pure core function guarding a precondition** that the type system
  cannot express (e.g., `require_int_range` raising `ValueError` on an
  out-of-domain int — a contract violation, not a protocol path). Use
  exceptions here.
- **For programmer errors or tool/infrastructure failures** (misconfiguration,
  missing binary, bug). Use exceptions or `panic!` in Rust.
- **In UI code** — errors are surfaced as UI state, not Result types.
- **As a blanket framework** — do not wrap every simple value in a custom
  result type. Do not build a monad framework in Python.

### Rules

1. **Use Result/railway for domain errors, not for everything.** A domain error
   is a protocol outcome the system must handle and tests must assert. A
   programmer error is a bug that should surface loudly.

2. **Rejection reasons are typed and stable.** Use an `Enum` or a frozen
   dataclass with a `code` field. Do not use generic `ValueError` or
   `RuntimeError` to drive protocol behavior on critical paths.

3. **Negative tests assert the rejection class/code.** Do not assert on error
   message strings (they change). Assert on the typed rejection.

4. **In Rust, use native `Result<T, E>` and `Option<T>`.** The `?` operator is
   railway propagation. Do not build a custom result type.

5. **In Python, use small typed results or `(ok, reason)` tuples.** Do not
   build a monad framework. Do not wrap every value in a result type.

### Repository examples

- `src/core/perp_v2/types.py:156-158` — `StepResult` is a frozen dataclass
  with `state` and `effect` fields. The engine returns `StepResult` or raises
  `ValueError` for contract violations.
- `src/core/zusd.py` — `step()` returns `ZUSDStepResult` with `ok`, `state`,
  `error` fields. Rejection reasons are typed strings.
- `src/kernels/python/*_native_adapter.py` — ESSO adapters return `StepOk` /
  `StepError` from the interpreter.
- `zk/state_proof_risc0/**` — native Rust `Result<T, E>` and `Option<T>`.

---

## Pattern D: Imperative Shell

### What it is

Code that performs IO, parsing, subprocess calls, network access, filesystem
operations, clock reads, and other side effects. The shell validates and
translates external input into typed commands, calls the functional core, and
emits effects. The shell never decides settlement semantics.

### Signature shape

```python
def handle_request(raw_input: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    # 1. Parse and validate at the boundary
    command = parse_command(raw_input)  # Pattern C: returns typed result
    if not command.ok:
        return 400, {"error": command.reason}

    # 2. Load state (IO)
    state = load_state_from_snapshot()

    # 3. Call functional core (Pattern A)
    result = step(state, command.value)

    # 4. Persist state (IO)
    if result.ok:
        save_state(result.state)

    # 5. Return response
    return 200, {"state": serialize(result.state)}
```

### When to use it

- **API handlers**: HTTP request parsing, response formatting.
- **Snapshot serialization**: loading and saving state from disk/database.
- **Subprocess invocation**: calling Tau, RISC0, ESSO tools.
- **Oracle ingestion**: reading external price feeds.
- **Wallet/signature surfaces**: signing and verifying transactions.
- **Demo/audit harnesses**: in-memory state for testing.

### When NOT to use it

- **In the functional core.** The core must not import from the shell.
  `src/core/**` must not import from `src/integration/**`.
- **For value-moving math.** Use Pattern A.
- **For committed state types.** Use Pattern A.

### Rules

1. **The shell validates at the boundary.** Parse-don't-validate: convert raw
   input into typed domain objects once, then pass typed objects to the core.

2. **The shell never decides settlement semantics.** Business rules belong in
   the core. The shell is an adapter.

3. **The shell captures external time, randomness, and IO once, labels them,
   and passes them explicitly inward.** The core never reads the clock or
   environment.

4. **The shell may use mutable context objects** as long as they are freshly
   owned, transaction-local, non-escaping, and discarded on rejection. The
   committed state produced at the boundary must be immutable (Pattern A).

5. **Retries must be idempotent** or explicitly non-idempotent with a safe
   replay rule.

6. **Demo paths must never become authority.** Module-level mutable state in
   demo/audit code is acceptable for testing but must not be promoted to
   production.

### Repository examples

- `src/integration/perp_engine.py` — `_PerpApplyCtx` is a mutable context
  object used for transaction-local state. Acceptable as shell.
- `src/integration/zusd_api.py` — HTTP handler that parses requests, calls the
  zUSD core, and returns responses.
- `src/integration/zusd_monetary_bridge.py` — production monetary bridge that
  calls the zUSD core with shutdown extension.
- `src/integration/validation.py` — shell-side acceptance gate that returns
  `(ok, reason)` then delegates to the core.

---

## KISS vs FP vs OOP — which is better?

**None is universally better. The right pattern depends on the authority and
risk surface of the code, not on taste.**

### KISS (Keep It Simple, Stupid)

KISS is a tiebreaker, not a pattern. It says: when two patterns are equally
safe for the authority surface, pick the simpler one. It does not say: always
pick the simplest code regardless of risk.

- **Use KISS as a tiebreaker** when Pattern A and Pattern B are both safe for
  the surface and Pattern B is simpler.
- **Do not use KISS to justify mutable state in the functional core.** A
  mutable `BalanceTable` is simpler than an immutable sorted-tuple
  `BalanceTable`, but it is not safe for committed state. KISS does not
  override the authority surface.
- **Do not use KISS to justify stringly-typed state bags.** A
  `Dict[str, Value]` is simpler than a frozen dataclass with named fields, but
  it hides missing fields and weakens the type system. KISS does not override
  make-invalid-states-unrepresentable.

### Functional Programming (FP)

FP is the correct style for the functional core (Pattern A). Pure functions,
immutable data, no side effects. This is not a preference — it is a safety
requirement for value-moving code.

- **Use FP for**: value-moving state transitions, committed state types, core
  math, proof witnesses, receipt bodies.
- **Do not use FP for**: IO, parsing, subprocess calls, network access (use
  Pattern D).
- **Do not use FP as a blanket framework**: do not build a monad framework in
  Python, do not wrap every value in a custom result type, do not force
  railway-oriented programming where a simple exception is clearer.

### Railway-Oriented Programming (ROP)

ROP is a specific FP technique for error handling. It is Pattern C. Use it at
fallible boundaries and transition steps where a typed rejection improves
auditability and negative testing.

- **Use ROP for**: domain errors that the protocol must handle and tests must
  assert.
- **Do not use ROP for**: programmer errors, tool failures, UI errors, or as a
  blanket framework.

### Object-Oriented Programming (OOP)

OOP is the correct style for the imperative shell (Pattern D) and for builders
(Pattern B). Mutable objects with methods are honest about their mutability.

- **Use OOP for**: API handlers, snapshot serializers, subprocess wrappers,
  wallet/signature surfaces, demo harnesses.
- **Do not use OOP for**: the functional core. Mutable objects with methods
  that mutate internal state are not safe for committed state.
- **Do not use OOP to hide mutation behind a frozen facade.** A
  `@dataclass(frozen=True)` with `Dict` fields is OOP pretending to be FP. It
  is the worst of both worlds: the immutability is a lie, and the mutation is
  hidden.

### Decision table

| Code surface | Pattern | Style | KISS applies? |
|---|---|---|---|
| Value-moving transition | A | FP (pure, immutable) | No — safety requirement |
| Committed state type | A | FP (frozen dataclass) | No — safety requirement |
| Core math | A | FP (pure function) | Yes — pick simplest safe formula |
| Proof witness / receipt body | A | FP (frozen, hash-bound) | No — safety requirement |
| Batch computation buffer | B | OOP (honestly mutable) | Yes — pick simplest accumulator |
| Support root derivation | B | OOP (honestly mutable) | Yes |
| Fallible boundary | C | ROP (typed Result) | Yes — pick simplest result type |
| Transition step that can reject | C | ROP (typed Result) | No — rejection reason is a contract |
| API handler | D | OOP (imperative shell) | Yes |
| Snapshot serialization | D | OOP (imperative shell) | Yes |
| Subprocess invocation | D | OOP (imperative shell) | Yes |
| Demo/audit harness | D | OOP (imperative shell) | Yes |

---

## The frozen-dataclass immutability rules

These rules prevent the mutability bugs found in the immutability audit. They
apply to every state type in Pattern A.

### Rule 1: Every state type is `@dataclass(frozen=True)`

```python
# BAD
@dataclass
class PoolState:
    reserve0: int
    reserve1: int

# GOOD
@dataclass(frozen=True)
class PoolState:
    reserve0: int
    reserve1: int
```

### Rule 2: Every field is an immutable type

```python
# BAD: Dict is mutable even inside a frozen dataclass
@dataclass(frozen=True)
class DexState:
    pools: Dict[str, PoolState]       # frozen lie
    balances: BalanceTable             # mutable class

# GOOD: tuple and frozen dataclass only
@dataclass(frozen=True)
class DexState:
    pools: tuple[tuple[str, PoolState], ...]    # sorted, immutable
    balances: BalanceTable                       # after BalanceTable is made frozen
```

### Rule 3: Collections are sorted tuples, not dicts

```python
# BAD: mutable, non-deterministic iteration
accounts: Dict[str, AccountState]

# GOOD: immutable, canonical iteration
accounts: tuple[tuple[str, AccountState], ...]  # sorted by key
```

### Rule 4: No stringly-typed state bags

```python
# BAD: missing keys silently return None
global_state: Dict[str, Value]

# GOOD: every field is named and typed
@dataclass(frozen=True)
class PerpGlobalState:
    now_epoch: int
    fee_pool_quote: int
    insurance_balance: int
    # ... every key that was in the Dict
```

### Rule 5: Transitions return a new state, never mutate in place

```python
# BAD: mutates in place
pool.reserve0 += amount
balances.add(pubkey, asset, delta)

# GOOD: returns a new state
new_pool = replace(pool, reserve0=pool.reserve0 + amount)
new_balances = balances.add(pubkey, asset, delta)  # returns new BalanceTable
```

### Rule 6: Local mutable builders are honestly mutable

```python
# BAD: frozen lie on a mutable builder
@dataclass(frozen=True)
class _SettlementBuffers:
    fills: list[Fill]

# GOOD: honestly mutable builder
@dataclass
class _SettlementBuffers:
    fills: list[Fill]
```

### Rule 7: The output at the boundary is immutable

```python
# BAD: returns mutable lists
def compute_settlement(...) -> Settlement:
    ...
    return Settlement(fills=buffers.fills, ...)  # mutable list escapes

# GOOD: returns immutable tuples
def compute_settlement(...) -> Settlement:
    ...
    return Settlement(fills=tuple(buffers.fills), ...)  # frozen at boundary
```

---

## Quick reference for agents

When generating code, ask yourself:

1. **Am I moving value or carrying committed state?** → Pattern A. Frozen
   dataclass, immutable fields, pure function, `replace()` transitions.
2. **Am I accumulating intermediate results?** → Pattern B. Honestly mutable
   builder, freshly constructed, discarded after use, immutable output at
   boundary.
3. **Can this step reject with a typed reason?** → Pattern C. Typed Result,
   stable rejection codes, negative tests assert the code.
4. **Am I doing IO, parsing, or shell work?** → Pattern D. Imperative shell,
   parse-don't-validate, never decides settlement semantics.
5. **Am I using `Dict` or `List` inside a `@dataclass(frozen=True)`?** → Stop.
   This is the frozen lie. Use `tuple` or make the builder honestly mutable.
6. **Am I using `Dict[str, Any]` as a state type?** → Stop. This is a
   stringly-typed bag. Use a frozen dataclass with named fields.
7. **Am I mutating a state object in place?** → Stop. Use `replace()` to
   return a new state. The only exception is a local builder (Pattern B) that
   is discarded after use.
8. **Am I using `assert` for runtime validation?** → Stop. Use explicit guards
   that return typed rejections or raise `ValueError`/`TypeError`.
9. **Am I using floats in value-moving math?** → Stop. Use integer base units
   with explicit scale, rounding, and dust policy.
10. **Am I adding a pattern because it is familiar?** → Stop. Use the smallest
    pattern that makes the boundary clearer. Pattern cargo-culting makes code
    harder to audit.
