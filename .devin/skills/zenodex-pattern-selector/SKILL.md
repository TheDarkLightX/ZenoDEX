---
name: zenodex-pattern-selector
description: >-
  Agent-facing guide for ZenoDEX code generation. Teaches specification-first
  functional core / imperative shell (FCIS): a specification refined into an
  abstract state machine, implemented as a deterministic Python reference
  transition, connected to a Rust implementation by differential vectors and
  proof obligations, committed atomically with replayable evidence. FCIS and
  immutability are architectural patterns that serve the specification
  discipline — they are not the assurance itself. Use BEFORE writing or
  editing any value-moving, state-carrying, or transition code in any
  language in the repo. Reference files provide before/after examples and
  the full refactoring preflight checklist.
---

# ZenoDEX Pattern Selector

## The assurance pipeline

The goal is not "functional programming" or "frozen dataclasses." The goal is:

```text
economic/protocol specification
        ↓ refinement
abstract state machine
        ↓ executable correspondence
Python reference transition
        ↓ differential vectors / proof obligations
Rust implementation
        ↓ atomic commit and replay
production execution
```

A perfectly pure liquidation function can still implement the wrong
liquidation semantics. FCIS is a strong architectural heuristic — simple
values at boundaries, deterministic computation inside, effects outside —
but it is not a correctness proof. The assurance comes from the specification,
the refinement steps, and the replayable evidence connecting them.

This pattern is used in seL4 (proofs connect functional specifications to
progressively more concrete implementations reaching C) and in Dexter2
(formalizing DEX contracts as state-transition functions in Coq, proving
individual and interacting-contract properties before extracting executable
code — the work reports discovering mismatches between the informal
specification and the implementation).

## FCIS foundation

FCIS separates pure, testable business logic (the core) from side effects
like database calls and network requests (the shell). The core operates only
on the data it is given; the shell acquires external input and executes
effects. This makes the core testable in isolation and the shell swappable.
See Gary Bernhardt's [Boundaries](https://www.destroyallsoftware.com/talks/boundaries),
[Google Testing Blog — Simplify Your Code: Functional Core](https://testing.googleblog.com/2025/10/simplify-your-code-functional-core.html),
and [Functional Core, Imperative Shell — Shortcomings](https://functional-architecture.org/functional_core_imperative_shell/).

The system is many small core/shell pairs, not one enormous core and shell.

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
  check postconditions, atomically commit state + effects + nonce + receipt
  using compare-and-swap on the pre-root, idempotently deliver effects
```

Dependencies point inward. A shell function may call pure core functions.
A pure core function never calls shell or I/O. If one function contains both,
extract the deterministic decision into a separate pure function.

Keep decisions in the core, represent required effects as values, and
restrict the shell to evidence acquisition, atomic commit, and external
execution.

## Decision rule: concern → location

| Concern | Location |
|---|---|
| Decode framing, impose resource limits | Shell/boundary |
| Acquire clock, oracle, signatures, state snapshot | Shell |
| Validate canonical syntax and construct domain values | Pure boundary parser (core) |
| Authorization, nonce, phase, and economic eligibility | Core |
| Rounding, fees, liquidation, and conservation semantics | Core |
| Describe transfers, postings, receipts, and notifications | Core as effect values |
| CAS/transaction, storage, network, and effect execution | Shell |
| Infrastructure retry and transport failure | Shell |
| Domain rejection and committed-failure semantics | Core |

Two dependency violations the skill prohibits explicitly:

```text
PROHIBITED: core → repository/oracle/clock/network
```
This reverses the dependency direction. The core never acquires external
input or executes external effects.

```text
PROHIBITED: shell decides liquidation eligibility, rounding, or compensation
```
This leaves authoritative domain logic in the imperative layer. The shell
acquires input and commits effects; it never decides settlement semantics.

The rule: `src/core/**` must not import from `src/integration/**`.

## The transition interface

```python
# Functional core
def transition(
    state: State,
    command: Command,
    evidence: Evidence,
) -> Decision:
    # authorization, economic admission, rounding,
    # conservation and state-transition semantics
    return Decision(post_state, effects, receipt)


# Imperative shell
def handle(raw_request: bytes) -> Response:
    command = decode_and_resource_bound(raw_request)
    evidence = acquire_clock_oracle_and_auth_evidence()
    pre_state, expected_root = repository.read()

    decision = transition(pre_state, command, evidence)

    repository.atomic_commit(
        expected_root=expected_root,
        decision=decision,
    )
    outbox.dispatch_idempotently()
    return encode_response(decision)
```

`Evidence` carries time, oracle observations, signatures, block information,
governance state, and randomness as explicit inputs. They are not ambient
reads. The core never reads the clock or environment.

`Decision` has explicit commit semantics:

```python
Decision = RejectNoCommit | CommitSuccess | CommitProtocolFailure
```

- **RejectNoCommit:** pre-state and effects remain untouched. The caller
  discards the result and retries from the same pre-state.
- **CommitSuccess:** the transition produced a new state and effect plan
  that must be committed atomically.
- **CommitProtocolFailure:** the protocol consumes a nonce, charges a fee,
  records an attempted operation, or advances trusted intermediate state
  even though the operation did not succeed economically. The result type
  must indicate that state was committed.

Every operation must specify its commit semantics. "Failure" does not
universally mean "nothing changed." If the skill's shell template assumes
no-commit rejection, that must be established as a ZenoDEX invariant and
tested, or the result type must distinguish committed failure explicitly.

## Classification: six questions

Classify by authority and ownership, not by syntax ("dataclass versus class"
or "frozen versus mutable"). Ask:

1. **Is this value authoritative, persisted, hashed, signed, or replayed?**
   If yes, it must be transitively immutable or exclusively owned, with
   canonical encoding.
2. **Can a mutable alias escape?** If yes, the value is not safe regardless
   of `frozen=True`. `frozen=True` only prevents field reassignment; nested
   dicts, lists, and mutable leaves remain mutable (Python documentation
   explicitly says it "emulates" immutability).
3. **Is mutation fresh, exclusively owned, and discarded on rejection?**
   If yes, a mutable local builder inside a pure transition is acceptable
   and often preferable to mechanically replacing every dict update with
   layers of tuples and `replace()`.
4. **Is this canonical protocol state or an operational representation?**
   Operational representations (database sessions, locks, clients, caches)
   should normally be imperative. Canonical protocol state (commands,
   receipts, certificates, effect plans) should be immutable and
   canonically encoded. These are separate concepts.
5. **Can failure commit anything?** If yes, the result type must say so
   explicitly. The shell must handle committed-failure differently from
   no-commit rejection.
6. **What exact invariant or proof obligation applies?** Conservation
   (`sum(post) == sum(pre) + sum(external_in) - sum(external_out)`),
   monotonicity, freshness, replay-protection, authorization, or a
   specification-level property. The invariant determines the required
   evidence (tests, property tests, differential vectors, proofs).

This decision procedure produces better refactors than blanket rules such
as "all state classes must be frozen" or "all validation belongs in the
shell."

## Immutability: the nuanced rule

The literature does not say "make every class frozen." Verified systems
(seL4, Coq DEX formalizations) contain mutation. What matters is whether
mutation is modeled, owned, bounded, and prevented from creating
unauthorized observable behavior.

A pure function may internally use a mutable builder while remaining
observationally pure if:

- The builder is newly allocated or completely detached.
- No mutable alias to authoritative pre-state exists.
- The builder never escapes before sealing.
- Rejection discards it completely.
- Sealing validates every invariant.
- The returned state/effects are immutable domain values.

Conversely, `@dataclass(frozen=True)` is not a deep-immutability guarantee.
Python's documentation says it only emulates immutability; nested
dictionaries, lists, and mutable leaves remain mutable.

Therefore:

- Persisted, hash-bound, or replay-bound state should be transitively
  immutable or exclusively owned.
- Commands, receipts, certificates, and effect plans should be immutable
  and canonically encoded.
- A fresh local builder inside a pure transition may be mutable.
- Shell objects (database sessions, locks, clients, caches) should normally
  be imperative — not awkwardly "frozen."
- Operational representations and canonical protocol representations should
  be separate concepts.

Surface immutability is a representation property, not an assurance result.
The assurance comes from the specification, the invariant checks, and the
replayable evidence.

## Mandatory invariants for authoritative state

1. **Transitive immutability for escaped state.** No retained mutable
   aliases, no mutable contents, no mutation after construction — for
   values that escape, persist, hash, sign, or enter a receipt.
2. **No stringly-typed state bags.** Every field is a named, typed field on
   a frozen dataclass. No `Dict[str, Any]` as a state representation.
3. **Transitions return a new state.** Use `replace()`. When refactoring a
   mutable API (e.g., `add() -> None`) to immutable, use a deliberately
   different method name (e.g., `with_delta()`) to prevent silent
   value-loss at call sites that ignore the return value.
4. **Integer-only arithmetic.** No floats in consensus, accounting,
   settlement, core state, proof, or verifier paths. Use integer base units
   with explicit scale, named rounding operations (not anonymous `//`),
   and dust policy.
5. **No assert for runtime validation.** Use explicit guards that return
   typed rejections or raise `ValueError`/`TypeError`.
6. **Canonical encoding independently of in-memory representation.** If data
   is hashed or signed, require a single canonical encoding per semantic
   value via a versioned protocol encoder. The canonical encoding is an ABI.
7. **Effects are values, decided by the core, executed by the shell.** The
   core decides that a transfer, posting, receipt, or notification is
   required and returns it as a transitively immutable, canonical,
   asset-qualified effect value. The shell possesses the authority to
   execute it but does not recalculate the amount or decide whether it
   should occur. Deltas are aggregated by `(principal, asset,
   custody-domain)` before commitment. Conservation is checked across the
   complete plan. The transition binds pre-root, command, post-root,
   effect-plan hash, and replay identity. External effects require a
   transactional outbox plus idempotent delivery.

   ```python
   @dataclass(frozen=True)
   class TransferEffect:
       asset: AssetId
       source: AccountId
       destination: AccountId
       amount: Amount
   ```

   The core returns this as data. The shell executes it. The shell must not
   reconstruct economic amounts from the effect plan.

## Representation rules

"Use sorted tuples instead of dicts" is too mechanical. Choose by semantics:

| Semantic type | Representation rule |
|---|---|
| Ordered sequence | Immutable tuple in protocol-defined order. Never sort automatically. |
| Set (no duplicates) | Define duplicate policy and canonical total order. `frozenset` is immutable but not canonically ordered across languages. |
| Dynamic map | Persistent/immutable map, canonical tuple, or privately owned map behind an immutable API. For large hot state, preserve complexity. |
| Hash/signature encoding | Canonicalize by specified bytes via a versioned protocol encoder. Do not rely on in-memory iteration order. |
| Large hot state | Preserve O(1) lookup. A tuple turns balance lookups into O(n); repeated updates become O(n²). Benchmark before replacing maps with tuples. |

A privately owned map with canonical serialization may be safer and faster
than an immutable tuple with linear updates. Using a dictionary should
trigger classification and verification, not an automatic tuple rewrite.

## Typed rejections and commit semantics

For new authoritative code, use a discriminated `Decision` with a `RejectCode`
enum and immutable structured details:

```python
class RejectCode(Enum):
    NEGATIVE_AMOUNT = "negative_amount"
    INSUFFICIENT_BALANCE = "insufficient_balance"
    STALE_ORACLE = "stale_oracle"
    # ...

@dataclass(frozen=True)
class CommitSuccess:
    state: MyState
    effect_plan: MyEffectPlan

@dataclass(frozen=True)
class RejectNoCommit:
    code: RejectCode
    details: RejectDetails  # frozen dataclass, not str

@dataclass(frozen=True)
class CommitProtocolFailure:
    state: MyState  # state was committed (nonce consumed, fee charged)
    code: RejectCode
    details: RejectDetails

def step(state: MyState, command: MyCommand, evidence: Evidence
         ) -> CommitSuccess | RejectNoCommit | CommitProtocolFailure:
    ...
```

Legacy boolean/string results (e.g., `ok: bool`, `error: str | None`) are
migration targets, not exemplars. Do not cite them as typed-rejection
patterns. Do not mix Result APIs in the same function.

Negative tests assert the rejection enum and the commit semantics, not the
error message string.

## Mutable builder rules

A mutable builder is acceptable when:

1. Honestly mutable (`@dataclass` without `frozen=True`).
2. Freshly constructed per computation.
3. Never aliased with committed state. Copying the outer container is not
   enough — nested mutable values must also be copied.
4. Discarded on rejection.
5. Sealing validates every invariant.
6. Output at the boundary is transitively immutable.

### Repository status (do not copy as templates)

The following types are **unsafe migration targets** at the current commit.
Do not present them as correct exemplars:

- `src/core/settlement.py` — `Fill`, `BalanceDelta`, `ReserveDelta`,
  `LPDelta`, `Settlement` are `@dataclass` (NOT frozen) with `List` fields
  and `Optional[List[Dict[str, Any]]]` events.
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

## Imperative shell rules

```text
decode/resource-bound input
→ capture authenticated evidence once
→ read state + expected version/root
→ run pure transition
→ check postconditions
→ atomically CAS:
    post-state/root/version
    nonce/replay record
    receipt
    effect plan/outbox
→ idempotently deliver effects
```

A nominally thin shell can accumulate substantial domain logic over time
([Functional Core, Imperative Shell — Shortcomings](https://functional-architecture.org/functional_core_imperative_shell/)).
Watch for this drift. Represent effectful interactions as pure values and
separate their description (core) from their execution (shell).

1. **Parse-don't-validate at the boundary.** Convert raw input into typed
   domain objects once, then pass typed objects to the core.
2. **The shell never decides settlement semantics.** Authorization,
   admission, economics, freshness, and replay are core responsibilities.
3. **Capture external time, randomness, and IO once as `Evidence`.** Pass
   explicitly inward. The core never reads the clock or environment.
4. **Exhaustive result handling.** Handle `CommitSuccess`,
   `RejectNoCommit`, and `CommitProtocolFailure` explicitly. Do not assume
   every non-reject is success.
5. **Check postconditions before commit.** Verify conservation
   (`sum(post) == sum(pre) + sum(external_in) - sum(external_out)`) and
   any transition-specific invariants.
6. **Atomic commit with compare-and-swap.** Call an explicit commit
   operation that takes the expected pre-root and version, the post-state,
   the effect plan, and the replay record. The commit returns `CommitOk`
   (with receipt) or `CommitConflict`.
7. **External effects require a transactional outbox** plus idempotent
   delivery. Persisting the effect plan is not the same as executing it.
8. **Retries must be idempotent** or explicitly non-idempotent with a safe
   replay rule.
9. **Demo paths must never become authority.**

Without compare-and-swap and the transactional outbox, a pure core can still
be deployed incorrectly.

## Python recommendations

- Transitively immutable escaped state; mutable local builders allowed under
  exclusive ownership.
- Runtime smart constructors for authoritative values. Type annotations
  alone do not enforce invariants.
- Reject `bool` where an amount expects an `int` (`isinstance(x, bool)`).
- No floats, ambient time, randomness, locale, unordered iteration, or
  process-global mutable state in the core.
- Explicit protocol bounds matching Rust, even though Python integers do
  not overflow.
- Named rounding operations rather than anonymous `//`.
- No `assert` for reachable validation (optimized Python can remove
  assertions).
- Strict typing plus custom architectural lints (e.g., AST checks for
  ignored `with_delta`/`with_balance` return values; mypy cannot enforce
  this).
- Hypothesis rule-based state-machine testing, not only one-operation
  properties. QuickCheck's foundational result is that properties and
  generated inputs are especially effective for functional components.

## Rust recommendations

- `#![forbid(unsafe_code)]` in value-authority and arithmetic crates, or a
  tiny separately audited unsafe boundary.
- Private newtypes for assets, amounts, collateral, debt, price, ratio,
  nonce, version, and state root. Dimensional typing prevents unit
  confusion (Phoenix), but not overflow or incorrect economic formulas.
- Closed command/outcome enums and exhaustive matching.
- Total `Result` APIs; no reachable panic, indexing panic, `unwrap`, or
  `expect` for adversarial input.
- Checked or widened arithmetic. Wrapping and saturation only through
  explicitly named protocol operations.
- Canonical protocol encoding separate from incidental Serde representation.
  `BTreeMap` supplies deterministic key iteration order, not canonical
  bytes. Serde derives and `rename_all` do not establish a canonical wire
  encoding. Require a versioned protocol encoder with explicit widths,
  normalization, and field/tag encoding. Python/Rust golden vectors
  required.
- `#[must_use]` on returned transitions and effect plans.
- Ownership moves preserve replayable pre-state. Take `&State`, return
  owned `State`.
- Proptest, stateful fuzzing, and differential replay against Python
  (OpenBook uses fuzz invariants for end-to-end token and volume
  identities).
- Kani proof harnesses for bounded arithmetic and transition kernels;
  Verus for selected high-value functional claims.

## Lessons from comparable codebases

These are patterns worth learning from, not claims that the projects are
bug-free. Audits are evidence, not proof — Orca's pinned revision fixed an
overflow-related panic despite previous audits.

| Codebase | Pattern | Limitation |
|---|---|---|
| Raiden (Python) | Deterministic `state_transition(state, state_change)`, separates state changes from emitted events, restores through snapshots + WAL replay | State is mutable by convention, protected with deep copies. ZenoDEX can enforce this boundary more strongly. |
| Python TUF | Network/filesystem I/O outside trusted update state machine, strict root→timestamp→snapshot→targets sequencing, rollback protection, expiry, authority | Some rejected updates intentionally retain trusted intermediate state. Failure/commit semantics must be explicit. |
| Chia (Python/Rust) | Mechanically restricts protocol objects, derives deterministic codecs, fixed-width integer/byte types, hashes serialized forms | Frozen schemas may still contain mutable collections. Canonical encoding and immutability remain separate obligations. |
| Orca Whirlpools (Rust) | Deterministic integer swap computation returning typed result, explicit rounding helpers, Proptest properties | Full transition mutates state and depends on Solana's transaction rollback. An off-chain engine cannot assume that runtime guarantee. |
| Penumbra (Rust) | Distinguishes stateless checks, historical-state checks, and checks adjacent to execution; documents TOCTOU risk | Not completely FCIS. Safety argument includes its transactional storage substrate. |
| Phoenix (Rust) | Private dimensional newtypes for base lots, quote lots, atoms, ticks | Dimensional typing prevents unit confusion, not overflow or incorrect formulas. |
| OpenBook (Rust) | Stateful fuzz harness exercising command sequences, checks end-to-end token and volume identities | Mutation followed by rejection is safe only because the platform rolls back the transaction. |

A key lesson: platforms with transactional rollback (Solana, Penumbra's
storage) can safely mutate-then-reject. An off-chain engine like ZenoDEX
cannot assume that guarantee — it must enforce no-commit rejection or
committed-failure semantics explicitly in the result type.

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
11. CAS/concurrency: compare-and-swap on expected pre-root/version?
12. Crash points: what happens between persisting state and delivering effects?
13. Outbox/idempotence: are external effects delivered exactly-once?
14. Conservation postconditions: does the transition verify conservation?
15. Retained-alias tests: no mutable alias from pre-state survives into post?
16. Deterministic activation/versioning: commit records exact code version?
17. Forward recovery: rollback is unsafe once new consensus state is committed.

See `reference/refactoring-preflight.md` for the full checklist.

## Quick reference for agents

When generating code, ask yourself:

1. **Is this value authoritative, persisted, hashed, signed, or replayed?**
   → Transitively immutable or exclusively owned, with canonical encoding.
2. **Can a mutable alias escape?** → Do not commit this form. Either make
   the fields immutable or make the builder honestly mutable and seal
   before escape. Continue after the invariants pass.
3. **Is mutation fresh, exclusively owned, and discarded on rejection?**
   → Mutable builder is acceptable inside a pure transition.
4. **Is this canonical protocol state or an operational representation?**
   → Protocol state: immutable and canonically encoded. Operational:
   imperative is fine.
5. **Can failure commit anything?** → The result type must distinguish
   `RejectNoCommit` from `CommitProtocolFailure`.
6. **What invariant or proof obligation applies?** → Conservation,
   monotonicity, freshness, replay-protection, authorization, or a
   specification-level property. The invariant determines the required
   evidence.
7. **Does this code decide or bind value?** → Pure deterministic core. No
   IO, no floats, no hidden state. If the function does IO, it is shell.
   Extract the pure decision into a separate function.
8. **Am I using `Dict[str, Any]` as a state type?** → Do not commit this
   form. Replace with a frozen dataclass with named fields.
9. **Am I mutating a state object in place?** → Do not commit this form.
   Use `replace()` to return a new state. The only exception is a local
   builder that is discarded after use.
10. **Am I using `assert` for runtime validation?** → Do not commit this
    form. Use explicit guards that return typed rejections or raise
    `ValueError`/`TypeError`.
11. **Am I using floats in value-moving math?** → Do not commit this form.
    Use integer base units with named rounding operations and dust policy.
12. **Am I refactoring an existing mutable API to immutable?** → Use a
    deliberately different method name. Run the refactoring preflight.
13. **Am I persisting only state and dropping the effect plan?** → Do not
    commit this form. The shell must atomically commit state + effect plan
    + nonce + receipt via compare-and-swap, with a transactional outbox
    for external effects.
14. **Am I moving an authoritative semantic check into the shell?** → Do
    not commit this form. Authorization, admission, economics, freshness,
    and replay are core responsibilities. The shell acquires input and
    commits effects; it never decides settlement semantics.
15. **Am I treating `frozen=True` as a correctness proof?** → It is not.
    Surface immutability is a representation property. The assurance
    comes from the specification, invariant checks, and replayable
    evidence.
16. **Is the core calling the repository, oracle, clock, or network?** → Do
    not commit this form. This reverses the dependency direction. Extract
    the external acquisition into the shell and pass it as `Evidence`.
17. **Is the shell recalculating amounts or deciding whether an effect
    occurs?** → Do not commit this form. The core decides and returns
    effects as values. The shell executes them without reconstruction.

## Reference files

- `reference/before-after-examples.md` — concrete before/after code,
  including the correct shell template with compare-and-swap commit,
  postcondition checks, and the BalanceTable migration with `with_delta()`.
- `reference/refactoring-preflight.md` — full preflight checklist.
