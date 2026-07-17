# Pattern Selector — Before/After Examples

Concrete before/after examples for agents generating code.

## Pattern: Authoritative core + typed rejection

### Example 1: A value-moving transition that can reject

```python
class RejectCode(Enum):
    NEGATIVE_AMOUNT = "negative_amount"
    INSUFFICIENT_BALANCE = "insufficient_balance"

@dataclass(frozen=True)
class StepOk:
    state: MyState
    effect_plan: MyEffectPlan

@dataclass(frozen=True)
class StepReject:
    code: RejectCode
    details: RejectDetails  # frozen dataclass, not str

def step(state: MyState, command: MyCommand) -> StepOk | StepReject:
    if command.amount < 0:
        return StepReject(
            code=RejectCode.NEGATIVE_AMOUNT,
            details=RejectDetails(field="amount", value=command.amount),
        )
    new_balance = state.balance + command.amount
    new_state = replace(state, balance=new_balance)
    return StepOk(state=new_state, effect_plan=MyEffectPlan(delta=command.amount))
```

Negative tests assert the rejection enum:

```python
def test_negative_amount_rejected():
    result = step(state, MyCommand(amount=-1))
    assert isinstance(result, StepReject)
    assert result.code == RejectCode.NEGATIVE_AMOUNT
```

### When to use exceptions instead

```python
# Contract violation after trusted construction — programmer error, not protocol.
def require_int_range(value: object, name: str, lo: int, hi: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < lo or value > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}]")
    return value
```

---

## Pattern: Authoritative core with internal mutable builder

### Example 2: Honest mutable builder with immutable output

```python
@dataclass  # honestly mutable — no frozen=True
class _SettlementBuffers:
    fills: list[Fill]
    balance_deltas: list[BalanceDelta]

def compute_settlement(...) -> Settlement:
    buffers = _SettlementBuffers(fills=[], balance_deltas=[])
    # ... accumulate into buffers ...
    # Boundary: convert to immutable tuples
    return Settlement(
        fills=tuple(buffers.fills),
        balance_deltas=tuple(buffers.balance_deltas),
    )
```

The builder is honestly mutable, freshly constructed, discarded after use,
and produces a transitively immutable `Settlement` at the boundary. For this
to be safe, `Fill`, `BalanceDelta`, and `Settlement` must all be
`@dataclass(frozen=True)` with immutable field types. At the current commit
they are NOT — see the "Repository status" section in SKILL.md.

---

## Pattern: Refactoring a mutable table to immutable

### Example 3: BalanceTable migration with safe API naming

The current `BalanceTable.add()` returns `None` (mutates in place). Keeping
the same name but changing semantics causes silent value-loss at call sites
that ignore the return value.

**Before** (current mutable API):

```python
class BalanceTable:
    def add(self, pubkey: str, asset: str, delta: int) -> None:
        current = self.get(pubkey, asset)
        self.set(pubkey, asset, current + delta)

# Call site (ignores return — correct today because add() returns None):
balances.add(pubkey, asset, delta)
```

**After** (immutable API with deliberately different name):

```python
@dataclass(frozen=True)
class BalanceTable:
    _entries: tuple[tuple[tuple[str, str], int], ...] = ()

    @classmethod
    def from_entries(
        cls, entries: Iterable[tuple[tuple[str, str], int]]
    ) -> "BalanceTable":
        """Smart constructor. Rejects duplicates, unsorted input, invalid amounts."""
        seen: dict[tuple[str, str], int] = {}
        for key, amount in entries:
            if not isinstance(key, tuple) or len(key) != 2:
                raise TypeError("each key must be a (pubkey, asset) tuple")
            if not isinstance(amount, int) or isinstance(amount, bool):
                raise TypeError("amount must be int")
            if amount < 0:
                raise ValueError(f"amount must be non-negative: {amount}")
            if key in seen:
                raise ValueError(f"duplicate key: {key}")
            seen[key] = amount
        return cls(_entries=tuple(sorted(seen.items())))

    def get(self, pubkey: str, asset: str) -> int:
        key = (pubkey, asset)
        for k, v in self._entries:
            if k == key:
                return v
        return 0

    def with_delta(self, pubkey: str, asset: str, delta: int) -> "BalanceTable":
        """Return a new BalanceTable with delta applied. Does NOT mutate self."""
        if not isinstance(delta, int) or isinstance(delta, bool):
            raise TypeError("delta must be int")
        current = self.get(pubkey, asset)
        new_balance = current + delta
        if new_balance < 0:
            raise ValueError(f"Insufficient balance: {current} + {delta}")
        return self.with_balance(pubkey, asset, new_balance)

    def with_balance(self, pubkey: str, asset: str, amount: int) -> "BalanceTable":
        """Return a new BalanceTable with the balance set. Does NOT mutate self."""
        if not isinstance(amount, int) or isinstance(amount, bool):
            raise TypeError("amount must be int")
        if amount < 0:
            raise ValueError("amount must be non-negative")
        key = (pubkey, asset)
        if amount == 0:
            new_entries = tuple((k, v) for k, v in self._entries if k != key)
        else:
            existing = dict(self._entries)
            existing[key] = amount
            new_entries = tuple(sorted(existing.items()))
        return BalanceTable(_entries=new_entries)

# Call site (must use the return value — different name prevents silent breakage):
new_balances = balances.with_delta(pubkey, asset, delta)
```

**Why `with_delta()` not `add()`:** The different name forces every call site
to be updated. A call site that writes `balances.add(pubkey, asset, delta)`
will get an `AttributeError`, making the migration visible.

**Migration checklist:**
1. Search for all call sites of `add()`, `subtract()`, `set()`.
2. Replace each with `with_delta()`, `with_balance()`.
3. Ensure every call site uses the return value.
4. Add a custom AST lint check that rejects ignored `with_delta`/`with_balance`
   return values. mypy `# type: ignore` audits cannot enforce this.
5. Run the full test suite — any test that was silently passing with broken
   balances will now fail.

**Performance note:** The `with_delta` example above is O(n) per update
because it scans the tuple. For a hot balance table with 100k+ entries, use a
privately owned map behind an immutable API, or a persistent/immutable map
data structure. Benchmark before choosing the representation.

---

## Pattern: Imperative shell with atomic commit

### Example 4: Correct shell template

The shell must use compare-and-swap on the expected pre-root, handle both
success and rejection exhaustively, and return a receipt from the successful
commit.

```python
@dataclass(frozen=True)
class CommitOk:
    receipt: Receipt  # pre-root, post-root, effect-plan hash, version

@dataclass(frozen=True)
class CommitConflict:
    expected_pre_root: bytes
    actual_pre_root: bytes

def handle_request(
    raw_input: dict[str, Any],
    snapshot: Snapshot,  # loaded by outer shell, contains root + version
) -> tuple[int, dict[str, Any]]:
    # 1. Parse and validate at the boundary (typed rejection)
    command = parse_command(raw_input)
    if isinstance(command, ParseReject):
        return 400, {"error": {"code": command.code.value, "details": ...}}

    # 2. Call functional core (pure — returns typed result)
    result = step(snapshot.state, command.value)

    # 3. Exhaustive result handling — do not assume non-reject is success
    if isinstance(result, StepReject):
        # No-commit rejection: do NOT persist. Pre-state is untouched.
        return 422, {"error": {"code": result.code.value, "details": ...}}

    # result is StepOk — proceed to commit

    # 4. Atomic commit with compare-and-swap
    #    External effects go through a transactional outbox for idempotent delivery.
    commit_result = commit_transition(
        expected_pre_root=snapshot.root,
        expected_version=snapshot.version,
        post_state=result.state,
        effect_plan=result.effect_plan,
        replay_record=ReplayRecord(
            pre_root=snapshot.root,
            post_root=result.state.root,
            command_hash=hash_command(command.value),
            effect_plan_hash=hash_effect_plan(result.effect_plan),
        ),
    )

    if isinstance(commit_result, CommitConflict):
        # Concurrent commit — caller must reload and retry
        return 409, {"error": {
            "code": "commit_conflict",
            "expected_pre_root": commit_result.expected_pre_root.hex(),
            "actual_pre_root": commit_result.actual_pre_root.hex(),
        }}

    # 5. Return response with receipt from the successful commit
    return 200, {
        "state": serialize(result.state),
        "effect_plan": serialize(result.effect_plan),
        "receipt": {
            "pre_root": commit_result.receipt.pre_root.hex(),
            "post_root": commit_result.receipt.post_root.hex(),
            "effect_plan_hash": commit_result.receipt.effect_plan_hash.hex(),
            "version": commit_result.receipt.version,
        },
    }
```

**What the previous broken example did wrong:**
- `expected_version` was unused.
- `save_state()` received neither expected pre-root nor version.
- No compare-and-swap conflict result.
- Receipt was constructed optimistically instead of returned by the commit.
- Persisting the effect plan was conflated with executing it (external effects
  need a transactional outbox).
- "Exhaustive" handling assumed every non-`StepReject` was `StepOk`.
- Every protocol rejection became HTTP 402 (should be 422 for semantic
  rejection, 409 for conflict).

---

## Anti-examples — what NOT to generate

### Anti-example 1: The frozen lie

```python
# DO NOT GENERATE THIS
@dataclass(frozen=True)
class MyState:
    data: dict[str, Any]  # frozen lie — dict is mutable
```

**Fix:** Use `tuple` for collections, or make the builder honestly
`@dataclass` (not frozen).

### Anti-example 2: Stringly-typed state bag

```python
# DO NOT GENERATE THIS
@dataclass(frozen=True)
class MyState:
    config: dict[str, Any]  # stringly-typed bag
```

**Fix:** Replace with a frozen dataclass that has a named field for every key.

### Anti-example 3: In-place mutation of committed state

```python
# DO NOT GENERATE THIS
def step(state: MyState, amount: int) -> None:
    state.balance += amount  # mutates committed state in place
```

**Fix:** Return a new state via `replace(state, balance=state.balance + amount)`.

### Anti-example 4: assert for runtime validation

```python
# DO NOT GENERATE THIS
def step(state: MyState, amount: int) -> MyState:
    assert amount >= 0  # vanishes under python -O
```

**Fix:** Use `if amount < 0: raise ValueError(...)` or return a typed
`StepReject`.

### Anti-example 5: Float in value-moving math

```python
# DO NOT GENERATE THIS
def compute_output_amount(r_in: float, r_out: float, a_in: float) -> float:
    return a_in * r_out / (r_in + a_in)
```

**Fix:** Use integer base units with explicit scale, rounding, and dust policy.

### Anti-example 6: Silent value-loss on immutable refactor

```python
# DO NOT GENERATE THIS
# Before: add() returns None (mutates in place)
# After: add() returns new BalanceTable (but call sites ignore return value)
balances.add(pubkey, asset, delta)  # silently does nothing now!
```

**Fix:** Use a deliberately different method name (`with_delta()`).

### Anti-example 7: Shell that drops the effect plan

```python
# DO NOT GENERATE THIS
def handle_request(raw_input):
    result = step(state, command)
    if result.ok:
        save_state(result.state)  # drops effect plan, nonce, receipt
    return 200, {"state": serialize(result.state)}  # always 200
```

**Fix:** See Example 4 above — compare-and-swap commit with effect plan,
nonce, receipt, and outbox for external effects.

### Anti-example 8: Pattern cargo-culting

```python
# DO NOT GENERATE THIS
class BalanceStrategy(ABC):
    @abstractmethod
    def add(self, ...) -> "BalanceStrategy": ...

class SimpleBalanceStrategy(BalanceStrategy):
    def add(self, ...) -> "BalanceStrategy":
        pass

class BalanceStrategyFactory:
    def create(self, t: str) -> BalanceStrategy: ...
```

**Fix:** Use a frozen dataclass with a pure `with_delta` method. Add the
strategy pattern only when there are multiple interchangeable implementations
behind the same typed contract.

### Anti-example 9: Shallow copy that aliases nested mutable state

```python
# DO NOT GENERATE THIS
def build_ctx(state: DexState) -> Ctx:
    markets = dict(state.perps.markets)  # copies outer dict only
    # PerpMarketState values are still aliased. global_state Dict inside
    # them is mutable and shared.
    return Ctx(markets=markets)
```

**Fix:** Deep-copy nested mutable values, or make `PerpMarketState`
transitively immutable so aliasing is safe.
