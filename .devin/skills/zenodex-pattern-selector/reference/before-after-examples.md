# Pattern Selector — Before/After Examples

Concrete before/after examples for each pattern in the ZenoDEX codebase.
These are the examples agents should follow when generating code.

## Pattern: Authoritative core + typed rejection

### Example 1: A value-moving transition that can reject

```python
class RejectCode(Enum):
    NEGATIVE_AMOUNT = "negative_amount"
    INSUFFICIENT_BALANCE = "insufficient_balance"
    EXPIRED_INTENT = "expired_intent"

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
        return StepReject(
            code=RejectCode.NEGATIVE_AMOUNT,
            details=RejectDetails(field="amount", value=command.amount),
        )
    new_balance = state.balance + command.amount
    new_state = replace(state, balance=new_balance)
    return StepOk(state=new_state, effect=MyEffect(delta=command.amount))
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
# This is a contract violation (programmer error), not a protocol outcome.
# The input crossed a trust boundary and was already validated.
# Use an exception, not a Result.
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
    # Boundary: convert to immutable tuples when constructing Settlement
    return Settlement(
        fills=tuple(buffers.fills),
        balance_deltas=tuple(buffers.balance_deltas),
    )
```

The builder is honestly mutable, freshly constructed, discarded after use,
and produces a transitively immutable `Settlement` at the boundary.

### Example 3: Copy-then-mutate-then-return (transitional pattern)

The existing `apply_settlement_pure` copies state before mutating. This is
correct in spirit but returns mutable types. Use as a transitional pattern
only — the return types should eventually be made transitively immutable.

```python
def apply_settlement_pure(settlement, balances, pools):
    # Fresh copies — original state is untouched
    balances_copy = copy_balance_table(balances)
    pools_copy = {pid: replace(p) for pid, p in pools.items()}
    # Mutate copies (current API mutates in place)
    for delta in settlement.balance_deltas:
        balances_copy.add(delta.pubkey, delta.asset, delta.net_delta())
    return balances_copy, pools_copy
```

**Migration warning:** When refactoring `BalanceTable.add()` from `-> None`
(mutating) to an immutable API, see Example 4 below.

---

## Pattern: Refactoring a mutable table to immutable

### Example 4: BalanceTable migration with safe API naming

The current `BalanceTable.add()` returns `None` (mutates in place). If we
change `add()` to return a new `BalanceTable` but keep the same name, existing
call sites that ignore the return value will silently stop moving balances.

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
    entries: tuple[tuple[tuple[str, str], int], ...] = ()

    def get(self, pubkey: str, asset: str) -> int:
        key = (pubkey, asset)
        for k, v in self.entries:
            if k == key:
                return v
        return 0

    def with_delta(self, pubkey: str, asset: str, delta: int) -> "BalanceTable":
        """Return a new BalanceTable with delta applied. Does NOT mutate self."""
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
            new_entries = tuple((k, v) for k, v in self.entries if k != key)
        else:
            existing = {k: v for k, v in self.entries}
            existing[key] = amount
            new_entries = tuple(sorted(existing.items()))
        return BalanceTable(entries=new_entries)

# Call site (must use the return value — different name prevents silent breakage):
new_balances = balances.with_delta(pubkey, asset, delta)
```

**Why `with_delta()` not `add()`:** The different name forces every call site
to be updated. A call site that writes `balances.add(pubkey, asset, delta)`
will get an `AttributeError` on the new immutable type, making the migration
visible. If we kept the name `add()`, the call would silently do nothing
(return value ignored, self not mutated).

**Migration checklist:**
1. Search for all call sites of `add()`, `subtract()`, `set()`.
2. Replace each with `with_delta()`, `with_balance()`.
3. Ensure every call site uses the return value.
4. Add a static check (mypy `# type: ignore` audit) for ignored
   `#[must_use]`-style returns.
5. Run the full test suite — any test that was silently passing with broken
   balances will now fail.

---

## Pattern: Imperative shell with exhaustive result handling

### Example 5: Correct shell template

The shell must handle both success and rejection, persist state + effect plan
+ nonce atomically, and return the correct HTTP status.

```python
def handle_request(
    raw_input: dict[str, Any],
    pre_root: bytes,
    expected_version: int,
) -> tuple[int, dict[str, Any]]:
    # 1. Parse and validate at the boundary (typed rejection)
    command = parse_command(raw_input)
    if isinstance(command, ParseReject):
        return 400, {"error": {"code": command.code.value, "details": ...}}

    # 2. Load state (IO — shell only)
    state = load_state_from_snapshot(pre_root)

    # 3. Call functional core (pure — returns typed result)
    result = step(state, command.value)

    # 4. Exhaustive result handling
    if isinstance(result, StepReject):
        # Rejection: do NOT persist. Return typed rejection.
        return 402, {"error": {"code": result.code.value, "details": ...}}

    # 5. Atomic commit (IO — shell only)
    #    Must persist: post-state, effect plan, nonce/replay record, receipt hash.
    #    Must NOT reconstruct economic amounts from the effect plan.
    save_state(
        root=result.state.root,
        state=result.state,
        effect_plan=result.effect,
        nonce=command.value.nonce,
        replay_record=ReplayRecord(
            pre_root=pre_root,
            post_root=result.state.root,
            command_hash=hash_command(command.value),
            effect_plan_hash=hash_effect_plan(result.effect),
        ),
    )

    # 6. Return response with receipt
    return 200, {
        "state": serialize(result.state),
        "effect_plan": serialize(result.effect),
        "receipt": {
            "pre_root": pre_root.hex(),
            "post_root": result.state.root.hex(),
            "effect_plan_hash": hash_effect_plan(result.effect).hex(),
        },
    }
```

**What the previous broken example did wrong:**
- Always returned HTTP 200 even on rejection.
- Read `result.state` even when the result was rejected (no state).
- Persisted only state, dropping the effect plan.
- No nonce/replay record.
- No receipt or effect-plan hash.

---

## Anti-examples — what NOT to generate

### Anti-example 1: The frozen lie

```python
# DO NOT GENERATE THIS
@dataclass(frozen=True)
class MyState:
    data: dict[str, Any]  # frozen lie — dict is mutable
    items: list[Item]     # frozen lie — list is mutable
```

**Why it's wrong:** `frozen=True` prevents reassigning `data` and `items`,
but the dict and list contents are fully mutable. A reviewer seeing
`frozen=True` will assume the type is immutable. It is not.

**Fix:** Use `tuple` for collections, or make the builder honestly
`@dataclass` (not frozen) if it is a local builder.

### Anti-example 2: Stringly-typed state bag

```python
# DO NOT GENERATE THIS
@dataclass(frozen=True)
class MyState:
    config: dict[str, Any]  # stringly-typed bag
```

**Why it's wrong:** Missing keys silently return `None` or a default. The
type system cannot catch incomplete construction. This pattern hides bugs.

**Fix:** Replace with a frozen dataclass that has a named field for every key.

### Anti-example 3: In-place mutation of committed state

```python
# DO NOT GENERATE THIS
def step(state: MyState, amount: int) -> None:
    state.balance += amount  # mutates committed state in place
```

**Why it's wrong:** The pre-state is destroyed. The caller cannot keep a
reference to the pre-state for comparison, replay, or rollback. Conservation
checks may observe different values before and after.

**Fix:** Return a new state via `replace(state, balance=state.balance + amount)`.

### Anti-example 4: assert for runtime validation

```python
# DO NOT GENERATE THIS
def step(state: MyState, amount: int) -> MyState:
    assert amount >= 0  # vanishes under python -O
    return replace(state, balance=state.balance + amount)
```

**Why it's wrong:** `assert` is removed when Python runs with `-O`. The
validation disappears in optimized mode.

**Fix:** Use `if amount < 0: raise ValueError(...)` or return a typed
`StepReject`.

### Anti-example 5: Float in value-moving math

```python
# DO NOT GENERATE THIS
def compute_output_amount(reserve_in: float, reserve_out: float, amount_in: float) -> float:
    return amount_in * reserve_out / (reserve_in + amount_in)
```

**Why it's wrong:** Floating-point arithmetic is non-deterministic across
platforms and loses precision. It cannot be used in consensus, accounting, or
settlement paths.

**Fix:** Use integer base units with explicit scale, rounding, and dust policy.

### Anti-example 6: Silent value-loss on immutable refactor

```python
# DO NOT GENERATE THIS
# Before: add() returns None (mutates in place)
# After: add() returns new BalanceTable (but call sites ignore return value)
balances.add(pubkey, asset, delta)  # silently does nothing now!
```

**Why it's wrong:** Keeping the same method name but changing the semantics
from mutate-in-place to return-new-value means existing call sites that ignore
the return value will silently stop moving balances.

**Fix:** Use a deliberately different method name (`with_delta()` instead of
`add()`) so existing call sites get an `AttributeError` and must be updated.

### Anti-example 7: Shell that drops the effect plan

```python
# DO NOT GENERATE THIS
def handle_request(raw_input):
    result = step(state, command)
    if result.ok:
        save_state(result.state)  # drops effect plan, nonce, receipt
    return 200, {"state": serialize(result.state)}  # always 200, reads state on reject
```

**Why it's wrong:** The effect plan is the bridge between the pure core and
actual value movement. Dropping it means the persisted state cannot be
verified against the intended effects. Always returning 200 hides rejections
from the caller. Reading `result.state` on a rejected result accesses a field
that may not exist.

**Fix:** See Example 5 above for the correct shell template.

### Anti-example 8: Pattern cargo-culting

```python
# DO NOT GENERATE THIS
class BalanceStrategy(ABC):
    @abstractmethod
    def add(self, pubkey: str, asset: str, delta: int) -> "BalanceStrategy": ...

class SimpleBalanceStrategy(BalanceStrategy):
    def add(self, pubkey: str, asset: str, delta: int) -> "BalanceStrategy":
        pass

class BalanceStrategyFactory:
    def create(self, strategy_type: str) -> BalanceStrategy:
        if strategy_type == "simple":
            return SimpleBalanceStrategy()
        raise ValueError(f"unknown strategy: {strategy_type}")
```

**Why it's wrong:** This adds an abstract base class, a factory, and a
strategy pattern for a single implementation. It makes the code harder to
audit without adding any safety or flexibility.

**Fix:** Use a frozen dataclass with a pure `with_delta` method. Add the
strategy pattern only when there are multiple interchangeable implementations
behind the same typed contract.

### Anti-example 9: Shallow copy that aliases nested mutable state

```python
# DO NOT GENERATE THIS
def build_ctx(state: DexState) -> Ctx:
    markets = dict(state.perps.markets)  # copies outer dict only
    # PerpMarketState values are still aliased to the original state.
    # If global_state (a Dict[str, Value]) is mutated, the original
    # state is corrupted.
    return Ctx(markets=markets)
```

**Why it's wrong:** Copying the outer container does not copy nested mutable
values. `PerpMarketState.global_state` is a `Dict[str, Value]` — mutating it
through the copy also mutates the original.

**Fix:** Deep-copy nested mutable values, or make `PerpMarketState` transitively
immutable so aliasing is safe.
