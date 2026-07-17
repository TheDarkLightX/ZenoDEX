# Pattern Selector — Before/After Examples

Concrete before/after examples for each pattern in the ZenoDEX codebase.
These are the examples agents should follow when generating code.

## Pattern A: Pure Immutable Deterministic Function

### Example A1: Making a state type immutable

**Before** (mutable, in-place mutation):

```python
@dataclass
class PoolState:
    pool_id: str
    reserve0: int
    reserve1: int
    lp_supply: int
    # ...

# Mutation site:
context.pool_state.reserve0 += amount_in
context.pool_state.reserve1 -= amount_out
```

**After** (frozen, replace-based transition):

```python
@dataclass(frozen=True)
class PoolState:
    pool_id: str
    reserve0: int
    reserve1: int
    lp_supply: int
    # ...

    def with_reserves(self, reserve0: int, reserve1: int) -> "PoolState":
        return replace(self, reserve0=reserve0, reserve1=reserve1)

# Transition site:
new_pool = context.pool_state.with_reserves(
    reserve0=context.pool_state.reserve0 + amount_in,
    reserve1=context.pool_state.reserve1 - amount_out,
)
```

### Example A2: Making a table type immutable

**Before** (mutable class, in-place mutation):

```python
class BalanceTable:
    def __init__(self):
        self._balances: dict[tuple[str, str], int] = {}

    def add(self, pubkey: str, asset: str, delta: int) -> None:
        current = self.get(pubkey, asset)
        self.set(pubkey, asset, current + delta)

# Mutation site:
balances.add(pubkey, asset, delta)  # mutates in place
```

**After** (frozen dataclass, returns new value):

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

    def add(self, pubkey: str, asset: str, delta: int) -> "BalanceTable":
        current = self.get(pubkey, asset)
        new_balance = current + delta
        if new_balance < 0:
            raise ValueError(f"Insufficient balance: {current} + {delta}")
        return self.set(pubkey, asset, new_balance)

    def set(self, pubkey: str, asset: str, amount: int) -> "BalanceTable":
        # ... return a new BalanceTable with the entry replaced ...
        pass

# Transition site:
new_balances = balances.add(pubkey, asset, delta)  # returns new table
```

### Example A3: Replacing a stringly-typed dict with a frozen dataclass

**Before** (stringly-typed bag, missing keys silently return None):

```python
@dataclass(frozen=True)
class PerpMarketState:
    global_state: dict[str, Value]  # frozen lie + stringly-typed

# Access:
fee_pool = market.global_state.get("fee_pool_quote", 0)  # silent default
```

**After** (named fields, typed, construction-time validation):

```python
@dataclass(frozen=True)
class PerpGlobalState:
    now_epoch: int = 0
    fee_pool_quote: int = 0
    insurance_balance: int = 0
    liquidation_gas_comp_bps: int = 0
    # ... every key that was in the dict ...

@dataclass(frozen=True)
class PerpMarketState:
    global_state: PerpGlobalState  # named fields, typed

# Access:
fee_pool = market.global_state.fee_pool_quote  # typed, always present
```

### Example A4: Replacing a dict field with a sorted tuple

**Before** (mutable dict, non-deterministic iteration):

```python
@dataclass(frozen=True)
class PerpMarketState:
    accounts: dict[str, PerpAccountState]  # frozen lie

# Mutation:
market.accounts[pubkey] = new_account  # mutates without producing new state
```

**After** (sorted tuple, immutable):

```python
@dataclass(frozen=True)
class PerpMarketState:
    accounts: tuple[tuple[str, PerpAccountState], ...]  # sorted by pubkey

# Transition:
new_accounts = _update_account(state.accounts, pubkey, new_account)
new_state = replace(state, accounts=new_accounts)
```

---

## Pattern B: Local Mutable Builder

### Example B1: Honest mutable builder with immutable output

**Before** (frozen lie on a mutable builder):

```python
@dataclass(frozen=True)  # frozen lie — fields are mutable
class _SettlementExecutionState:
    pool_states: dict[str, PoolState]  # mutable
    buffers: _SettlementBuffers         # mutable
```

**After** (honestly mutable builder):

```python
@dataclass  # honestly mutable
class _SettlementExecutionState:
    pool_states: dict[str, PoolState]  # mutable, but builder is local
    buffers: _SettlementBuffers

# Output at boundary is immutable:
def compute_settlement(...) -> Settlement:
    state = _SettlementExecutionState(...)
    # ... accumulate into state ...
    return Settlement(
        fills=tuple(state.buffers.fills),           # immutable
        balance_deltas=tuple(state.buffers.balance_deltas),  # immutable
        # ...
    )
```

### Example B2: Copy-then-mutate-then-return

**Before** (mutates original state):

```python
def apply_settlement(settlement, balances, pools):
    for delta in settlement.balance_deltas:
        balances.add(delta.pubkey, delta.asset, delta.net_delta())  # mutates original
    return balances
```

**After** (copies before mutating, returns copy):

```python
def apply_settlement_pure(settlement, balances, pools):
    balances_copy = copy_balance_table(balances)  # fresh copy
    pools_copy = {pid: replace(p) for pid, p in pools.items()}  # fresh copies
    # mutate copies
    for delta in settlement.balance_deltas:
        balances_copy = balances_copy.add(delta.pubkey, delta.asset, delta.net_delta())
    return balances_copy, pools_copy  # original untouched
```

---

## Pattern C: Railway / Result

### Example C1: Typed result for a transition step

**Before** (exception-driven, no typed rejection):

```python
def step(state, command):
    if command.amount < 0:
        raise ValueError("negative amount")  # generic, not a protocol outcome
    # ...
    return new_state
```

**After** (typed result, stable rejection code):

```python
@dataclass(frozen=True)
class StepOk:
    state: MyState
    effect: MyEffect

@dataclass(frozen=True)
class StepError:
    code: str
    message: str

def step(state: MyState, command: MyCommand) -> StepOk | StepError:
    if command.amount < 0:
        return StepError(code="negative_amount", message="amount must be non-negative")
    # ...
    return StepOk(state=new_state, effect=MyEffect(...))
```

### Example C2: When to use exceptions instead

```python
# This is a contract violation (programmer error), not a protocol outcome.
# Use an exception, not a Result.
def require_int_range(value: object, name: str, lo: int, hi: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < lo or value > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}]")
    return value
```

---

## Pattern D: Imperative Shell

### Example D1: Shell handler that delegates to core

```python
def handle_request(raw_input: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    # 1. Parse and validate at the boundary (Pattern C)
    command = parse_command(raw_input)
    if not command.ok:
        return 400, {"error": command.reason}

    # 2. Load state (IO — shell only)
    state = load_state_from_snapshot()

    # 3. Call functional core (Pattern A — pure)
    result = step(state, command.value)

    # 4. Persist state (IO — shell only)
    if result.ok:
        save_state(result.state)

    # 5. Return response
    return 200, {"state": serialize(result.state)}
```

### Example D2: Mutable shell context (acceptable)

```python
@dataclass  # honestly mutable, transaction-local
class _PerpApplyCtx:
    config: PerpEngineConfig
    balances: BalanceTable       # mutable copy, not aliased with committed state
    markets: dict[str, PerpAnyMarketState]  # mutable, transaction-local
    effects: list[dict[str, Any]]

def apply_transaction(ctx: _PerpApplyCtx, command: PerpCommand) -> PerpTxResult:
    # ctx is freshly constructed per transaction
    # ctx is discarded on rejection
    # committed state at the boundary is immutable
    ...
```

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

**Why it's wrong:** The `frozen=True` flag prevents reassigning `data` and
`items`, but the dict and list contents are fully mutable. A reviewer seeing
`frozen=True` will assume the type is immutable. It is not.

**Fix:** Use `tuple` for collections, or make the builder honestly `@dataclass`
(not frozen) if it is a local builder.

### Anti-example 2: Stringly-typed state bag

```python
# DO NOT GENERATE THIS
@dataclass(frozen=True)
class MyState:
    config: dict[str, Any]  # stringly-typed bag
```

**Why it's wrong:** Missing keys silently return `None` or a default. The type
system cannot catch incomplete construction. This pattern hides bugs.

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
`StepError`.

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

### Anti-example 6: Pattern cargo-culting

```python
# DO NOT GENERATE THIS
class BalanceStrategy(ABC):
    @abstractmethod
    def add(self, pubkey: str, asset: str, delta: int) -> "BalanceStrategy": ...

class SimpleBalanceStrategy(BalanceStrategy):
    def add(self, pubkey: str, asset: str, delta: int) -> "BalanceStrategy":
        # ... implementation ...
        pass

class BalanceStrategyFactory:
    def create(self, strategy_type: str) -> BalanceStrategy:
        if strategy_type == "simple":
            return SimpleBalanceStrategy()
        raise ValueError(f"unknown strategy: {strategy_type}")
```

**Why it's wrong:** This adds an abstract base class, a factory, and a strategy
pattern for a single implementation. It makes the code harder to audit without
adding any safety or flexibility.

**Fix:** Use a frozen dataclass with a pure `add` method. Add the strategy
pattern only when there are multiple interchangeable implementations behind
the same typed contract.
