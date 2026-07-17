# Pattern Selector — Before/After Examples

Concrete before/after examples for agents generating code. These examples
use the specification-first `Decision` type with explicit commit semantics
and `Evidence` as an explicit input.

## Pattern: Authoritative core + typed Decision

### Example 1: A value-moving transition with explicit commit semantics

```python
class RejectCode(Enum):
    NEGATIVE_AMOUNT = "negative_amount"
    INSUFFICIENT_BALANCE = "insufficient_balance"
    STALE_ORACLE = "stale_oracle"

@dataclass(frozen=True)
class Evidence:
    """Explicit inputs that are not ambient reads."""
    block_timestamp: int
    oracle_price_e8: int
    oracle_timestamp: int
    signatures: tuple[Signature, ...]
    governance_epoch: int
    randomness_seed: int

@dataclass(frozen=True)
class CommitSuccess:
    state: MyState
    effect_plan: MyEffectPlan

@dataclass(frozen=True)
class RejectNoCommit:
    """Pre-state and effects remain untouched."""
    code: RejectCode
    details: RejectDetails  # frozen dataclass, not str

@dataclass(frozen=True)
class CommitProtocolFailure:
    """State was committed (nonce consumed, fee charged) despite economic failure."""
    state: MyState
    code: RejectCode
    details: RejectDetails

Decision = CommitSuccess | RejectNoCommit | CommitProtocolFailure

def step(
    pre_state: MyState,
    command: MyCommand,
    evidence: Evidence,
) -> Decision:
    if command.amount < 0:
        return RejectNoCommit(
            code=RejectCode.NEGATIVE_AMOUNT,
            details=RejectDetails(field="amount", value=command.amount),
        )
    if evidence.oracle_timestamp < pre_state.last_oracle_timestamp:
        return RejectNoCommit(
            code=RejectCode.STALE_ORACLE,
            details=RejectDetails(
                field="oracle_timestamp",
                value=evidence.oracle_timestamp,
            ),
        )
    new_balance = pre_state.balance + command.amount
    new_state = replace(pre_state, balance=new_balance)
    return CommitSuccess(
        state=new_state,
        effect_plan=MyEffectPlan(delta=command.amount),
    )
```

Negative tests assert the rejection enum AND the commit semantics:

```python
def test_negative_amount_rejected_no_commit():
    result = step(pre_state, MyCommand(amount=-1), evidence)
    assert isinstance(result, RejectNoCommit)
    assert result.code == RejectCode.NEGATIVE_AMOUNT
    # Verify pre-state is untouched — no mutable alias survived
    assert pre_state.balance == original_balance

def test_stale_oracle_rejected_no_commit():
    result = step(pre_state, command, stale_evidence)
    assert isinstance(result, RejectNoCommit)
    assert result.code == RejectCode.STALE_ORACLE
```

### When to use exceptions instead

```python
# Contract violation after trusted construction — programmer error, not protocol.
# The input crossed a trust boundary and was already validated.
def require_int_range(value: object, name: str, lo: int, hi: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < lo or value > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}]")
    return value
```

### Committed-failure example

Some protocols consume a nonce or charge a fee even on rejection:

```python
def step_with_nonce(
    pre_state: MyState,
    command: MyCommand,
    evidence: Evidence,
) -> Decision:
    # Nonce is consumed regardless of economic outcome
    new_nonce_state = advance_nonce(pre_state, command.nonce)
    if command.amount < 0:
        return CommitProtocolFailure(
            state=new_nonce_state,
            code=RejectCode.NEGATIVE_AMOUNT,
            details=RejectDetails(field="amount", value=command.amount),
        )
    # ... economic logic ...
    return CommitSuccess(state=new_state, effect_plan=...)
```

The shell must handle `CommitProtocolFailure` by committing the state (the
nonce was consumed), not by discarding it.

---

## Pattern: Authoritative core with internal mutable builder

### Example 2: Honest mutable builder with immutable output

```python
@dataclass  # honestly mutable — no frozen=True
class _SettlementBuffers:
    fills: list[Fill]
    balance_deltas: list[BalanceDelta]

def compute_settlement(
    pre_state: MyState,
    command: MyCommand,
    evidence: Evidence,
) -> Decision:
    buffers = _SettlementBuffers(fills=[], balance_deltas=[])
    # ... accumulate into buffers ...
    # Boundary: convert to immutable tuples, seal validates invariants
    settlement = Settlement(
        fills=tuple(buffers.fills),
        balance_deltas=tuple(buffers.balance_deltas),
    )
    # Postcondition: conservation check before returning
    if not _check_conservation(pre_state, settlement):
        return RejectNoCommit(
            code=RejectCode.CONSERVATION_VIOLATION,
            details=RejectDetails(field="settlement", value=...),
        )
    return CommitSuccess(state=..., effect_plan=...)
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

The shell must capture evidence once, run the pure transition, check
postconditions, use compare-and-swap on the expected pre-root, handle all
three Decision variants exhaustively, and return a receipt from the
successful commit.

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
    # 1. Decode and resource-bound input at the boundary
    command = parse_command(raw_input)
    if isinstance(command, ParseReject):
        return 400, {"error": {"code": command.code.value, "details": ...}}

    # 2. Capture authenticated evidence once
    evidence = capture_evidence(
        block_timestamp=get_block_timestamp(),
        oracle_price_e8=get_oracle_price(),
        oracle_timestamp=get_oracle_timestamp(),
        signatures=extract_signatures(raw_input),
        governance_epoch=get_governance_epoch(),
        randomness_seed=get_randomness_seed(),
    )

    # 3. Run pure transition
    result = step(snapshot.state, command.value, evidence)

    # 4. Exhaustive result handling — three Decision variants
    if isinstance(result, RejectNoCommit):
        # No-commit rejection: do NOT persist. Pre-state is untouched.
        return 422, {"error": {"code": result.code.value, "details": ...}}

    if isinstance(result, CommitProtocolFailure):
        # Committed failure: nonce consumed, fee charged. Must commit the state.
        commit_result = commit_transition(
            expected_pre_root=snapshot.root,
            expected_version=snapshot.version,
            post_state=result.state,
            effect_plan=EffectPlan.empty(),  # no economic effects
            replay_record=ReplayRecord(
                pre_root=snapshot.root,
                post_root=result.state.root,
                command_hash=hash_command(command.value),
                effect_plan_hash=hash_effect_plan(EffectPlan.empty()),
            ),
        )
        if isinstance(commit_result, CommitConflict):
            return 409, {"error": {"code": "commit_conflict", ...}}
        return 422, {
            "error": {"code": result.code.value, "details": ...},
            "receipt": {"post_root": commit_result.receipt.post_root.hex()},
        }

    # result is CommitSuccess — proceed to commit

    # 5. Check postconditions before commit
    if not check_conservation(snapshot.state, result.state, result.effect_plan):
        # Internal invariant failure — do not commit, raise
        raise RuntimeError("conservation postcondition violated")

    # 6. Atomic commit with compare-and-swap
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

    # 7. Idempotently deliver external effects via outbox
    deliver_effects(result.effect_plan, commit_result.receipt)

    # 8. Return response with receipt from the successful commit
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
- No postcondition check before commit.
- Receipt was constructed optimistically instead of returned by the commit.
- Persisting the effect plan was conflated with executing it (external effects
  need a transactional outbox).
- "Exhaustive" handling assumed every non-reject was success.
- Every protocol rejection became HTTP 402 (should be 422 for semantic
  rejection, 409 for conflict).
- No `CommitProtocolFailure` handling (committed failures were silently
  dropped).
- No `Evidence` capture — time and oracle data were ambient reads.

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
`@dataclass` (not frozen). Surface immutability is a representation property,
not an assurance result.

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
`RejectNoCommit`.

### Anti-example 5: Float in value-moving math

```python
# DO NOT GENERATE THIS
def compute_output_amount(r_in: float, r_out: float, a_in: float) -> float:
    return a_in * r_out / (r_in + a_in)
```

**Fix:** Use integer base units with named rounding operations and dust policy.

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
nonce, receipt, postcondition checks, and outbox for external effects.

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

### Anti-example 10: Moving semantic checks to the shell

```python
# DO NOT GENERATE THIS
def handle_request(raw_input, snapshot):
    command = parse_command(raw_input)
    # WRONG: economic check in the shell, not the core
    if command.amount > snapshot.state.balance:
        return 422, {"error": "insufficient balance"}
    result = step(snapshot.state, command.value)
    ...
```

**Fix:** Authorization, admission, economics, freshness, and replay are core
responsibilities. The shell acquires input and commits effects; it never
decides settlement semantics. Move the check into `step()` and return
`RejectNoCommit` from the core.

### Anti-example 11: Treating frozen=True as a correctness proof

```python
# DO NOT GENERATE THIS
@dataclass(frozen=True)
class LiquidationResult:
    # frozen=True does not prove the liquidation semantics are correct.
    # It only proves the fields cannot be reassigned.
    # The assurance comes from the specification, invariant checks,
    # and replayable evidence — not from the frozen decorator.
    state: MyState
    effect_plan: MyEffectPlan
```

**Fix:** `frozen=True` is a representation property. The assurance comes from
the specification, the refinement steps, and the replayable evidence. Write
the specification, check the invariants (conservation, monotonicity, etc.),
and produce replayable evidence (differential vectors, property tests, proofs).
