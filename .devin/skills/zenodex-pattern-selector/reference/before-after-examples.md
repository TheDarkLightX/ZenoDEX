# Boundary-Aware Before and After Examples

These examples are templates, not substitutes for the domain model.

## 1. Broad helper and narrow proof profile

### Wrong: silently narrow the reusable helper

```rust
fn deposit_mint(input: DepositMintInput) -> Result<Journal, Error> {
    if input.mcr_bps != 11_000 {
        return Err(Error::WrongMcr);
    }
    // The helper can no longer represent legitimate nonbaseline experiments.
    ...
}
```

### Wrong: let every helper result acquire profile authority

```rust
fn authorized_mint_row(journal: &Journal, policy_hash: Hash) -> MintRow {
    // Nonzero policy_hash does not prove the journal used that policy.
    MintRow::new(journal.minted, policy_hash)
}
```

### Correct: preserve helper scope, narrow at the authority boundary

```rust
fn deposit_mint(input: DepositMintInput) -> Result<GenericJournal, Error> {
    require!(input.mcr_bps > 10_000);
    ...
}

fn project_liquity_v1_minimum(
    journal: &GenericJournal,
    binding: &GovernedProfileBinding,
) -> Result<AuthorizedMintRow, ProfileReject> {
    if journal.mcr_bps != 11_000 {
        return Err(ProfileReject::McrMismatch);
    }
    if journal.pre_state_root != binding.expected_pre_state_root {
        return Err(ProfileReject::PrestateMismatch);
    }
    if journal.image_id != binding.base_image_id {
        return Err(ProfileReject::ImageMismatch);
    }
    AuthorizedMintRow::trusted_new(journal, binding)
}
```

The generic helper remains broader. The profile certificate proves one exact
member of that family.

---

## 2. Functional core and thin semantic shell

### Wrong: shell recomputes economics

```python
def handle_liquidation(request: dict[str, object]) -> Response:
    state = load_state()
    debt = state.vault.debt
    offset = min(debt, state.sp_balance)
    collateral_to_sp = state.vault.collateral * offset // debt
    if state.recovery_mode:
        collateral_to_sp = 0
    save_state(apply_numbers(state, offset, collateral_to_sp))
    return Response.ok()
```

The shell now owns liquidation mode, arithmetic, and effects.

### Correct: shell supplies facts and executes one plan

```python
def handle_liquidation(raw: Mapping[str, object]) -> Response:
    command = parse_liquidation_command(raw)
    snapshot = load_committed_snapshot(command.expected_pre_root)
    oracle = authenticate_oracle_snapshot(raw["oracle"], snapshot.policy)
    caller = authenticate_actor(raw["signature"], command)

    outcome = liquidate(snapshot.protocol_state, command, oracle, caller)
    if isinstance(outcome, LiquidationReject):
        return reject_response(outcome)

    committed = commit_bundle_compare_and_swap(
        expected_pre_root=command.expected_pre_root,
        post_state=outcome.post_state,
        effects=outcome.effects,
        nullifiers=outcome.nullifiers,
        receipt=outcome.receipt,
        outbox=outcome.outbox,
    )
    return committed_response(committed)
```

The shell branches on typed result and commit status. The core owns liquidation
semantics.

---

## 3. Effects as pure values

### Wrong: core mutates an adapter

```python
def repay(state: State, amount: int, ledger: Ledger) -> State:
    ledger.burn_zusd(state.owner, amount)
    return replace(state, debt=state.debt - amount)
```

### Correct: core returns an immutable effect plan

```python
@dataclass(frozen=True, slots=True)
class BurnEffect:
    effect_id: EffectId
    owner: AccountId
    asset: AssetId
    amount_atoms: int
    source_balance_root: Root

@dataclass(frozen=True, slots=True)
class RepayAccepted:
    post_state: State
    effects: tuple[BurnEffect, ...]
    receipt: RepayReceipt


def repay(state: State, command: RepayCommand) -> RepayAccepted | RepayReject:
    ...
```

The shell applies the returned burn exactly once at CAS commit.

---

## 4. Authenticated facts instead of verdict Booleans

### Wrong

```python
@dataclass(frozen=True)
class MintCommand:
    amount: int
    oracle_ok: bool
    auth_ok: bool
```

A caller can construct both flags.

### Correct

```python
@dataclass(frozen=True, slots=True)
class VerifiedOracleSnapshot:
    chain_id: ChainId
    asset_pair: AssetPair
    price_e8: int
    observed_epoch: int
    expires_epoch: int
    state_root: Root
    producer_root: Root
    evidence_root: Root

    _seal: object = field(repr=False, compare=False)


def mint(
    state: State,
    command: MintCommand,
    oracle: VerifiedOracleSnapshot,
    actor: AuthenticatedActor,
) -> MintOutcome:
    ...
```

The trusted boundary owns construction. The core still rechecks subject, root,
profile, and freshness bindings relevant to the command.

---

## 5. Complete canonical violation vectors

### Wrong: first error hides independent defects

```python
def validate(candidate: Candidate) -> RejectCode | None:
    if candidate.free_liabilities != candidate.free_debt:
        return RejectCode.FREE_COVER
    if candidate.sp_custody != candidate.sp_debt:
        return RejectCode.SP_COVER
    if candidate.free_debt + candidate.sp_debt != candidate.total_debt:
        return RejectCode.DEBT_SPLIT
    return None
```

### Correct

```python
VIOLATION_ORDER = (
    Violation.FREE_COVER,
    Violation.SP_COVER,
    Violation.DEBT_SPLIT,
    Violation.GLOBAL_COVER,
)


def validate(candidate: Candidate) -> tuple[Violation, ...]:
    failed: list[Violation] = []
    if candidate.free_liabilities != candidate.free_debt:
        failed.append(Violation.FREE_COVER)
    if candidate.sp_custody != candidate.sp_debt:
        failed.append(Violation.SP_COVER)
    if candidate.free_debt + candidate.sp_debt != candidate.total_debt:
        failed.append(Violation.DEBT_SPLIT)
    if candidate.free_liabilities + candidate.sp_custody != candidate.total_debt:
        failed.append(Violation.GLOBAL_COVER)
    return tuple(failed)
```

The result constructor should rederive the vector so forged omissions or
reordering are unrepresentable.

---

## 6. Frozen lie versus immutable value

### Wrong

```python
@dataclass(frozen=True)
class MonetaryState:
    deposits: dict[str, int]
    claims: dict[str, int]
```

Both dictionaries remain mutable.

### Correct for small canonical state

```python
@dataclass(frozen=True, slots=True)
class AccountAmount:
    account: AccountId
    amount_atoms: int

@dataclass(frozen=True, slots=True)
class MonetaryState:
    deposits: tuple[AccountAmount, ...]
    claims: tuple[AccountAmount, ...]

    def __post_init__(self) -> None:
        require_sorted_unique_accounts(self.deposits)
        require_sorted_unique_accounts(self.claims)
```

### Correct for large hot state

Use a purpose-built persistent map or a privately owned indexed representation
behind an immutable interface. Define canonical bytes independently. Do not
replace a 100,000-entry map with tuple linear scans merely to satisfy a style
rule.

---

## 7. Local mutable builder

### Correct

```python
@dataclass
class _PlanBuilder:
    transfers: list[TransferEffect]
    violations: list[Violation]


def build_plan(inputs: Inputs) -> Plan | Reject:
    builder = _PlanBuilder(transfers=[], violations=[])
    ...
    if builder.violations:
        return Reject(tuple(builder.violations))
    return Plan(transfers=tuple(builder.transfers))
```

Conditions:

- freshly constructed per call;
- no alias to committed state;
- discarded on rejection;
- output transitively immutable;
- mutation is not observable outside the pure call.

---

## 8. Exception boundaries

### Wrong: implementation bugs become protocol outcomes

```python
def step(state: State, command: Command) -> StepResult:
    try:
        ...
    except Exception as exc:
        return StepReject(code="invalid", details=str(exc))
```

This can hide `AttributeError`, incorrect field names, arithmetic bugs, and
unexpected adapter objects.

### Correct

```python
def step(state: State, command: Command) -> StepResult:
    if command.amount <= 0:
        return StepReject(RejectCode.AMOUNT_NOT_POSITIVE, ...)
    ...
```

Trusted-construction violations raise explicit `TypeError` or `ValueError`.
Operational exceptions are caught in the shell and mapped to a separate
operational error policy.

---

## 9. Bound witness

### Wrong

```python
@dataclass(frozen=True)
class Eligible:
    ok: bool = True
```

### Correct

```python
@dataclass(frozen=True, slots=True)
class EligibleLiquidationPlan:
    vault_id: VaultId
    command_hash: Hash
    pre_state_root: Root
    oracle_root: Root
    policy_root: Root
    protocol_version: ProtocolVersion
    evidence_root: Root
    plan: LiquidationPlan
```

The shell commits only if the live root still equals `pre_state_root`.

---

## 10. Immutable API migration

### Wrong

```python
# Old API mutated and returned None.
balances.add(account, asset, delta)

# New implementation returns a new value under the same name.
def add(...) -> BalanceTable:
    ...
```

Existing callers silently ignore the returned state.

### Correct

```python
new_balances = balances.with_delta(account, asset, delta)
```

Use a deliberately different name, inventory every call site, and add a static
or mutation test that catches an ignored return value.
