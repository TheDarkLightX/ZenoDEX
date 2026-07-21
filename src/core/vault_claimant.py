"""Claimant-indexed reward-vault functional core.

The historical ``src.core.vault`` module is an aggregate bounded reference model.
It has no claimant identity and therefore cannot safely authorize multi-user
reward claims. This module represents the production claimant relation directly:

* every account has active and pending shares, reward debt, claimable rewards,
  and an exact replay nonce;
* reward funding has its own exact replay nonce;
* staking after an accrual snapshots the current accumulator and cannot capture
  historical rewards;
* unstaking settles the claimant first and preserves earned rewards;
* claims update only the named claimant and emit an immutable transfer plan;
* rounding and no-staker deposits remain explicit protocol residue;
* every rejected command is an exact no-state/no-effect result.

This module performs no I/O, authentication, clock access, persistence, or token
transfer. A shell must authenticate command identities, atomically commit the
returned state and effect plan, and deliver transfers idempotently.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Final, Literal, TypeAlias

ACC_SCALE: Final = 10**18
MAX_U256: Final = (1 << 256) - 1
MAX_ACCOUNTS: Final = 100_000
MAX_CLAIMANT_BYTES: Final = 512
MAX_EFFECT_TRANSFERS: Final = 8


def _require_u256(value: int, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0 or value > MAX_U256:
        raise ValueError(f"{name} must be in [0, 2^256-1]")
    return int(value)


def _checked_add(left: int, right: int, *, name: str) -> int:
    result = _require_u256(left, name=f"{name}.left") + _require_u256(
        right,
        name=f"{name}.right",
    )
    if result > MAX_U256:
        raise OverflowError(f"{name} overflow")
    return result


def _checked_mul(left: int, right: int, *, name: str) -> int:
    left = _require_u256(left, name=f"{name}.left")
    right = _require_u256(right, name=f"{name}.right")
    result = left * right
    if result > MAX_U256:
        raise OverflowError(f"{name} overflow")
    return result


def _require_positive(value: int, *, name: str) -> int:
    value = _require_u256(value, name=name)
    if value == 0:
        raise ValueError(f"{name} must be positive")
    return value


def _require_claimant(value: str, *, name: str = "claimant") -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value or len(value.encode("utf-8")) > MAX_CLAIMANT_BYTES:
        raise ValueError(
            f"{name} must be non-empty and at most {MAX_CLAIMANT_BYTES} UTF-8 bytes"
        )
    return value


def _require_next_nonce(observed: int, previous: int, *, name: str) -> int:
    observed = _require_u256(observed, name=name)
    previous = _require_u256(previous, name=f"previous_{name}")
    if previous == MAX_U256 or observed != previous + 1:
        raise ValueError(f"{name} must equal previous nonce + 1")
    return observed


@dataclass(frozen=True, slots=True, order=True)
class VaultAccount:
    """One claimant's complete reward and share entitlement state."""

    claimant: str
    active_shares: int = 0
    pending_shares: int = 0
    reward_debt: int = 0
    claimable: int = 0
    last_nonce: int = 0

    def __post_init__(self) -> None:
        _require_claimant(self.claimant)
        for name in (
            "active_shares",
            "pending_shares",
            "reward_debt",
            "claimable",
            "last_nonce",
        ):
            _require_u256(getattr(self, name), name=f"account.{name}")


@dataclass(frozen=True, slots=True)
class ClaimantVaultState:
    """Canonical claimant vector plus aggregate reward custody."""

    accounts: tuple[VaultAccount, ...] = ()
    acc_reward_per_share: int = 0
    reward_balance: int = 0
    explicit_residue: int = 0
    cumulative_deposited: int = 0
    cumulative_claimed: int = 0
    cumulative_drained: int = 0
    last_funding_nonce: int = 0

    total_active_shares: int = field(init=False)
    total_pending_shares: int = field(init=False)
    aggregate_owned_rewards: int = field(init=False)

    def __post_init__(self) -> None:
        if not isinstance(self.accounts, tuple):
            raise TypeError("accounts must be a tuple")
        if len(self.accounts) > MAX_ACCOUNTS:
            raise ValueError("too many vault accounts")
        if any(not isinstance(account, VaultAccount) for account in self.accounts):
            raise TypeError("accounts contain a non-VaultAccount")
        canonical_accounts = tuple(sorted(self.accounts, key=lambda item: item.claimant))
        if len({account.claimant for account in canonical_accounts}) != len(
            canonical_accounts
        ):
            raise ValueError("duplicate vault claimant")
        object.__setattr__(self, "accounts", canonical_accounts)

        for name in (
            "acc_reward_per_share",
            "reward_balance",
            "explicit_residue",
            "cumulative_deposited",
            "cumulative_claimed",
            "cumulative_drained",
            "last_funding_nonce",
        ):
            _require_u256(getattr(self, name), name=name)

        total_active = 0
        total_pending = 0
        aggregate_owned = 0
        for account in canonical_accounts:
            total_active = _checked_add(
                total_active,
                account.active_shares,
                name="total_active_shares",
            )
            total_pending = _checked_add(
                total_pending,
                account.pending_shares,
                name="total_pending_shares",
            )
            gross = _gross_reward(
                account.active_shares,
                self.acc_reward_per_share,
            )
            if account.reward_debt > gross:
                raise ValueError("account reward_debt exceeds gross accrued reward")
            unsettled = gross - account.reward_debt
            account_owned = _checked_add(
                account.claimable,
                unsettled,
                name="account_owned_rewards",
            )
            aggregate_owned = _checked_add(
                aggregate_owned,
                account_owned,
                name="aggregate_owned_rewards",
            )

        if _checked_add(
            aggregate_owned,
            self.explicit_residue,
            name="owned_plus_residue",
        ) != self.reward_balance:
            raise ValueError(
                "reward_balance must equal aggregate claimant ownership plus explicit residue"
            )
        if _checked_add(
            _checked_add(
                self.reward_balance,
                self.cumulative_claimed,
                name="custody_plus_claimed",
            ),
            self.cumulative_drained,
            name="custody_claimed_drained",
        ) != self.cumulative_deposited:
            raise ValueError(
                "reward conservation violated: custody + claimed + drained != deposited"
            )

        object.__setattr__(self, "total_active_shares", total_active)
        object.__setattr__(self, "total_pending_shares", total_pending)
        object.__setattr__(self, "aggregate_owned_rewards", aggregate_owned)

    def account(self, claimant: str) -> VaultAccount | None:
        claimant = _require_claimant(claimant)
        for account in self.accounts:
            if account.claimant == claimant:
                return account
        return None


@dataclass(frozen=True, slots=True)
class DepositRewards:
    amount: int
    funding_nonce: int

    def __post_init__(self) -> None:
        _require_positive(self.amount, name="amount")
        _require_u256(self.funding_nonce, name="funding_nonce")


@dataclass(frozen=True, slots=True)
class QueueStake:
    claimant: str
    shares: int
    nonce: int

    def __post_init__(self) -> None:
        _require_claimant(self.claimant)
        _require_positive(self.shares, name="shares")
        _require_u256(self.nonce, name="nonce")


@dataclass(frozen=True, slots=True)
class ActivateStake:
    claimant: str
    shares: int
    nonce: int

    def __post_init__(self) -> None:
        _require_claimant(self.claimant)
        _require_positive(self.shares, name="shares")
        _require_u256(self.nonce, name="nonce")


@dataclass(frozen=True, slots=True)
class CancelPendingStake:
    claimant: str
    shares: int
    nonce: int

    def __post_init__(self) -> None:
        _require_claimant(self.claimant)
        _require_positive(self.shares, name="shares")
        _require_u256(self.nonce, name="nonce")


@dataclass(frozen=True, slots=True)
class Unstake:
    claimant: str
    shares: int
    nonce: int

    def __post_init__(self) -> None:
        _require_claimant(self.claimant)
        _require_positive(self.shares, name="shares")
        _require_u256(self.nonce, name="nonce")


@dataclass(frozen=True, slots=True)
class ClaimRewards:
    claimant: str
    nonce: int

    def __post_init__(self) -> None:
        _require_claimant(self.claimant)
        _require_u256(self.nonce, name="nonce")


@dataclass(frozen=True, slots=True)
class DrainResidue:
    recipient: str
    funding_nonce: int

    def __post_init__(self) -> None:
        _require_claimant(self.recipient, name="recipient")
        _require_u256(self.funding_nonce, name="funding_nonce")


VaultCommand: TypeAlias = (
    DepositRewards
    | QueueStake
    | ActivateStake
    | CancelPendingStake
    | Unstake
    | ClaimRewards
    | DrainResidue
)


@dataclass(frozen=True, slots=True)
class RewardTransfer:
    recipient: str
    amount: int
    reason: Literal["CLAIM", "RESIDUE_DRAIN"]

    def __post_init__(self) -> None:
        _require_claimant(self.recipient, name="recipient")
        _require_positive(self.amount, name="transfer amount")


@dataclass(frozen=True, slots=True)
class ShareTransfer:
    claimant: str
    shares: int
    direction: Literal["INTO_VAULT", "OUT_OF_VAULT"]

    def __post_init__(self) -> None:
        _require_claimant(self.claimant)
        _require_positive(self.shares, name="transfer shares")


@dataclass(frozen=True, slots=True)
class ClaimantVaultEffects:
    reward_transfers: tuple[RewardTransfer, ...] = ()
    share_transfers: tuple[ShareTransfer, ...] = ()
    accumulator_delta: int = 0
    explicit_residue_delta: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.reward_transfers, tuple) or not isinstance(
            self.share_transfers,
            tuple,
        ):
            raise TypeError("effect transfers must be tuples")
        if len(self.reward_transfers) + len(self.share_transfers) > MAX_EFFECT_TRANSFERS:
            raise ValueError("too many vault effect transfers")
        if any(
            not isinstance(transfer, RewardTransfer)
            for transfer in self.reward_transfers
        ):
            raise TypeError("reward_transfers contain an invalid value")
        if any(
            not isinstance(transfer, ShareTransfer)
            for transfer in self.share_transfers
        ):
            raise TypeError("share_transfers contain an invalid value")
        _require_u256(self.accumulator_delta, name="accumulator_delta")
        if not isinstance(self.explicit_residue_delta, int) or isinstance(
            self.explicit_residue_delta,
            bool,
        ):
            raise TypeError("explicit_residue_delta must be an int")
        if abs(self.explicit_residue_delta) > MAX_U256:
            raise ValueError("explicit_residue_delta out of range")


@dataclass(frozen=True, slots=True)
class ClaimantVaultStepResult:
    ok: bool
    state: ClaimantVaultState | None = None
    effects: ClaimantVaultEffects | None = None
    error: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if not isinstance(self.state, ClaimantVaultState):
                raise ValueError("accepted result requires ClaimantVaultState")
            if not isinstance(self.effects, ClaimantVaultEffects):
                raise ValueError("accepted result requires ClaimantVaultEffects")
            if self.error is not None:
                raise ValueError("accepted result cannot carry error")
            return
        if self.state is not None or self.effects is not None:
            raise ValueError("rejected result cannot carry state or effects")
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected result requires non-empty error")


def init_claimant_vault_state() -> ClaimantVaultState:
    return ClaimantVaultState()


def _gross_reward(active_shares: int, accumulator: int) -> int:
    product = _checked_mul(
        active_shares,
        accumulator,
        name="gross_reward_product",
    )
    return product // ACC_SCALE


def _settled_account(
    account: VaultAccount,
    *,
    accumulator: int,
    nonce: int | None = None,
) -> VaultAccount:
    gross = _gross_reward(account.active_shares, accumulator)
    if account.reward_debt > gross:
        raise ValueError("account reward debt exceeds gross reward")
    accrued = gross - account.reward_debt
    claimable = _checked_add(
        account.claimable,
        accrued,
        name="account_claimable",
    )
    return replace(
        account,
        reward_debt=gross,
        claimable=claimable,
        last_nonce=account.last_nonce if nonce is None else nonce,
    )


def _replace_account(
    state: ClaimantVaultState,
    account: VaultAccount,
    **state_updates: int | tuple[VaultAccount, ...],
) -> ClaimantVaultState:
    accounts = [
        existing
        for existing in state.accounts
        if existing.claimant != account.claimant
    ]
    accounts.append(account)
    return replace(
        state,
        accounts=tuple(accounts),
        **state_updates,
    )


def _empty_account(claimant: str) -> VaultAccount:
    return VaultAccount(claimant=_require_claimant(claimant))


def _account_for_command(
    state: ClaimantVaultState,
    claimant: str,
    nonce: int,
    *,
    create: bool,
) -> VaultAccount:
    account = state.account(claimant)
    if account is None:
        if not create:
            raise ValueError("unknown vault claimant")
        account = _empty_account(claimant)
    _require_next_nonce(nonce, account.last_nonce, name="nonce")
    return account


def _deposit_rewards(
    state: ClaimantVaultState,
    command: DepositRewards,
) -> ClaimantVaultStepResult:
    funding_nonce = _require_next_nonce(
        command.funding_nonce,
        state.last_funding_nonce,
        name="funding_nonce",
    )
    amount = _require_positive(command.amount, name="amount")
    pre_owned = state.aggregate_owned_rewards
    accumulator_delta = 0
    next_accumulator = state.acc_reward_per_share
    if state.total_active_shares > 0:
        scaled = _checked_mul(amount, ACC_SCALE, name="deposit_scaled")
        accumulator_delta = scaled // state.total_active_shares
        next_accumulator = _checked_add(
            next_accumulator,
            accumulator_delta,
            name="acc_reward_per_share",
        )

    provisional = replace(
        state,
        acc_reward_per_share=next_accumulator,
        reward_balance=_checked_add(
            state.reward_balance,
            amount,
            name="reward_balance",
        ),
        cumulative_deposited=_checked_add(
            state.cumulative_deposited,
            amount,
            name="cumulative_deposited",
        ),
        explicit_residue=0,
        last_funding_nonce=funding_nonce,
    )
    newly_owned = provisional.aggregate_owned_rewards - pre_owned
    if newly_owned < 0 or newly_owned > amount:
        raise ValueError("deposit ownership delta out of range")
    residue_increment = amount - newly_owned
    next_state = replace(
        provisional,
        explicit_residue=_checked_add(
            state.explicit_residue,
            residue_increment,
            name="explicit_residue",
        ),
    )
    return ClaimantVaultStepResult(
        ok=True,
        state=next_state,
        effects=ClaimantVaultEffects(
            accumulator_delta=accumulator_delta,
            explicit_residue_delta=residue_increment,
        ),
    )


def _queue_stake(
    state: ClaimantVaultState,
    command: QueueStake,
) -> ClaimantVaultStepResult:
    account = _account_for_command(
        state,
        command.claimant,
        command.nonce,
        create=True,
    )
    settled = _settled_account(
        account,
        accumulator=state.acc_reward_per_share,
        nonce=command.nonce,
    )
    next_account = replace(
        settled,
        pending_shares=_checked_add(
            settled.pending_shares,
            command.shares,
            name="pending_shares",
        ),
    )
    next_state = _replace_account(state, next_account)
    return ClaimantVaultStepResult(
        ok=True,
        state=next_state,
        effects=ClaimantVaultEffects(
            share_transfers=(
                ShareTransfer(
                    claimant=command.claimant,
                    shares=command.shares,
                    direction="INTO_VAULT",
                ),
            )
        ),
    )


def _activate_stake(
    state: ClaimantVaultState,
    command: ActivateStake,
) -> ClaimantVaultStepResult:
    account = _account_for_command(
        state,
        command.claimant,
        command.nonce,
        create=False,
    )
    if command.shares > account.pending_shares:
        raise ValueError("activation exceeds pending shares")
    settled = _settled_account(
        account,
        accumulator=state.acc_reward_per_share,
        nonce=command.nonce,
    )
    next_active = _checked_add(
        settled.active_shares,
        command.shares,
        name="active_shares",
    )
    next_account = replace(
        settled,
        active_shares=next_active,
        pending_shares=settled.pending_shares - command.shares,
        reward_debt=_gross_reward(next_active, state.acc_reward_per_share),
    )
    next_state = _replace_account(state, next_account)
    return ClaimantVaultStepResult(
        ok=True,
        state=next_state,
        effects=ClaimantVaultEffects(),
    )


def _cancel_pending_stake(
    state: ClaimantVaultState,
    command: CancelPendingStake,
) -> ClaimantVaultStepResult:
    account = _account_for_command(
        state,
        command.claimant,
        command.nonce,
        create=False,
    )
    if command.shares > account.pending_shares:
        raise ValueError("cancellation exceeds pending shares")
    settled = _settled_account(
        account,
        accumulator=state.acc_reward_per_share,
        nonce=command.nonce,
    )
    next_account = replace(
        settled,
        pending_shares=settled.pending_shares - command.shares,
    )
    next_state = _replace_account(state, next_account)
    return ClaimantVaultStepResult(
        ok=True,
        state=next_state,
        effects=ClaimantVaultEffects(
            share_transfers=(
                ShareTransfer(
                    claimant=command.claimant,
                    shares=command.shares,
                    direction="OUT_OF_VAULT",
                ),
            )
        ),
    )


def _unstake(
    state: ClaimantVaultState,
    command: Unstake,
) -> ClaimantVaultStepResult:
    account = _account_for_command(
        state,
        command.claimant,
        command.nonce,
        create=False,
    )
    if command.shares > account.active_shares:
        raise ValueError("unstake exceeds active shares")
    settled = _settled_account(
        account,
        accumulator=state.acc_reward_per_share,
        nonce=command.nonce,
    )
    next_active = settled.active_shares - command.shares
    next_account = replace(
        settled,
        active_shares=next_active,
        reward_debt=_gross_reward(next_active, state.acc_reward_per_share),
    )
    next_state = _replace_account(state, next_account)
    return ClaimantVaultStepResult(
        ok=True,
        state=next_state,
        effects=ClaimantVaultEffects(
            share_transfers=(
                ShareTransfer(
                    claimant=command.claimant,
                    shares=command.shares,
                    direction="OUT_OF_VAULT",
                ),
            )
        ),
    )


def _claim_rewards(
    state: ClaimantVaultState,
    command: ClaimRewards,
) -> ClaimantVaultStepResult:
    account = _account_for_command(
        state,
        command.claimant,
        command.nonce,
        create=False,
    )
    settled = _settled_account(
        account,
        accumulator=state.acc_reward_per_share,
        nonce=command.nonce,
    )
    amount = settled.claimable
    if amount == 0:
        raise ValueError("nothing claimable")
    if amount > state.reward_balance:
        raise ValueError("claim exceeds reward custody")
    next_account = replace(settled, claimable=0)
    next_state = _replace_account(
        state,
        next_account,
        reward_balance=state.reward_balance - amount,
        cumulative_claimed=_checked_add(
            state.cumulative_claimed,
            amount,
            name="cumulative_claimed",
        ),
    )
    return ClaimantVaultStepResult(
        ok=True,
        state=next_state,
        effects=ClaimantVaultEffects(
            reward_transfers=(
                RewardTransfer(
                    recipient=command.claimant,
                    amount=amount,
                    reason="CLAIM",
                ),
            )
        ),
    )


def _drain_residue(
    state: ClaimantVaultState,
    command: DrainResidue,
) -> ClaimantVaultStepResult:
    funding_nonce = _require_next_nonce(
        command.funding_nonce,
        state.last_funding_nonce,
        name="funding_nonce",
    )
    if state.total_active_shares != 0 or state.total_pending_shares != 0:
        raise ValueError("terminal residue drain requires zero active and pending shares")
    if state.aggregate_owned_rewards != 0:
        raise ValueError("terminal residue drain requires zero claimant ownership")
    amount = state.explicit_residue
    if amount == 0:
        raise ValueError("no explicit residue to drain")
    next_state = replace(
        state,
        reward_balance=state.reward_balance - amount,
        explicit_residue=0,
        cumulative_drained=_checked_add(
            state.cumulative_drained,
            amount,
            name="cumulative_drained",
        ),
        last_funding_nonce=funding_nonce,
    )
    return ClaimantVaultStepResult(
        ok=True,
        state=next_state,
        effects=ClaimantVaultEffects(
            reward_transfers=(
                RewardTransfer(
                    recipient=command.recipient,
                    amount=amount,
                    reason="RESIDUE_DRAIN",
                ),
            ),
            explicit_residue_delta=-amount,
        ),
    )


def step_claimant_vault(
    state: ClaimantVaultState,
    command: VaultCommand,
) -> ClaimantVaultStepResult:
    """Apply one pure claimant-vault transition.

    All validation exceptions are converted into typed no-state/no-effect
    rejections. Implementation defects outside the declared validation surface
    remain visible rather than being silently converted into protocol semantics.
    """

    if not isinstance(state, ClaimantVaultState):
        raise TypeError("state must be ClaimantVaultState")
    try:
        if isinstance(command, DepositRewards):
            return _deposit_rewards(state, command)
        if isinstance(command, QueueStake):
            return _queue_stake(state, command)
        if isinstance(command, ActivateStake):
            return _activate_stake(state, command)
        if isinstance(command, CancelPendingStake):
            return _cancel_pending_stake(state, command)
        if isinstance(command, Unstake):
            return _unstake(state, command)
        if isinstance(command, ClaimRewards):
            return _claim_rewards(state, command)
        if isinstance(command, DrainResidue):
            return _drain_residue(state, command)
        raise TypeError("unsupported claimant-vault command type")
    except (TypeError, ValueError, OverflowError, ArithmeticError) as exc:
        return ClaimantVaultStepResult(ok=False, error=str(exc))
