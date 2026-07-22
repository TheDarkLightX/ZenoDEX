"""Pure zUSD vault ownership lifecycle.

The monetary shell authenticates a transaction sender, but ownership itself is a
consensus state-machine fact.  This module defines the complete lifecycle:

- an empty, unowned vault may be acquired only by an authenticated collateral
  deposit;
- owner-controlled mutations require the same authenticated owner;
- permissionless redemption and liquidation may change the vault but may not
  transfer ownership;
- ownership is released exactly when both vault debt and vault collateral reach
  the explicit empty terminal state.

No balance, network, clock, signature, or persistence effects occur here.
"""

from __future__ import annotations

from dataclasses import dataclass

OWNER_CONTROLLED_VAULT_ACTIONS = frozenset(
    {
        "deposit_collateral",
        "withdraw_collateral",
        "mint_zusd",
        "repay_zusd",
    }
)
VAULT_MUTATING_ACTIONS = frozenset(
    {
        *OWNER_CONTROLLED_VAULT_ACTIONS,
        "redeem_zusd",
        "liquidate",
    }
)


def _require_nonnegative_exact_int(value: int, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise TypeError(f"{name} must be a non-negative exact int")
    return value


def _require_owner(value: str | None, *, name: str) -> str | None:
    if value is None:
        return None
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be a non-empty exact str or None")
    return value


def vault_is_empty(*, collateral_e8: int, debt_e8: int) -> bool:
    collateral = _require_nonnegative_exact_int(collateral_e8, name="collateral_e8")
    debt = _require_nonnegative_exact_int(debt_e8, name="debt_e8")
    return collateral == 0 and debt == 0


def vault_owner_invariant_error(
    *,
    owner_pubkey: str | None,
    collateral_e8: int,
    debt_e8: int,
) -> str | None:
    """Return the unique ownership-shape violation, if one exists."""

    owner = _require_owner(owner_pubkey, name="owner_pubkey")
    empty = vault_is_empty(collateral_e8=collateral_e8, debt_e8=debt_e8)
    if empty and owner is not None:
        return "empty vault must release vault_owner_pubkey"
    if not empty and owner is None:
        return "non-empty vault requires vault_owner_pubkey"
    return None


def authorize_vault_owner_action(
    *,
    current_owner_pubkey: str | None,
    actor_pubkey: str,
    action: str,
    collateral_e8: int,
    debt_e8: int,
) -> str | None:
    """Authorize one action and return the owner after possible acquisition.

    Permissionless actions preserve the existing owner.  Owner-controlled actions
    either authenticate the current owner or acquire a truly empty vault through
    ``deposit_collateral``.  The caller must subsequently pass the core post-state
    to :func:`finalize_vault_owner_transition`.
    """

    owner = _require_owner(current_owner_pubkey, name="current_owner_pubkey")
    actor = _require_owner(actor_pubkey, name="actor_pubkey")
    if actor is None:  # pragma: no cover - excluded by _require_owner contract
        raise AssertionError("actor validation returned None")
    if type(action) is not str or not action:
        raise TypeError("action must be a non-empty exact str")

    invariant_error = vault_owner_invariant_error(
        owner_pubkey=owner,
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
    )
    if invariant_error is not None:
        raise ValueError(invariant_error)

    if action not in OWNER_CONTROLLED_VAULT_ACTIONS:
        return owner
    if owner is None:
        if action != "deposit_collateral":
            raise ValueError("vault owner not initialized")
        return actor
    if owner != actor:
        raise ValueError("vault owner mismatch")
    return owner


@dataclass(frozen=True, slots=True)
class VaultOwnerTransition:
    previous_owner_pubkey: str | None
    next_owner_pubkey: str | None
    acquired_owner_pubkey: str | None = None
    released_owner_pubkey: str | None = None

    def __post_init__(self) -> None:
        previous = _require_owner(
            self.previous_owner_pubkey,
            name="previous_owner_pubkey",
        )
        next_owner = _require_owner(
            self.next_owner_pubkey,
            name="next_owner_pubkey",
        )
        acquired = _require_owner(
            self.acquired_owner_pubkey,
            name="acquired_owner_pubkey",
        )
        released = _require_owner(
            self.released_owner_pubkey,
            name="released_owner_pubkey",
        )
        if acquired is not None and (previous is not None or acquired != next_owner):
            raise ValueError("invalid vault-owner acquisition transition")
        if released is not None and (previous != released or next_owner is not None):
            raise ValueError("invalid vault-owner release transition")
        if acquired is not None and released is not None:
            raise ValueError("one transition cannot both acquire and release ownership")

    def effect_fields(self) -> dict[str, str]:
        fields: dict[str, str] = {}
        if self.acquired_owner_pubkey is not None:
            fields["vault_owner_acquired_pubkey"] = self.acquired_owner_pubkey
        if self.released_owner_pubkey is not None:
            fields["vault_owner_released_pubkey"] = self.released_owner_pubkey
        return fields


def finalize_vault_owner_transition(
    *,
    previous_owner_pubkey: str | None,
    authorized_owner_pubkey: str | None,
    action: str,
    post_collateral_e8: int,
    post_debt_e8: int,
) -> VaultOwnerTransition:
    """Bind ownership to one accepted core post-state.

    Only vault-mutating actions may acquire or release ownership.  A non-empty
    successor without an owner is impossible; an empty successor always releases
    the owner.  Permissionless actions can therefore close a vault but cannot
    assign it to the caller.
    """

    previous = _require_owner(
        previous_owner_pubkey,
        name="previous_owner_pubkey",
    )
    authorized = _require_owner(
        authorized_owner_pubkey,
        name="authorized_owner_pubkey",
    )
    if type(action) is not str or not action:
        raise TypeError("action must be a non-empty exact str")

    empty = vault_is_empty(
        collateral_e8=post_collateral_e8,
        debt_e8=post_debt_e8,
    )
    if action not in VAULT_MUTATING_ACTIONS:
        if authorized != previous:
            raise ValueError("non-vault action cannot change vault ownership")
        next_owner = previous
    else:
        next_owner = None if empty else authorized

    invariant_error = vault_owner_invariant_error(
        owner_pubkey=next_owner,
        collateral_e8=post_collateral_e8,
        debt_e8=post_debt_e8,
    )
    if invariant_error is not None:
        raise ValueError(invariant_error)

    acquired = next_owner if previous is None and next_owner is not None else None
    released = previous if previous is not None and next_owner is None else None
    return VaultOwnerTransition(
        previous_owner_pubkey=previous,
        next_owner_pubkey=next_owner,
        acquired_owner_pubkey=acquired,
        released_owner_pubkey=released,
    )
