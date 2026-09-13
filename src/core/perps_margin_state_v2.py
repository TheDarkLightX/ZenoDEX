"""Owned V2 state and active-claim bindings for the perps margin lane.

The V2 value keeps the existing V1 margin economics and adds the explicit
account-to-terminal-claim relationship needed by a successor projection.  It
is a pure, research-only value: construction grants no authentication, proof,
settlement, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final

from .global_settlement_types_v2 import (
    LaneIdV2,
    _require_root_v2,
    _require_token_v2,
    hash_global_v2,
)
from .perps_margin_types_v1 import (
    MAX_PERPS_MARGIN_ACCOUNTS_V1,
    PerpsMarginAccountV1,
    PerpsMarginStateV1,
)

PERPS_MARGIN_MODULE_SCHEMA_V2: Final = "zenodex/perps-margin-module/v2"
PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V2: Final = (
    "zenodex/perps-margin-terminal-obligation-id/v2"
)
PERPS_MARGIN_TERMINAL_OBLIGATION_ID_DOMAIN_V2: Final = (
    "perps-margin-terminal-obligation-id-v2"
)
MAX_PERPS_MARGIN_ACCOUNTS_V2: Final = MAX_PERPS_MARGIN_ACCOUNTS_V1


@dataclass(frozen=True, slots=True, order=True)
class PerpsMarginClaimBindingV2:
    """Bind one positive-collateral account to its active claim ID."""

    account_id: str
    obligation_id: str

    def __post_init__(self) -> None:
        _require_token_v2(self.account_id, name="perps margin claim account id")
        _require_root_v2(self.obligation_id, name="perps margin claim obligation id")

    def to_canonical(self) -> dict[str, object]:
        return {
            "account_id": self.account_id,
            "obligation_id": self.obligation_id,
        }


def _snapshot_economic_state_v2(state: PerpsMarginStateV1) -> PerpsMarginStateV1:
    """Copy a validated V1 state without retaining account aliases."""

    if type(state) is not PerpsMarginStateV1:
        raise TypeError("perps margin economic state must be an exact V1 value")
    accounts = state.accounts
    if type(accounts) is not tuple:
        raise TypeError("perps margin economic accounts must be a tuple")
    if len(accounts) > MAX_PERPS_MARGIN_ACCOUNTS_V2:
        raise ValueError("perps margin economic account count exceeds bound")
    if any(type(account) is not PerpsMarginAccountV1 for account in accounts):
        raise TypeError("perps margin economic accounts must contain exact V1 values")
    owned_accounts = tuple(replace(account) for account in accounts)
    return replace(state, accounts=owned_accounts)


def _snapshot_claim_bindings_v2(
    bindings: tuple[PerpsMarginClaimBindingV2, ...],
) -> tuple[PerpsMarginClaimBindingV2, ...]:
    if type(bindings) is not tuple:
        raise TypeError("perps margin active claims must be a tuple")
    if len(bindings) > MAX_PERPS_MARGIN_ACCOUNTS_V2:
        raise ValueError("perps margin active claim count exceeds bound")
    if any(type(binding) is not PerpsMarginClaimBindingV2 for binding in bindings):
        raise TypeError("perps margin active claims must contain exact typed values")
    owned_bindings = tuple(replace(binding) for binding in bindings)
    account_ids = tuple(binding.account_id for binding in owned_bindings)
    if any(left >= right for left, right in zip(account_ids, account_ids[1:], strict=False)):
        raise ValueError("perps margin active claims must be strictly sorted by account id")
    obligation_ids = tuple(binding.obligation_id for binding in owned_bindings)
    if len(set(obligation_ids)) != len(obligation_ids):
        raise ValueError("perps margin active claims must use unique obligation ids")
    return owned_bindings


@dataclass(frozen=True, slots=True, init=False)
class PerpsMarginStateV2:
    """V1 margin economics with an owned active terminal-claim index."""

    _economic_state: PerpsMarginStateV1
    _active_claims: tuple[PerpsMarginClaimBindingV2, ...]

    def __init__(
        self,
        economic_state: PerpsMarginStateV1,
        active_claims: tuple[PerpsMarginClaimBindingV2, ...],
    ) -> None:
        owned_economic_state = _snapshot_economic_state_v2(economic_state)
        owned_claims = _snapshot_claim_bindings_v2(active_claims)
        positive_accounts = {
            account.account_id
            for account in owned_economic_state.accounts
            if account.collateral_atoms > 0
        }
        claim_accounts = {binding.account_id for binding in owned_claims}
        if claim_accounts != positive_accounts:
            raise ValueError(
                "perps margin active claims must cover exactly positive-collateral accounts"
            )
        object.__setattr__(self, "_economic_state", owned_economic_state)
        object.__setattr__(self, "_active_claims", owned_claims)

    @property
    def economic_state(self) -> PerpsMarginStateV1:
        return _snapshot_economic_state_v2(self._economic_state)

    @property
    def active_claims(self) -> tuple[PerpsMarginClaimBindingV2, ...]:
        return _snapshot_claim_bindings_v2(self._active_claims)

    @property
    def state_root(self) -> str:
        return hash_global_v2("perps-margin-state-v2", self.to_canonical())

    def claim_id(self, account_id: str) -> str | None:
        _require_token_v2(account_id, name="perps margin claim lookup account id")
        return next(
            (
                binding.obligation_id
                for binding in self._active_claims
                if binding.account_id == account_id
            ),
            None,
        )

    def to_canonical(self) -> dict[str, object]:
        canonical = dict(self.economic_state.to_canonical())
        canonical["schema"] = PERPS_MARGIN_MODULE_SCHEMA_V2
        canonical["active_claims"] = self.active_claims
        return canonical


def margin_claim_id_v2(
    state: PerpsMarginStateV1,
    account_id: str,
    occurrence_id: str,
) -> str:
    """Derive the V2 claim ID for one account-opening occurrence."""

    if type(state) is not PerpsMarginStateV1:
        raise TypeError("perps margin claim state must be an exact V1 value")
    _require_token_v2(account_id, name="perps margin claim account id")
    _require_root_v2(occurrence_id, name="perps margin claim opening occurrence id")
    _require_root_v2(state.module_release_id, name="perps margin claim module release id")
    _require_token_v2(state.market_id, name="perps margin claim market id")
    _require_token_v2(state.collateral_asset, name="perps margin claim collateral asset")
    return hash_global_v2(
        PERPS_MARGIN_TERMINAL_OBLIGATION_ID_DOMAIN_V2,
        {
            "schema": PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V2,
            "lane_id": LaneIdV2.PERPS_MARKET,
            "module_release_id": state.module_release_id,
            "market_id": state.market_id,
            "collateral_asset": state.collateral_asset,
            "account_id": account_id,
            "opening_occurrence_id": occurrence_id,
        },
    )


__all__ = [
    "PERPS_MARGIN_MODULE_SCHEMA_V2",
    "PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V2",
    "PERPS_MARGIN_TERMINAL_OBLIGATION_ID_DOMAIN_V2",
    "MAX_PERPS_MARGIN_ACCOUNTS_V2",
    "PerpsMarginClaimBindingV2",
    "PerpsMarginStateV2",
    "margin_claim_id_v2",
]
