"""Non-overlapping token-accounting projection for persistent perps markets."""

from __future__ import annotations

from .perps import (
    PerpAnyMarketState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpMarketState,
)

E8_SCALE = 100_000_000


class PerpsTokenAccountingError(ValueError):
    """Base class for invalid perps token-accounting projections."""


class PerpsTokenAmountNegative(PerpsTokenAccountingError):
    """Raised when a projected locked-token total is negative."""


class PerpsTokenAmountNonIntegral(PerpsTokenAccountingError):
    """Raised when an E8 aggregate does not represent whole token units."""


def _strict_int(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    return value


def perps_market_locked_quote_e8(market: PerpAnyMarketState) -> int:
    """Return units represented in one exact committed market, scaled by E8.

    Mirrored accounting views and claims are intentionally excluded. Isolated
    `fee_pool_quote` equals fee income already represented in
    `insurance_balance`; adding both would count the same units twice.

    Exact market types are required because committed accounting must not call
    behavior-changing properties or methods inherited from caller subclasses.
    """

    market_type = type(market)
    if market_type is PerpMarketState:
        account_units = sum(
            _strict_int(
                account.collateral_quote,
                name="isolated account collateral_quote",
            )
            for account in market.accounts.values()
        )
        insurance_units = _strict_int(
            market.global_state.get("insurance_balance", 0),
            name="isolated insurance_balance",
        )
        total_units = account_units + insurance_units
        if total_units < 0:
            raise PerpsTokenAmountNegative(
                "isolated perps locked quote units must be non-negative"
            )
        return total_units * E8_SCALE

    if market_type in {
        PerpClearinghouse2pMarketState,
        PerpClearinghouse3pTransferMarketState,
    }:
        total_e8 = _strict_int(
            market.state.get("net_deposited_e8", 0),
            name="fixed perps net_deposited_e8",
        )
        if total_e8 < 0:
            raise PerpsTokenAmountNegative(
                "fixed perps locked quote e8 must be non-negative"
            )
        return total_e8

    raise TypeError(f"unsupported exact perps market type: {market_type!r}")


def perps_market_locked_quote_units(market: PerpAnyMarketState) -> int:
    """Return whole token units, rejecting nonintegral E8 representations."""

    total_e8 = perps_market_locked_quote_e8(market)
    if total_e8 % E8_SCALE != 0:
        raise PerpsTokenAmountNonIntegral(
            "perps locked quote e8 must be whole-token aligned"
        )
    return total_e8 // E8_SCALE
