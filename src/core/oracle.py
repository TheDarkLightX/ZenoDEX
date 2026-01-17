"""
Oracle freshness kernel.

This module is intentionally small and pure:
- The functional core computes freshness decisions deterministically.
- The imperative shell is responsible for fetching oracle data and timestamps.
"""

from __future__ import annotations

from dataclasses import dataclass, replace


@dataclass(frozen=True)
class OracleState:
    """Minimal oracle freshness state."""

    price_timestamp: int
    max_staleness_seconds: int

    def __post_init__(self) -> None:
        if self.price_timestamp < 0:
            raise ValueError(f"price_timestamp must be non-negative: {self.price_timestamp}")
        if self.max_staleness_seconds <= 0:
            raise ValueError(
                f"max_staleness_seconds must be positive: {self.max_staleness_seconds}"
            )


def init_oracle_state(max_staleness_seconds: int = 300) -> OracleState:
    """Initialize oracle state with an empty (0) price timestamp."""
    return OracleState(price_timestamp=0, max_staleness_seconds=max_staleness_seconds)


def is_fresh(state: OracleState, current_timestamp: int) -> bool:
    """Return True if the oracle price timestamp is within the max staleness window."""
    if current_timestamp < 0:
        raise ValueError(f"current_timestamp must be non-negative: {current_timestamp}")
    if state.price_timestamp > current_timestamp:
        return False
    return (current_timestamp - state.price_timestamp) <= state.max_staleness_seconds


def update_price_timestamp(state: OracleState, current_timestamp: int) -> OracleState:
    """Update oracle state to record a new price timestamp."""
    if current_timestamp < 0:
        raise ValueError(f"current_timestamp must be non-negative: {current_timestamp}")
    return replace(state, price_timestamp=current_timestamp)

