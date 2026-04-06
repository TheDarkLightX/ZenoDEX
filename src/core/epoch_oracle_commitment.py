"""Epoch-Atomic Oracle Commitment (EAOC) primitives.

Use this when multiple protocol modules must read a shared immutable
oracle value per epoch to avoid cross-module price skew.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class EpochOracleCommitment:
    """Immutable oracle commitment for a single epoch."""

    epoch: int
    price_e8: int
    timestamp: int
    source_hash: str

    def __post_init__(self) -> None:
        if self.epoch < 0:
            raise ValueError(f"epoch must be non-negative: {self.epoch}")
        if self.price_e8 <= 0:
            raise ValueError(f"price_e8 must be positive: {self.price_e8}")
        if self.timestamp < 0:
            raise ValueError(f"timestamp must be non-negative: {self.timestamp}")
        if not self.source_hash:
            raise ValueError("source_hash must be non-empty")


class OracleRegistry:
    """Monotonic registry of epoch commitments."""

    def __init__(self) -> None:
        self._commitments: dict[int, EpochOracleCommitment] = {}
        self._latest_epoch = -1

    def commit(self, commitment: EpochOracleCommitment) -> None:
        """Commit a new epoch price.

        Enforces:
        - one commitment per epoch
        - strictly increasing epoch sequence
        """
        if commitment.epoch in self._commitments:
            raise ValueError(
                f"Epoch {commitment.epoch} already has a commitment"
            )
        if commitment.epoch <= self._latest_epoch:
            raise ValueError(
                f"Epoch {commitment.epoch} is not strictly after latest epoch {self._latest_epoch}"
            )
        self._commitments[commitment.epoch] = commitment
        self._latest_epoch = commitment.epoch

    def get(self, epoch: int) -> EpochOracleCommitment | None:
        """Get commitment for an epoch, if present."""
        return self._commitments.get(epoch)

    def get_price_e8(self, epoch: int) -> int:
        """Get committed price for an epoch or raise KeyError."""
        c = self._commitments.get(epoch)
        if c is None:
            raise KeyError(f"No oracle commitment for epoch {epoch}")
        return c.price_e8

    @property
    def latest_epoch(self) -> int:
        return self._latest_epoch

    @property
    def commitment_count(self) -> int:
        return len(self._commitments)


@dataclass(frozen=True)
class ModuleOracleView:
    """Read-only module view pinned to a committed epoch."""

    module_name: str
    epoch: int
    price_e8: int
    source_hash: str


def create_module_views(
    registry: OracleRegistry,
    epoch: int,
    module_names: list[str],
) -> dict[str, ModuleOracleView]:
    """Create per-module read-only views for a single epoch."""
    commitment = registry.get(epoch)
    if commitment is None:
        raise KeyError(f"No oracle commitment for epoch {epoch}")
    return {
        module: ModuleOracleView(
            module_name=module,
            epoch=epoch,
            price_e8=commitment.price_e8,
            source_hash=commitment.source_hash,
        )
        for module in module_names
    }


def estimate_cross_module_arbitrage_bps(
    price_a_e8: int,
    price_b_e8: int,
    trade_size_quote: int,
) -> int:
    """Rough arbitrage edge from price skew in bps.

    Returns zero when prices match or trade size is non-positive.
    """
    if price_a_e8 <= 0 or price_b_e8 <= 0:
        raise ValueError(f"Prices must be positive: ({price_a_e8}, {price_b_e8})")
    if trade_size_quote <= 0:
        return 0

    low = min(price_a_e8, price_b_e8)
    high = max(price_a_e8, price_b_e8)
    if low == high:
        return 0
    return (high - low) * 10_000 // low

