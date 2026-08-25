"""Profile-bound identifiers for one perps market and its Oracle price pair."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    _require_token,
    hash_global_v1,
)
from .m6_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)

PERPS_MARKET_POLICY_SCHEMA_V1: Final = "zenodex/perps-market-policy/v1"
PERPS_MARKET_POLICY_KIND_V1: Final = "perps_market_policy_v1"


@dataclass(frozen=True, slots=True)
class PerpsMarketPolicyV1:
    market_id: str
    base_asset: str
    quote_asset: str
    oracle_id: str

    def __post_init__(self) -> None:
        for name, value in (
            ("market id", self.market_id),
            ("base asset", self.base_asset),
            ("quote asset", self.quote_asset),
            ("Oracle id", self.oracle_id),
        ):
            if type(value) is not str:
                raise TypeError(f"perps market policy {name} must be exact text")
            _require_token(value, name=f"perps market policy {name}")
        if self.base_asset == self.quote_asset:
            raise ValueError("perps market policy assets must be distinct")

    @property
    def policy_root(self) -> str:
        return hash_global_v1(
            "perps-market-policy-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PERPS_MARKET_POLICY_SCHEMA_V1,
            "market_id": self.market_id,
            "base_asset": self.base_asset,
            "quote_asset": self.quote_asset,
            "oracle_id": self.oracle_id,
        }


def snapshot_perps_market_policy_v1(
    policy: PerpsMarketPolicyV1,
) -> PerpsMarketPolicyV1:
    if type(policy) is not PerpsMarketPolicyV1:
        raise TypeError("perps market policy type is not closed")
    return replace(policy)


def require_governed_perps_market_policy_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    occurrence: EconomicCommandOccurrenceV1,
    market_policy: PerpsMarketPolicyV1,
) -> PerpsMarketPolicyV1:
    """Return an owned policy after exact profile and command binding checks."""

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("perps market policy profile type is not closed")
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("perps market policy occurrence type is not closed")
    owned_registry = snapshot_economic_policy_registry_v1(policy_registry)
    owned_policy = snapshot_perps_market_policy_v1(market_policy)
    if owned_registry.registry_root != profile.policy_registry_root:
        raise ValueError("perps market policy registry is outside the profile")
    binding = owned_registry.require_binding(
        policy_kind=PERPS_MARKET_POLICY_KIND_V1,
        command_kind=occurrence.command_kind,
    )
    if binding.policy_root != owned_policy.policy_root:
        raise ValueError("perps market policy root mismatch")
    return owned_policy


__all__ = [
    "PERPS_MARKET_POLICY_KIND_V1",
    "PERPS_MARKET_POLICY_SCHEMA_V1",
    "PerpsMarketPolicyV1",
    "require_governed_perps_market_policy_v1",
    "snapshot_perps_market_policy_v1",
]
